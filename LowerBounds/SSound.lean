import Mathlib.Data.List.Flatten
import LowerBounds.SWord
import LowerBounds.ChainCapacityC

/-!
# The window search is complete

`wstatement_of_search`: if `search k A q2 C1 C2 bn fuel = false` and `runSearch k = false`, then
every chain of words (`IsWChain`: the model chain of `SModelDef.lean`, on words instead of
vertices) whose list of deficits is a window satisfies the window bound.

The proof takes a violating window with the fewest pieces.

* Every part of a chain is a chain, and so is a chain whose first piece is cut down to its last
  block.  Hence a suffix of the window that begins at the beginning of an interval is a shorter
  window, which satisfies the bound; so the score of the prefix before it is negative (`Viol.neg`).
* One block followed by `k - 2` full pieces would be found by `runSearch` after relabelling; so a
  run of full pieces that follows a piece has at most `k - 3` pieces (`Viol.run`).
* From these two facts the score of a prefix that ends with a partial piece stays below `C2`
  (`score_lt`), so the search does not drop any prefix of the window, and it follows the window
  piece by piece (`go_complete`) after the symbols are relabelled so that the first entry is the
  word `1 2 … k`.
-/

namespace SuperpermLowerBounds
namespace S

open ChainC

/-! ### Sets of codes -/

/-- `x` is one of the numbers of the tree. -/
def Tr.Has : Tr → ℕ → Prop
  | .leaf, _ => False
  | .node l key r, x => x = key ∨ Tr.Has l x ∨ Tr.Has r x

theorem Tr.has_node (l r : Tr) (key x : ℕ) :
    Tr.Has (.node l key r) x ↔ x = key ∨ Tr.Has l x ∨ Tr.Has r x := Iff.rfl

theorem Tr.has_of_mem : ∀ (t : Tr) (x : ℕ), Tr.mem t x = true → Tr.Has t x
  | .leaf, x, h => by
    rw [Tr.mem_leaf] at h
    cases h
  | .node l key r, x, h => by
    rw [Tr.mem_node] at h
    rw [Tr.has_node]
    cases h1 : Nat.ble key x with
    | false =>
      rw [h1] at h
      exact Or.inr (Or.inl (Tr.has_of_mem l x h))
    | true =>
      rw [h1] at h
      cases h2 : Nat.ble x key with
      | false =>
        rw [h2] at h
        exact Or.inr (Or.inr (Tr.has_of_mem r x h))
      | true =>
        exact Or.inl (Nat.le_antisymm (Nat.le_of_ble_eq_true h2) (Nat.le_of_ble_eq_true h1))

theorem Tr.has_ins : ∀ (t : Tr) (y x : ℕ), Tr.Has (Tr.ins t y) x → Tr.Has t x ∨ x = y
  | .leaf, y, x, h => by
    rw [Tr.ins_leaf, Tr.has_node] at h
    rcases h with h | h | h
    · exact Or.inr h
    · cases h
    · cases h
  | .node l key r, y, x, h => by
    rw [Tr.ins_node] at h
    rw [Tr.has_node]
    cases h1 : Nat.ble key y with
    | true =>
      rw [h1] at h
      have h' : Tr.Has (.node l key (Tr.ins r y)) x := h
      rw [Tr.has_node] at h'
      rcases h' with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr (Or.inl h'))
      · rcases Tr.has_ins r y x h' with h'' | h''
        · exact Or.inl (Or.inr (Or.inr h''))
        · exact Or.inr h''
    | false =>
      rw [h1] at h
      have h' : Tr.Has (.node (Tr.ins l y) key r) x := h
      rw [Tr.has_node] at h'
      rcases h' with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · rcases Tr.has_ins l y x h' with h'' | h''
        · exact Or.inl (Or.inr (Or.inl h''))
        · exact Or.inr h''
      · exact Or.inl (Or.inr (Or.inr h'))

/-- Every number of the tree is the class name of one of the words of `used`. -/
def TInv (k : ℕ) (T : Tr) (used : List (List ℕ)) : Prop :=
  ∀ x, Tr.Has T x → ∃ u ∈ used, x = canon k (code u)

theorem tinv_leaf (k : ℕ) (used : List (List ℕ)) : TInv k Tr.leaf used := fun _ h => h.elim

theorem tinv_ins {k : ℕ} {T : Tr} {used : List (List ℕ)} (h : TInv k T used) (v : List ℕ) :
    TInv k (Tr.ins T (canon k (code v))) (used ++ [v]) := by
  intro x hx
  rcases Tr.has_ins T _ x hx with h1 | h1
  · obtain ⟨u, hu, he⟩ := h x h1
    exact ⟨u, List.mem_append_left _ hu, he⟩
  · exact ⟨v, by simp, h1⟩

/-- A word that is not a rotation of any used word is not in the tree. -/
theorem mem_false_of_new {k : ℕ} (hk15 : k ≤ 15) {T : Tr} {used : List (List ℕ)}
    (hT : TInv k T used) (hused : ∀ u ∈ used, PermW k u) {v : List ℕ} (hv : PermW k v)
    (hnew : ∀ u ∈ used, ¬ u ~r v) : Tr.mem T (canon k (code v)) = false := by
  rw [← Bool.not_eq_true]
  intro hm
  obtain ⟨u, hu, he⟩ := hT _ (Tr.has_of_mem _ _ hm)
  exact hnew u hu (isRotated_of_canon_eq (hused u hu).2.1 hv.2.1 ((hused u hu).lt16 hk15)
    (hv.lt16 hk15) he.symm)

/-! ### The pieces at one start -/

/-- How the flag of a state changes with a piece of deficit `d`. -/
def flagStep (f d : ℕ) : ℕ := if d = 0 then 0 else if 2 ≤ d then 2 else if f = 0 then 1 else f

theorem bif_ble {α : Type} (a b : ℕ) (x y : α) :
    (bif Nat.ble a b then x else y) = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · rw [if_pos h, Nat.ble_eq_true_of_le h]
    rfl
  · have hb : Nat.ble a b = false := by
      rw [← Bool.not_eq_true]
      exact fun e => h (Nat.le_of_ble_eq_true e)
    rw [if_neg h, hb]
    rfl

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  rw [← Bool.not_eq_true]
  exact fun e => h (Nat.eq_of_beq_eq_true e)

theorem ble_false_of_lt {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  rw [← Bool.not_eq_true]
  intro e
  have := Nat.le_of_ble_eq_true e
  omega

theorem kid_acc {A q2 C2 P N f d x : ℕ} {T : Tr} {acc : List St} {c : St} (h : c ∈ acc) :
    c ∈ kid A q2 C2 P N f d x T acc := by
  rw [kid_eq]
  cases Nat.beq d 0 <;> cases Nat.beq f 1 <;> cases Nat.ble (N + q2 + C2) (P + A * d) <;>
    cases Nat.beq f 0 <;> cases Nat.ble N P <;> simp [h]

/-- A full piece is listed unless the interval before it has no piece of deficit at least 2. -/
theorem kid_full {A q2 C2 P N f x : ℕ} {T : Tr} (acc : List St) (hf : f ≠ 1) :
    (⟨x, T, P, N + q2, 0⟩ : St) ∈ kid A q2 C2 P N f 0 x T acc := by
  rw [kid_eq]
  simp only [show Nat.beq 0 0 = true from rfl, beq_false_of_ne hf, cond_true, cond_false]
  exact List.mem_cons_self

/-- A partial piece is listed if the score stays below the limit and, after a full piece, the
score before it is negative. -/
theorem kid_partial {A q2 C2 P N f d x : ℕ} {T : Tr} (acc : List St) (hd : d ≠ 0)
    (h1 : P + A * d < N + q2 + C2) (h2 : f = 0 → P < N) :
    (⟨x, T, P + A * d, N + q2, flagStep f d⟩ : St) ∈ kid A q2 C2 P N f d x T acc := by
  rw [kid_eq]
  simp only [beq_false_of_ne hd, ble_false_of_lt h1, cond_false, bif_ble]
  by_cases hf : f = 0
  · have e3 : Nat.beq f 0 = true := by rw [hf]; rfl
    simp only [e3, cond_true, if_neg (Nat.not_le.mpr (h2 hf))]
    have e : flagStep f d = if 2 ≤ d then 2 else 1 := by
      unfold flagStep
      rw [if_neg hd, if_pos hf]
    rw [e]
    exact List.mem_cons_self
  · simp only [beq_false_of_ne hf, cond_false]
    have e : flagStep f d = if 2 ≤ d then 2 else f := by
      unfold flagStep
      rw [if_neg hd, if_neg hf]
    rw [e]
    exact List.mem_cons_self

theorem walk_acc (k A q2 C2 P N f : ℕ) {c : St} : ∀ (n D : ℕ) (T : Tr) (acc : List St),
    c ∈ acc → c ∈ walk k A q2 C2 P N f n D T acc := by
  intro n
  induction n with
  | zero =>
    intro D T acc h
    rw [walk_zero]
    exact h
  | succ n ih =>
    intro D T acc h
    rw [walk_succ]
    cases Tr.mem T (canon k D)
    · exact ih _ _ _ (kid_acc h)
    · exact h

/-- The relation between consecutive block entries of a piece: the door of the exit. -/
def DoorEq (k : ℕ) (a b : List ℕ) : Prop := b = doorW (a.rotate (k - 1))

theorem code_door {k : ℕ} (hk : 2 ≤ k) (hk15 : k ≤ 15) {a b : List ℕ} (ha : PermW k a)
    (h : DoorEq k a b) : doorc k (exc k (code a)) = code b := by
  rw [exc_code k a ha.2.1 (ha.lt16 hk15) (by omega),
    doorc_code k _ (ha.rotate _).2.1 ((ha.rotate _).lt16 hk15) hk, h]

/-- The walk that starts at the first block of a piece `v :: R` whose classes are new lists the
state after that piece, if `kid` does. -/
theorem walk_complete (k A q2 C2 P N f : ℕ) (hk : 2 ≤ k) (hk15 : k ≤ 15) :
    ∀ (R : List (List ℕ)) (n : ℕ) (v : List ℕ) (T : Tr) (used : List (List ℕ)),
      R.length ≤ n → (∀ w ∈ v :: R, PermW k w) → List.IsChain (DoorEq k) (v :: R) →
      TInv k T used → (∀ u ∈ used, PermW k u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      ∃ T', TInv k T' (used ++ v :: R) ∧ ∀ (c : St) (acc : List St),
        (∀ acc', c ∈ kid A q2 C2 P N f (n - R.length)
          (exc k (code ((v :: R).getLast (List.cons_ne_nil v R)))) T' acc') →
        c ∈ walk k A q2 C2 P N f (n + 1) (code v) T acc := by
  intro R
  induction R with
  | nil =>
    intro n v T used _ hperm _ hT hused hnew _
    have hm := mem_false_of_new hk15 hT hused (hperm v List.mem_cons_self)
      (fun u hu => hnew u hu v List.mem_cons_self)
    refine ⟨Tr.ins T (canon k (code v)), tinv_ins hT v, ?_⟩
    intro c acc hc
    rw [walk_succ, hm]
    exact walk_acc k A q2 C2 P N f _ _ _ _ (hc _)
  | cons v' R' ih =>
    intro n v T used hn hperm hdoor hT hused hnew hpw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv : PermW k v := hperm v List.mem_cons_self
    have hm := mem_false_of_new hk15 hT hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    have hused' : ∀ u ∈ used ++ [v], PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hused u h
      · rw [List.mem_singleton.mp h]
        exact hv
    obtain ⟨T', hT', hc'⟩ := ih m v' (Tr.ins T (canon k (code v))) (used ++ [v])
      (by simp only [List.length_cons] at hn; omega)
      (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2 (tinv_ins hT v) hused'
      (by
        intro u hu w hw
        rcases List.mem_append.mp hu with h | h
        · exact hnew u h w (List.mem_cons_of_mem _ hw)
        · rw [List.mem_singleton.mp h]
          exact hpc.1 w hw)
      hpc.2
    refine ⟨T', ?_, ?_⟩
    · have e : used ++ v :: v' :: R' = used ++ [v] ++ v' :: R' := by simp
      rw [e]
      exact hT'
    · intro c acc hc
      rw [walk_succ, hm, code_door hk hk15 hv hdc.1]
      apply hc' c
      intro acc'
      have h := hc acc'
      rw [List.getLast_cons (List.cons_ne_nil v' R')] at h
      have e : m + 1 - (v' :: R').length = m - R'.length := by
        simp only [List.length_cons]
        omega
      rw [e] at h
      exact h

/-! ### The children of a state -/

theorem mem_six {w : ℕ → List St → List St} {c : St} (hmono : ∀ D acc, c ∈ acc → c ∈ w D acc)
    {D base a b cc : ℕ} (hD : ∀ acc, c ∈ w D acc)
    (hcase : D = base + (a * 256 + b * 16 + cc) ∨ D = base + (a * 256 + cc * 16 + b) ∨
      D = base + (b * 256 + a * 16 + cc) ∨ D = base + (b * 256 + cc * 16 + a) ∨
      D = base + (cc * 256 + a * 16 + b) ∨ D = base + (cc * 256 + b * 16 + a)) :
    c ∈ six w base a b cc := by
  unfold six
  rcases hcase with h | h | h | h | h | h <;> subst h
  · exact hD _
  · exact hmono _ _ (hD _)
  · exact hmono _ _ (hmono _ _ (hD _))
  · exact hmono _ _ (hmono _ _ (hmono _ _ (hD _)))
  · exact hmono _ _ (hmono _ _ (hmono _ _ (hmono _ _ (hD _))))
  · exact hmono _ _ (hmono _ _ (hmono _ _ (hmono _ _ (hmono _ _ (hD _)))))

/-- The state after the next piece `v :: R` of a chain is among the children, if `kid` lists
it. -/
theorem children_complete (k A q2 C2 : ℕ) (hk : 3 ≤ k) (hk15 : k ≤ 15) (st : St)
    (last : List ℕ) (used : List (List ℕ)) (v : List ℕ) (R : List (List ℕ))
    (hlast : PermW k last) (hy : st.y = exc k (code last)) (hseam : WLink k 3 last v)
    (hR : R.length ≤ k - 2) (hperm : ∀ w ∈ v :: R, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (v :: R)) (hT : TInv k st.T used)
    (hused : ∀ u ∈ used, PermW k u) (hnew : ∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (v :: R)) :
    ∃ T', TInv k T' (used ++ v :: R) ∧ ∀ c : St,
      (∀ acc', c ∈ kid A q2 C2 st.P st.N st.f (k - 2 - R.length)
        (exc k (code ((v :: R).getLast (List.cons_ne_nil v R)))) T' acc') →
      c ∈ children k A q2 C2 st := by
  have hx : PermW k (last.rotate (k - 1)) := hlast.rotate _
  have hv : PermW k v := hperm v List.mem_cons_self
  obtain ⟨a, b, c0, Y, t0, t1, t2, hxe, hYl, hve, ht0, ht1, ht2, h01, h02, h12⟩ :=
    seam_cases hk hx hv hseam
  have hy' : st.y = code (a :: b :: c0 :: Y) := by
    rw [hy, exc_code k last hlast.2.1 (hlast.lt16 hk15) (by omega), hxe]
  have hd : ∀ z ∈ a :: b :: c0 :: Y, z < 16 := by
    rw [← hxe]
    exact hx.lt16 hk15
  obtain ⟨hp0, hp1, hp2, hp3⟩ := six_parts k a b c0 Y hYl hd hk
  have hcv : code v = code Y * 4096 + (t0 * 256 + t1 * 16 + t2) := by
    rw [hve, code_append3]
  obtain ⟨T', hT', hc'⟩ := walk_complete k A q2 C2 st.P st.N st.f (by omega) hk15 R (k - 2) v st.T
    used hR hperm hdoor hT hused hnew hpw
  refine ⟨T', hT', ?_⟩
  intro c hc
  show c ∈ six (fun D acc => walk k A q2 C2 st.P st.N st.f (k - 1) D st.T acc)
    (st.y % pw (k - 3) * 4096) (st.y / pw (k - 1)) (st.y / pw (k - 2) % 16)
    (st.y / pw (k - 3) % 16)
  rw [hy', hp0, hp1, hp2, hp3]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  refine mem_six (D := code v) (fun D acc h => walk_acc k A q2 C2 st.P st.N st.f _ _ _ _ h) ?_ ?_
  · intro acc
    rw [hk1]
    exact hc' c acc hc
  · rw [hcv]
    rcases ht0 with rfl | rfl | rfl <;> rcases ht1 with rfl | rfl | rfl <;>
      rcases ht2 with rfl | rfl | rfl <;>
      first
        | exact absurd rfl h01
        | exact absurd rfl h02
        | exact absurd rfl h12
        | simp

/-! ### The flag of a list of deficits -/

/-- The flag of a prefix with deficits `ds`. -/
def flagOf (ds : List ℕ) : ℕ := ds.foldl flagStep 1

theorem flagOf_nil : flagOf [] = 1 := rfl

theorem flagOf_concat (ds : List ℕ) (d : ℕ) : flagOf (ds ++ [d]) = flagStep (flagOf ds) d := by
  simp [flagOf, List.foldl_append]

theorem flagStep_zero (f : ℕ) : flagStep f 0 = 0 := by simp [flagStep]

theorem flag_zero {ds : List ℕ} (h : flagOf ds = 0) : ∃ p, ds = p ++ [0] := by
  rcases nil_or_concat ds with rfl | ⟨t, y, rfl⟩
  · rw [flagOf_nil] at h
    omega
  · rw [flagOf_concat] at h
    unfold flagStep at h
    by_cases hy : y = 0
    · subst hy
      exact ⟨t, rfl⟩
    · rw [if_neg hy] at h
      split_ifs at h
      all_goals omega

theorem flag_one {ds : List ℕ} (h : flagOf ds = 1) :
    ds = [] ∨ ∃ pre blk, ds = pre ++ blk ∧ blk ≠ [] ∧ (∀ x ∈ blk, x = 1) ∧
      (pre = [] ∨ ∃ p, pre = p ++ [0]) := by
  induction ds using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton t y ih =>
    right
    rw [flagOf_concat] at h
    unfold flagStep at h
    have hy : y = 1 := by
      by_cases h0 : y = 0
      · rw [if_pos h0] at h
        omega
      · rw [if_neg h0] at h
        by_cases h2 : 2 ≤ y
        · rw [if_pos h2] at h
          omega
        · omega
    subst hy
    rw [if_neg (by omega), if_neg (by omega)] at h
    by_cases hf : flagOf t = 0
    · obtain ⟨p, hp⟩ := flag_zero hf
      exact ⟨t, [1], rfl, by simp, by simp, Or.inr ⟨p, hp⟩⟩
    · rw [if_neg hf] at h
      rcases ih h with rfl | ⟨pre, blk, rfl, hb, hall, hpre⟩
      · exact ⟨[], [1], rfl, by simp, by simp, Or.inl rfl⟩
      · refine ⟨pre, blk ++ [1], by simp, by simp, ?_, hpre⟩
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · exact hall x h1
        · simpa using h1

theorem flagOf_le (ds : List ℕ) : flagOf ds ≤ 2 := by
  induction ds using List.reverseRecOn with
  | nil =>
    rw [flagOf_nil]
    omega
  | append_singleton t y ih =>
    rw [flagOf_concat]
    unfold flagStep
    split_ifs <;> omega

/-- At the end of a window the flag is 2. -/
theorem flag_window {ds : List ℕ} (h : IsWindow ds) : flagOf ds = 2 := by
  have hle := flagOf_le ds
  have h0 : flagOf ds ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := flag_zero h0
    obtain ⟨init, y, hy, hpos⟩ := h.last_partial
    rw [hp] at hy
    have := last_eq_of_concat_eq hy
    omega
  have h1 : flagOf ds ≠ 1 := by
    intro h1
    rcases flag_one h1 with rfl | ⟨pre, blk, rfl, hb, hall, hpre⟩
    · obtain ⟨x, rest, hx, _⟩ := h.first_partial
      cases hx
    · obtain ⟨x, hx, h2⟩ := h.excess pre blk [] (by simp) hb
        (fun x hx => by rw [hall x hx]; omega) hpre (Or.inl rfl)
      rw [hall x hx] at h2
      omega
  omega

/-- Before a full piece of a window the flag is not 1. -/
theorem flag_before_full {pre rest : List ℕ} (h : IsWindow (pre ++ 0 :: rest)) :
    flagOf pre ≠ 1 := by
  intro h1
  rcases flag_one h1 with rfl | ⟨p0, blk, rfl, hb, hall, hpre⟩
  · obtain ⟨x, r, hx, hpos⟩ := h.first_partial
    simp only [List.nil_append, List.cons.injEq] at hx
    omega
  · obtain ⟨x, hx, h2⟩ := h.excess p0 blk (0 :: rest) rfl hb
      (fun x hx => by rw [hall x hx]; omega) hpre (Or.inr ⟨rest, rfl⟩)
    rw [hall x hx] at h2
    omega

/-! ### A violating window with the fewest pieces -/

/-- What is known about the list of deficits of a violating window with the fewest pieces: it is
a window, it violates the bound, the score before every interval after the first is negative, and
a run of full pieces after a piece has at most `k - 3` pieces. -/
structure Viol (k A q2 C1 bn : ℕ) (ds : List ℕ) : Prop where
  win : IsWindow ds
  viol : A * ds.sum + bn < q2 * ds.length + C1
  neg : ∀ u v, ds = u ++ v → (∃ p, u = p ++ [0]) → (∃ d t, v = d :: t ∧ 0 < d) →
    A * u.sum < q2 * u.length
  run : ∀ u f v, ds = u ++ List.replicate f 0 ++ v → u ≠ [] → f ≤ k - 3

/-- The score of a prefix that ends with a partial piece is below `C2`. -/
theorem score_lt {k A q2 C1 C2 bn : ℕ} (hA : q2 ≤ A) (hC : C1 ≤ C2) (hC2 : C2 = q2 * (k - 3))
    {ds : List ℕ} (h : Viol k A q2 C1 bn ds) :
    ∀ (v u : List ℕ), ds = u ++ v → (∃ p y, u = p ++ [y] ∧ 0 < y) →
      A * u.sum < q2 * u.length + C2 := by
  intro v
  induction v with
  | nil =>
    intro u hds _
    rw [List.append_nil] at hds
    have := h.viol
    rw [hds] at this
    omega
  | cons x v' ih =>
    intro u hds hu
    by_cases hx : 0 < x
    · have h1 := ih (u ++ [x]) (by rw [hds]; simp) ⟨u, x, rfl, hx⟩
      rw [List.sum_append, List.length_append, List.sum_singleton, List.length_singleton,
        Nat.mul_add, Nat.mul_add, Nat.mul_one] at h1
      have h2 : A ≤ A * x := Nat.le_mul_of_pos_right A hx
      omega
    · have hx0 : x = 0 := by omega
      subst hx0
      obtain ⟨Z, M, hZM, hZ, hM⟩ := split_front (fun z => z = 0) (0 :: v')
      have hZ' : ∀ z ∈ Z, z = 0 := hZ
      have hZne : Z ≠ [] := by
        rintro rfl
        rcases hM with rfl | ⟨y, t, rfl, hy⟩
        · simp at hZM
        · have hy' : y ≠ 0 := hy
          simp only [List.nil_append, List.cons.injEq] at hZM
          exact hy' hZM.1.symm
      obtain ⟨_, ⟨Z1, hZ1⟩⟩ := zeros_forms hZne hZ'
      have hrep : Z = List.replicate Z.length 0 := List.eq_replicate_iff.mpr ⟨rfl, hZ'⟩
      rcases hM with rfl | ⟨y, t, rfl, hy⟩
      · exfalso
        obtain ⟨init, y, hy, hpos⟩ := h.win.last_partial
        rw [hds, hZM, List.append_nil, hZ1, ← List.append_assoc] at hy
        have := last_eq_of_concat_eq hy
        omega
      · have hy' : y ≠ 0 := hy
        have hf := h.run u Z.length (y :: t) (by rw [hds, hZM, ← hrep, List.append_assoc])
          (by obtain ⟨p, y0, rfl, _⟩ := hu; simp)
        have hn := h.neg (u ++ Z) (y :: t) (by rw [hds, hZM, List.append_assoc])
          ⟨u ++ Z1, by rw [hZ1, List.append_assoc]⟩ ⟨y, t, rfl, by omega⟩
        rw [List.sum_append, List.length_append, sum_eq_zero_of_zeros Z hZ', Nat.add_zero,
          Nat.mul_add] at hn
        have h3 : q2 * Z.length ≤ q2 * (k - 3) := Nat.mul_le_mul_left _ hf
        omega

/-! ### The search follows a chain -/

/-- The pieces `rest` continue a chain whose last block has entry `last` and whose blocks so far
are `used`. -/
def Cont (k : ℕ) : List ℕ → List (List ℕ) → List (List (List ℕ)) → Prop
  | _, _, [] => True
  | _, _, [] :: _ => False
  | last, used, (v :: R) :: rest =>
    R.length ≤ k - 2 ∧ (∀ w ∈ v :: R, PermW k w) ∧ WLink k 3 last v ∧
      List.IsChain (DoorEq k) (v :: R) ∧ (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      List.Pairwise (fun a b => ¬ a ~r b) (v :: R) ∧
      Cont k ((v :: R).getLast (List.cons_ne_nil v R)) (used ++ v :: R) rest

theorem anyIdx_of_mem {f : St → ℕ → Bool} {c : St} (hf : ∀ i, f c i = true) :
    ∀ (l : List St) (j : ℕ), c ∈ l → anyIdx f l j = true := by
  intro l
  induction l with
  | nil =>
    intro j h
    cases h
  | cons b t ih =>
    intro j h
    rw [anyIdx_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · rw [← h1, hf j]
      rfl
    · rw [ih (j + 1) h1, Bool.or_true]

/-- The search finds a violating window with the fewest pieces of which it has reached a
prefix. -/
theorem go_complete (k A q2 C1 C2 bn : ℕ) (hk : 3 ≤ k) (hk15 : k ≤ 15) (hA : q2 ≤ A)
    (hC : C1 ≤ C2) (hC2 : C2 = q2 * (k - 3)) :
    ∀ (fuel : ℕ) (rest : List (List (List ℕ))) (st : St) (key : List ℕ) (last : List ℕ)
      (used : List (List ℕ)) (pre : List ℕ),
      PermW k last → (∀ u ∈ used, PermW k u) → st.y = exc k (code last) → TInv k st.T used →
      st.P = A * pre.sum → st.N = q2 * pre.length → st.f = flagOf pre →
      Cont k last used rest →
      Viol k A q2 C1 bn (pre ++ rest.map (fun Q => k - 1 - Q.length)) →
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel st key = true := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rfl
  | succ fuel ih =>
    intro rest st key last used pre hlast hused hy hT hP hN hf hcont hviol
    rw [goK_succ]
    cases rest with
    | nil =>
      simp only [List.map_nil, List.append_nil] at hviol
      have h2 := flag_window hviol.win
      have hv := hviol.viol
      have hvi : viol C1 bn st = true := by
        rw [viol_eq, hf, h2, hP, hN, ble_false_of_lt (by omega)]
        rfl
      rw [hvi]
      rfl
    | cons Q rest' =>
      cases hvi : viol C1 bn st with
      | true => rfl
      | false =>
        show anyIdx _ _ 0 = true
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hseam, hdoor, hnew, hpw, hcont'⟩ := hcont
          obtain ⟨T', hT', hc'⟩ := children_complete k A q2 C2 hk hk15 st last used v R hlast hy
            hseam hR hperm hdoor hT hused hnew hpw
          have hlastQ : PermW k ((v :: R).getLast (List.cons_ne_nil v R)) :=
            hperm _ (List.getLast_mem _)
          have hused' : ∀ u ∈ used ++ v :: R, PermW k u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          have hd : k - 1 - (v :: R).length = k - 2 - R.length := by
            simp only [List.length_cons]
            omega
          simp only [List.map_cons, hd] at hviol
          generalize hdd : k - 2 - R.length = d at hviol hc'
          by_cases hd0 : d = 0
          · subst hd0
            have hf1 : st.f ≠ 1 := by
              rw [hf]
              exact flag_before_full hviol.win
            apply anyIdx_of_mem (c := ⟨exc k (code ((v :: R).getLast (List.cons_ne_nil v R))), T',
              st.P, st.N + q2, 0⟩) _ _ _ (hc' _ (fun acc' => kid_full acc' hf1))
            intro i
            apply ih rest' _ (i :: key) _ (used ++ v :: R) (pre ++ [0]) hlastQ hused' rfl hT'
            · show st.P = A * (pre ++ [0]).sum
              rw [List.sum_append, List.sum_singleton, Nat.add_zero]
              exact hP
            · show st.N + q2 = q2 * (pre ++ [0]).length
              rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, hN]
            · show 0 = flagOf (pre ++ [0])
              rw [flagOf_concat, flagStep_zero]
            · exact hcont'
            · rw [List.append_assoc]
              exact hviol
          · have hdpos : 0 < d := by omega
            have hs := score_lt hA hC hC2 hviol (rest'.map (fun Q => k - 1 - Q.length))
              (pre ++ [d]) (by rw [List.append_assoc]; rfl) ⟨pre, d, rfl, hdpos⟩
            rw [List.sum_append, List.length_append, List.sum_singleton, List.length_singleton,
              Nat.mul_add, Nat.mul_add, Nat.mul_one] at hs
            have h1 : st.P + A * d < st.N + q2 + C2 := by
              rw [hP, hN]
              omega
            have h2 : st.f = 0 → st.P < st.N := by
              intro h0
              rw [hf] at h0
              obtain ⟨p, hp⟩ := flag_zero h0
              have := hviol.neg pre (d :: rest'.map (fun Q => k - 1 - Q.length)) rfl ⟨p, hp⟩
                ⟨d, _, rfl, hdpos⟩
              rw [hP, hN]
              exact this
            apply anyIdx_of_mem (c := ⟨exc k (code ((v :: R).getLast (List.cons_ne_nil v R))), T',
              st.P + A * d, st.N + q2, flagStep st.f d⟩) _ _ _
              (hc' _ (fun acc' => kid_partial acc' hd0 h1 h2))
            intro i
            apply ih rest' _ (i :: key) _ (used ++ v :: R) (pre ++ [d]) hlastQ hused' rfl hT'
            · show st.P + A * d = A * (pre ++ [d]).sum
              rw [List.sum_append, List.sum_singleton, Nat.mul_add, hP]
            · show st.N + q2 = q2 * (pre ++ [d]).length
              rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, hN]
            · show flagStep st.f d = flagOf (pre ++ [d])
              rw [flagOf_concat, hf]
            · exact hcont'
            · rw [List.append_assoc]
              exact hviol

/-- A run of full pieces that continues a chain is followed by the search with `A = q2 = 0`. -/
theorem run_complete (k : ℕ) (hk : 3 ≤ k) (hk15 : k ≤ 15) :
    ∀ (m : ℕ) (run : List (List (List ℕ))) (st : St) (key : List ℕ) (last : List ℕ)
      (used : List (List ℕ)),
      run.length = m → (∀ Q ∈ run, Q.length = k - 1) →
      PermW k last → (∀ u ∈ used, PermW k u) → st.y = exc k (code last) → TInv k st.T used →
      st.P = 0 → st.N = 0 → st.f = 0 → Cont k last used run →
      goK k 0 0 0 0 0 (fun _ _ => true) m st key = true := by
  intro m
  induction m with
  | zero =>
    intros
    rfl
  | succ m ih =>
    intro run st key last used hlen hfull hlast hused hy hT hP hN hf hcont
    rw [goK_succ]
    cases hvi : viol 0 0 st with
    | true => rfl
    | false =>
      show anyIdx _ _ 0 = true
      cases run with
      | nil => simp at hlen
      | cons Q run' =>
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hseam, hdoor, hnew, hpw, hcont'⟩ := hcont
          obtain ⟨T', hT', hc'⟩ := children_complete k 0 0 0 hk hk15 st last used v R hlast hy
            hseam hR hperm hdoor hT hused hnew hpw
          have hlastQ : PermW k ((v :: R).getLast (List.cons_ne_nil v R)) :=
            hperm _ (List.getLast_mem _)
          have hused' : ∀ u ∈ used ++ v :: R, PermW k u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          have hQ := hfull (v :: R) List.mem_cons_self
          have hd0 : k - 2 - R.length = 0 := by
            simp only [List.length_cons] at hQ
            omega
          rw [hd0] at hc'
          have hf1 : st.f ≠ 1 := by
            rw [hf]
            omega
          apply anyIdx_of_mem (c := ⟨exc k (code ((v :: R).getLast (List.cons_ne_nil v R))), T',
            st.P, st.N + 0, 0⟩) _ _ _ (hc' _ (fun acc' => kid_full acc' hf1))
          intro i
          exact ih run' _ (i :: key) _ (used ++ v :: R) (by simpa using hlen)
            (fun Q hQ => hfull Q (List.mem_cons_of_mem _ hQ)) hlastQ hused' rfl hT' hP
            (by show st.N + 0 = 0; rw [hN]) rfl hcont'

/-! ### Chains of words -/

/-- The seam between two consecutive pieces. -/
def SeamRel (k : ℕ) (P Q : List (List ℕ)) : Prop :=
  ∀ (hP : P ≠ []) (hQ : Q ≠ []), WLink k 3 (P.getLast hP) (Q.head hQ)

/-- A model chain on words: `IsModelChain` of `SModelDef.lean`, with the words of the vertices. -/
structure IsWChain (k : ℕ) (L : List (List (List ℕ))) : Prop where
  words : ∀ P ∈ L, ∀ w ∈ P, PermW k w
  pieces_ne : ∀ P ∈ L, P ≠ []
  size_le : ∀ P ∈ L, P.length ≤ k - 1
  doors : ∀ P ∈ L, List.IsChain (WLink k 2) P
  seams : List.IsChain (SeamRel k) L
  classes : List.Pairwise (fun u v => ¬ u ~r v) L.flatten

/-- The deficits of the pieces. -/
def wdef (k : ℕ) (L : List (List (List ℕ))) : List ℕ := L.map fun P => k - 1 - P.length

/-- Every contiguous part of a chain is a chain. -/
theorem IsWChain.infix {k : ℕ} {L L' : List (List (List ℕ))} (h : IsWChain k L)
    (hi : L' <:+: L) : IsWChain k L' :=
  ⟨fun P hP => h.words P (hi.subset hP), fun P hP => h.pieces_ne P (hi.subset hP),
    fun P hP => h.size_le P (hi.subset hP), fun P hP => h.doors P (hi.subset hP),
    h.seams.infix hi, h.classes.sublist (List.Sublist.flatten hi.sublist)⟩

/-- A chain whose first piece is cut down to its last block is a chain. -/
theorem IsWChain.trim {k : ℕ} (hk : 2 ≤ k) {P : List (List ℕ)} {rest : List (List (List ℕ))}
    (h : IsWChain k (P :: rest)) (hP : P ≠ []) : IsWChain k ([P.getLast hP] :: rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ w hw
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · rw [List.mem_singleton.mp hw]
      exact h.words P List.mem_cons_self _ (List.getLast_mem hP)
    · exact h.words Q (List.mem_cons_of_mem _ hQ') w hw
  · intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · simp
    · exact h.pieces_ne Q (List.mem_cons_of_mem _ hQ')
  · intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · simp only [List.length_singleton]
      omega
    · exact h.size_le Q (List.mem_cons_of_mem _ hQ')
  · intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · exact List.isChain_singleton _
    · exact h.doors Q (List.mem_cons_of_mem _ hQ')
  · refine List.IsChain.imp_head ?_ h.seams
    intro Z hZ hP' hQ
    exact hZ hP hQ
  · have hs : List.Sublist ([P.getLast hP] :: rest).flatten (P :: rest).flatten := by
      rw [List.flatten_cons, List.flatten_cons]
      exact List.Sublist.append_right (List.singleton_sublist.mpr (List.getLast_mem hP)) _
    exact h.classes.sublist hs

/-- The chain with every word relabelled. -/
def relabChain (e : List ℕ) (L : List (List (List ℕ))) : List (List (List ℕ)) :=
  L.map (List.map (List.map (relab e)))

theorem wdef_relabChain (k : ℕ) (e : List ℕ) (L : List (List (List ℕ))) :
    wdef k (relabChain e L) = wdef k L := by
  simp [wdef, relabChain, List.map_map, Function.comp_def]

theorem mem_flatten_perm {k : ℕ} {L : List (List (List ℕ))} (h : IsWChain k L) {w : List ℕ}
    (hw : w ∈ L.flatten) : PermW k w := by
  obtain ⟨P, hP, hwP⟩ := List.mem_flatten.mp hw
  exact h.words P hP w hwP

/-- A relabelled chain is a chain. -/
theorem IsWChain.relabel {k : ℕ} {e : List ℕ} (he : PermW k e) {L : List (List (List ℕ))}
    (h : IsWChain k L) : IsWChain k (relabChain e L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP w hw
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    exact he.map_relab (h.words P0 hP0 w0 hw0)
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    simpa using h.pieces_ne P0 hP0
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    simpa using h.size_le P0 hP0
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    rw [List.isChain_map]
    exact (h.doors P0 hP0).imp (fun a b hab => hab.map _)
  · unfold relabChain
    rw [List.isChain_map]
    refine h.seams.imp ?_
    intro P Q hPQ hP hQ
    have hP0 : P ≠ [] := by simpa using hP
    have hQ0 : Q ≠ [] := by simpa using hQ
    rw [List.getLast_map, List.head_map]
    exact (hPQ hP0 hQ0).map _
  · unfold relabChain
    rw [← List.map_flatten, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ h.classes
    intro a b ha hb hab
    exact not_isRotated_map_relab he (mem_flatten_perm h ha) (mem_flatten_perm h hb) hab

/-- Inside a piece of a chain the entries are joined by doors. -/
theorem door_chain {k : ℕ} (hk : 3 ≤ k) : ∀ (Q : List (List ℕ)), (∀ w ∈ Q, PermW k w) →
    List.IsChain (WLink k 2) Q → List.Pairwise (fun a b => ¬ a ~r b) Q →
    List.IsChain (DoorEq k) Q
  | [], _, _, _ => List.IsChain.nil
  | [_], _, _, _ => List.isChain_singleton _
  | a :: b :: t, hperm, hc, hp => by
    have hc' := List.isChain_cons_cons.mp hc
    have hp' := List.pairwise_cons.mp hp
    refine List.isChain_cons_cons.mpr ⟨?_, door_chain hk (b :: t)
      (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hc'.2 hp'.2⟩
    exact door_of_link hk (hperm a List.mem_cons_self) (hperm b (by simp)) hc'.1
      (hp'.1 b List.mem_cons_self)

/-- The pieces after the first piece of a chain continue it. -/
theorem cont_of_chain {k : ℕ} (hk : 3 ≤ k) : ∀ (rest : List (List (List ℕ))) (P : List (List ℕ))
    (used : List (List ℕ)) (hP : P ≠ []), IsWChain k (P :: rest) →
    (∀ u ∈ used, ∀ w ∈ rest.flatten, ¬ u ~r w) → Cont k (P.getLast hP) used rest
  | [], _, _, _, _, _ => trivial
  | Q :: rest', P, used, hP, h, hnew => by
    have hQne : Q ≠ [] := h.pieces_ne Q (by simp)
    obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQne
    have hperm : ∀ w ∈ v :: R, PermW k w := h.words _ (by simp)
    have hsz := h.size_le (v :: R) (by simp)
    have hseam : WLink k 3 (P.getLast hP) v :=
      (List.isChain_cons_cons.mp h.seams).1 hP (List.cons_ne_nil v R)
    have hcl : List.Pairwise (fun a b => ¬ a ~r b) (P ++ ((v :: R) ++ rest'.flatten)) := by
      have := h.classes
      rw [List.flatten_cons, List.flatten_cons] at this
      exact this
    have hcl3 := List.pairwise_append.mp (List.pairwise_append.mp hcl).2.1
    have htail : IsWChain k ((v :: R) :: rest') := h.infix ⟨[P], [], by simp⟩
    refine ⟨by simp only [List.length_cons] at hsz; omega, hperm, hseam,
      door_chain hk _ hperm (h.doors _ (by simp)) hcl3.1, ?_, hcl3.1, ?_⟩
    · intro u hu w hw
      exact hnew u hu w (by rw [List.flatten_cons]; exact List.mem_append_left _ hw)
    · apply cont_of_chain hk rest' (v :: R) (used ++ v :: R) (List.cons_ne_nil v R) htail
      intro u hu w hw
      rcases List.mem_append.mp hu with hu' | hu'
      · exact hnew u hu' w (by rw [List.flatten_cons]; exact List.mem_append_right _ hw)
      · exact hcl3.2.2 u hu' w hw

/-! ### Arithmetic of the bound -/

theorem viol_of_not_bound {k cn bn q : ℕ} (hcn : cn ≤ q * (k - 3)) {ds : List ℕ}
    (h : ¬ WindowBound k cn bn q ds) :
    (q * (k - 3) - cn) * ds.sum + bn < 2 * q * ds.length + 2 * q * (k - 4) := by
  unfold WindowBound at h
  have e1 : (q * (k - 3) - cn) * ds.sum = q * (k - 3) * ds.sum - cn * ds.sum := Nat.sub_mul _ _ _
  have e2 : cn * ds.sum ≤ q * (k - 3) * ds.sum := Nat.mul_le_mul_right _ hcn
  have e3 : q * ((k - 3) * ds.sum) = q * (k - 3) * ds.sum := by ring
  have e4 : q * (2 * ds.length + 2 * (k - 4)) = 2 * q * ds.length + 2 * q * (k - 4) := by ring
  rw [e3, e4] at h
  omega

theorem neg_of_bounds {k cn bn q : ℕ} (hcn : cn ≤ q * (k - 3)) {u v : List ℕ}
    (hv : WindowBound k cn bn q v) (h : ¬ WindowBound k cn bn q (u ++ v)) :
    (q * (k - 3) - cn) * u.sum < 2 * q * u.length := by
  unfold WindowBound at hv h
  rw [List.sum_append, List.length_append] at h
  have e1 : (q * (k - 3) - cn) * u.sum = q * (k - 3) * u.sum - cn * u.sum := Nat.sub_mul _ _ _
  have e2 : cn * u.sum ≤ q * (k - 3) * u.sum := Nat.mul_le_mul_right _ hcn
  have e3 : q * ((k - 3) * (u.sum + v.sum)) = q * (k - 3) * u.sum + q * ((k - 3) * v.sum) := by
    ring
  have e4 : q * (2 * (u.length + v.length) + 2 * (k - 4)) =
      2 * q * u.length + q * (2 * v.length + 2 * (k - 4)) := by ring
  have e5 : cn * (u.sum + v.sum) = cn * u.sum + cn * v.sum := by ring
  rw [e3, e4, e5] at h
  omega

/-- A suffix of a window that begins after a zero with a non-zero entry is a window. -/
theorem isWindow_suffix {u v : List ℕ} (h : IsWindow (u ++ v)) (hu : ∃ p, u = p ++ [0])
    (hv : ∃ d t, v = d :: t ∧ 0 < d) : IsWindow v := by
  obtain ⟨p, rfl⟩ := hu
  obtain ⟨d, t, rfl, hd⟩ := hv
  refine ⟨⟨d, t, rfl, hd⟩, ?_, ?_⟩
  · obtain ⟨init, y, hy, hpos⟩ := h.last_partial
    rcases nil_or_concat (d :: t) with hnil | ⟨t', y', ht'⟩
    · cases hnil
    · refine ⟨t', y', ht', ?_⟩
      rw [ht', ← List.append_assoc] at hy
      have := last_eq_of_concat_eq hy
      omega
  · intro pre blk post hW hblk hpos hpre hpost
    refine h.excess (p ++ [0] ++ pre) blk post (by rw [hW]; simp) hblk hpos ?_ hpost
    right
    rcases hpre with rfl | ⟨pre', rfl⟩
    · exact ⟨p, by simp⟩
    · exact ⟨p ++ [0] ++ pre', by simp⟩

/-! ### The statement for chains of words -/

/-- The window bound for every chain of words whose list of deficits is a window. -/
def WStatement (k cn bn q : ℕ) : Prop :=
  ∀ L : List (List (List ℕ)), IsWChain k L → IsWindow (wdef k L) →
    WindowBound k cn bn q (wdef k L)

theorem wstatement_of_search {k cn bn q A q2 C1 C2 fuel : ℕ} (hk : 5 ≤ k) (hk15 : k ≤ 15)
    (hc : cn ≤ q * (k - 5)) (hA : A = q * (k - 3) - cn) (hq2 : q2 = 2 * q)
    (hC1 : C1 = 2 * q * (k - 4)) (hC2 : C2 = 2 * q * (k - 3))
    (hrun : runSearch k = false) (hs : search k A q2 C1 C2 bn fuel = false) :
    WStatement k cn bn q := by
  have hcn : cn ≤ q * (k - 3) := le_trans hc (Nat.mul_le_mul_left _ (by omega))
  have hAq : q2 ≤ A := by
    have e : q * (k - 3) = q * (k - 5) + 2 * q := by
      have : k - 3 = k - 5 + 2 := by omega
      rw [this, Nat.mul_add]
      ring
    rw [hA, hq2, e]
    omega
  have hCC : C1 ≤ C2 := by
    rw [hC1, hC2]
    exact Nat.mul_le_mul_left _ (by omega)
  have hC2' : C2 = q2 * (k - 3) := by rw [hC2, hq2]
  suffices hmain : ∀ n : ℕ, ∀ L : List (List (List ℕ)), L.length = n → IsWChain k L →
      IsWindow (wdef k L) → WindowBound k cn bn q (wdef k L) from
    fun L => hmain L.length L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL hwin
    by_contra hnb
    -- what a violating window with the fewest pieces satisfies
    have hviol : Viol k A q2 C1 bn (wdef k L) := by
      refine ⟨hwin, ?_, ?_, ?_⟩
      · rw [hA, hq2, hC1]
        exact viol_of_not_bound hcn hnb
      · intro u v hds hu hv
        have hds' : List.map (fun P : List (List ℕ) => k - 1 - P.length) L = u ++ v := hds
        obtain ⟨Lu, Lv, rfl, hLu, hLv⟩ := List.map_eq_append_iff.mp hds'
        have hwv : IsWindow (wdef k Lv) := by
          show IsWindow (List.map _ Lv)
          rw [hLv]
          rw [hds] at hwin
          exact isWindow_suffix hwin hu hv
        have hlt : Lv.length < n := by
          obtain ⟨p, hp⟩ := hu
          have h1 : Lu.length = u.length := by rw [← hLu, List.length_map]
          rw [← hlen, List.length_append, h1, hp, List.length_append, List.length_singleton]
          omega
        have hbv := ih Lv.length hlt Lv rfl (hL.infix ⟨Lu, [], by simp⟩) hwv
        have hbv' : WindowBound k cn bn q v := by
          rw [← hLv]
          exact hbv
        rw [hds] at hnb
        rw [hA, hq2]
        exact neg_of_bounds hcn hbv' hnb
      · intro u f v hds hune
        by_contra hf
        have hds' : List.map (fun P : List (List ℕ) => k - 1 - P.length) L =
            u ++ List.replicate f 0 ++ v := hds
        obtain ⟨Luf, Lv, rfl, hLuf, hLv⟩ := List.map_eq_append_iff.mp hds'
        obtain ⟨Lu, Lf, rfl, hLu, hLf⟩ := List.map_eq_append_iff.mp hLuf
        have hLune : Lu ≠ [] := by
          rintro rfl
          exact hune (by simpa using hLu.symm)
        obtain ⟨Lu', Pp, hLu'⟩ := (List.eq_nil_or_concat Lu).resolve_left hLune
        rw [List.concat_eq_append] at hLu'
        subst hLu'
        have hLflen : Lf.length = f := by
          have := congrArg List.length hLf
          simpa using this
        have hfull : ∀ Q ∈ Lf, Q.length = k - 1 := by
          intro Q hQ
          have h0 : k - 1 - Q.length ∈ List.replicate f 0 := by
            rw [← hLf]
            exact List.mem_map.mpr ⟨Q, hQ, rfl⟩
          have h1 := (List.mem_replicate.mp h0).2
          have h2 := hL.size_le Q (by simp [hQ])
          omega
        have hinf : (Pp :: Lf.take (k - 2)) <:+: (Lu' ++ [Pp] ++ Lf ++ Lv) := by
          have e : Lu' ++ [Pp] ++ Lf ++ Lv =
              Lu' ++ (Pp :: Lf.take (k - 2)) ++ (Lf.drop (k - 2) ++ Lv) := by
            conv_lhs => rw [← List.take_append_drop (k - 2) Lf]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          exact ⟨Lu', Lf.drop (k - 2) ++ Lv, e.symm⟩
        have hc0 := hL.infix hinf
        have hPp : Pp ≠ [] := hc0.pieces_ne Pp List.mem_cons_self
        have hc1 := hc0.trim (by omega) hPp
        have hep : PermW k (Pp.getLast hPp) :=
          hc1.words _ List.mem_cons_self _ List.mem_cons_self
        have hc2 := hc1.relabel hep
        have hid : (Pp.getLast hPp).map (relab (Pp.getLast hPp)) = List.range' 1 k := by
          rw [map_relab_self hep.1, hep.2.1]
        have hshape : relabChain (Pp.getLast hPp) ([Pp.getLast hPp] :: Lf.take (k - 2)) =
            [List.range' 1 k] :: relabChain (Pp.getLast hPp) (Lf.take (k - 2)) := by
          simp [relabChain, hid]
        rw [hshape] at hc2
        have hidp : PermW k (List.range' 1 k) := hc2.words _ List.mem_cons_self _ List.mem_cons_self
        have hcl := List.pairwise_cons.mp (show List.Pairwise (fun a b => ¬ a ~r b)
          (List.range' 1 k :: (relabChain (Pp.getLast hPp) (Lf.take (k - 2))).flatten) from by
            have := hc2.classes
            rw [List.flatten_cons] at this
            exact this)
        have hcont := cont_of_chain (by omega) (relabChain (Pp.getLast hPp) (Lf.take (k - 2)))
          [List.range' 1 k] [List.range' 1 k] (List.cons_ne_nil _ _) hc2
          (by
            intro u hu w hw
            rw [List.mem_singleton.mp hu]
            exact hcl.1 w hw)
        have htrue := run_complete k (by omega) hk15 (k - 2)
          (relabChain (Pp.getLast hPp) (Lf.take (k - 2))) (runStart k) [] (List.range' 1 k)
          [List.range' 1 k]
          (by
            simp only [relabChain, List.length_map, List.length_take, hLflen]
            omega)
          (by
            intro Q hQ
            obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.mp hQ
            rw [List.length_map]
            exact hfull Q0 (List.mem_of_mem_take hQ0))
          hidp
          (by
            intro u hu
            rw [List.mem_singleton.mp hu]
            exact hidp)
          (by
            show exc k (idc k) = _
            rw [idc_code])
          (by
            show TInv k (Tr.ins Tr.leaf (canon k (idc k))) [List.range' 1 k]
            rw [idc_code]
            exact tinv_ins (tinv_leaf k []) (List.range' 1 k))
          rfl rfl rfl hcont
        have hrun' : goK k 0 0 0 0 0 (fun _ _ => true) (k - 2) (runStart k) [] = false := hrun
        rw [hrun'] at htrue
        cases htrue
    -- the first piece
    obtain ⟨x, restd, hx, hxpos⟩ := hwin.first_partial
    cases L with
    | nil => cases hx
    | cons Q0 rest =>
      have hQ0 : Q0 ≠ [] := hL.pieces_ne Q0 List.mem_cons_self
      obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
      have hv0 : PermW k v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
      have hL' := hL.relabel hv0
      have hviol' : Viol k A q2 C1 bn (wdef k (relabChain v0 ((v0 :: R0) :: rest))) := by
        rw [wdef_relabChain]
        exact hviol
      have hshape : relabChain v0 ((v0 :: R0) :: rest) =
          (List.range' 1 k :: R0.map (List.map (relab v0))) :: relabChain v0 rest := by
        simp [relabChain, map_relab_self hv0.1, hv0.2.1]
      rw [hshape] at hL' hviol'
      generalize R0.map (List.map (relab v0)) = R1 at hL' hviol'
      generalize relabChain v0 rest = rest1 at hL' hviol'
      have hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w := hL'.words _ List.mem_cons_self
      have hcl : List.Pairwise (fun a b => ¬ a ~r b)
          ((List.range' 1 k :: R1) ++ rest1.flatten) := by
        have := hL'.classes
        rw [List.flatten_cons] at this
        exact this
      have hcl' := List.pairwise_append.mp hcl
      have hsz := hL'.size_le _ List.mem_cons_self
      have hdoor := door_chain (by omega) _ hperm (hL'.doors _ List.mem_cons_self) hcl'.1
      obtain ⟨T', hT', hc'⟩ := walk_complete k A q2 C2 0 0 1 (by omega) hk15 R1 (k - 2)
        (List.range' 1 k) Tr.leaf [] (by simp only [List.length_cons] at hsz; omega) hperm hdoor
        (tinv_leaf k []) (by simp) (by simp) hcl'.1
      have hcont := cont_of_chain (by omega) rest1 (List.range' 1 k :: R1)
        (List.range' 1 k :: R1) (List.cons_ne_nil _ _) hL' hcl'.2.2
      have hd : k - 1 - (List.range' 1 k :: R1).length = k - 2 - R1.length := by
        simp only [List.length_cons]
        omega
      simp only [wdef, List.map_cons, hd] at hviol'
      generalize k - 2 - R1.length = d at hviol' hc'
      have hdpos : 0 < d := by
        obtain ⟨x', r', hx', hpos'⟩ := hviol'.win.first_partial
        cases hx'
        exact hpos'
      have hsc := score_lt hAq hCC hC2' hviol' (rest1.map (fun P => k - 1 - P.length)) [d] rfl
        ⟨[], d, rfl, hdpos⟩
      simp only [List.sum_singleton, List.length_singleton, Nat.mul_one] at hsc
      have htrue : search k A q2 C1 C2 bn fuel = true := by
        have hk1 : Nat.sub k 1 = k - 2 + 1 := by
          show k - 1 = _
          omega
        unfold search rootChildren
        rw [hk1, idc_code]
        apply anyIdx_of_mem (c := ⟨exc k (code ((List.range' 1 k :: R1).getLast
          (List.cons_ne_nil _ _))), T', 0 + A * d, 0 + q2, flagStep 1 d⟩) _ _ _
          (hc' _ [] (fun acc' => kid_partial acc' (by omega) (by omega) (by intro h; omega)))
        intro i
        apply go_complete k A q2 C1 C2 bn (by omega) hk15 hAq hCC hC2' fuel rest1 _ [i] _
          ([] ++ List.range' 1 k :: R1) [d] (hperm _ (List.getLast_mem _))
          (by simpa using hperm) rfl hT'
        · show 0 + A * d = A * [d].sum
          simp
        · show 0 + q2 = q2 * [d].length
          simp
        · rfl
        · simpa using hcont
        · exact hviol'
      rw [hs] at htrue
      cases htrue

end S
end SuperpermLowerBounds

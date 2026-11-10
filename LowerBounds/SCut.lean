import LowerBounds.SSearch

/-!
# Cutting a search into parts

The kernel evaluates the search of `SSearch.lean` in parts.  `ref_of_cover` puts the parts
together: a search `a + b` pieces deep below a state finds nothing if a list `cover` of paths of
length `a` contains every path that the search reaches
(`goK (leafCover cover) a st [] = false`), and the search `b` pieces deep finds nothing below the
end of each of these paths.  `search_false` does the same for the states after the first piece.

This file imports only `SSearch.lean` (no Mathlib), so that the files that assemble the parts load
quickly.  It follows the same construction as an earlier search on eight symbols.
-/

namespace SuperpermLowerBounds
namespace S

theorem beqKey_eq : ∀ (a b : List Nat), beqKey a b = true → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x s ih =>
    intro b h
    cases b with
    | nil => cases h
    | cons y t =>
      have h' : (Nat.beq x y && beqKey s t) = true := h
      rw [Bool.and_eq_true] at h'
      rw [Nat.eq_of_beq_eq_true h'.1, ih t h'.2]

theorem memKey_mem : ∀ (cover : List (List Nat)) (key : List Nat), memKey key cover = true →
    key ∈ cover := by
  intro cover
  induction cover with
  | nil =>
    intro key h
    cases h
  | cons k t ih =>
    intro key h
    have h' : (beqKey key k || memKey key t) = true := h
    rcases Bool.or_eq_true_iff.mp h' with h1 | h1
    · rw [beqKey_eq _ _ h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih key h1)

theorem anyIdx_split {f1 f2 : St → Nat → Bool} (d : St) :
    ∀ (l : List St) (j : Nat), anyIdx f1 l j = true → anyIdx f2 l j = false →
      ∃ i, f1 (nthD l i d) (j + i) = true ∧ f2 (nthD l i d) (j + i) = false := by
  intro l
  induction l with
  | nil =>
    intro j h
    rw [anyIdx_nil] at h
    cases h
  | cons c t ih =>
    intro j h1 h2
    rw [anyIdx_cons] at h1 h2
    rw [Bool.or_eq_false_iff] at h2
    rcases Bool.or_eq_true_iff.mp h1 with h | h
    · exact ⟨0, h, h2.1⟩
    · obtain ⟨i, hi1, hi2⟩ := ih (j + 1) h h2.2
      refine ⟨i + 1, ?_, ?_⟩
      · rw [nthD_cons_succ, show j + (i + 1) = j + 1 + i by omega]
        exact hi1
      · rw [nthD_cons_succ, show j + (i + 1) = j + 1 + i by omega]
        exact hi2

theorem anyIdx_congr {f1 f2 : St → Nat → Bool} (h : ∀ c i, f1 c i = f2 c i) :
    ∀ (l : List St) (j : Nat), anyIdx f1 l j = anyIdx f2 l j := by
  intro l
  induction l with
  | nil =>
    intro j
    rfl
  | cons c t ih =>
    intro j
    rw [anyIdx_cons, anyIdx_cons, h, ih]

theorem anyIdx_false {f : St → Nat → Bool} (d : St) : ∀ (l : List St) (j : Nat),
    (∀ i, i < l.length → f (nthD l i d) (j + i) = false) → anyIdx f l j = false := by
  intro l
  induction l with
  | nil =>
    intro j _
    rfl
  | cons c t ih =>
    intro j h
    rw [anyIdx_cons, Bool.or_eq_false_iff]
    constructor
    · exact h 0 (Nat.zero_lt_succ _)
    · apply ih (j + 1)
      intro i hi
      have := h (i + 1) (Nat.succ_lt_succ hi)
      rw [nthD_cons_succ, show j + (i + 1) = j + 1 + i by omega] at this
      exact this

/-- Fuel adds up. -/
theorem goK_add (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) (b : Nat) :
    ∀ (a : Nat) (st : St) (key : List Nat),
      goK k A q2 C1 C2 bn leaf (a + b) st key =
        goK k A q2 C1 C2 bn (fun st' key' => goK k A q2 C1 C2 bn leaf b st' key') a st key := by
  intro a
  induction a with
  | zero =>
    intro st key
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    intro st key
    rw [Nat.succ_add, goK_succ, goK_succ]
    congr 1
    exact anyIdx_congr (fun c i => ih c (i :: key)) _ _

/-- With the leaf that is always `true` the recorded path does not matter. -/
theorem goK_key (k A q2 C1 C2 bn : Nat) : ∀ (fuel : Nat) (st : St) (key key' : List Nat),
    goK k A q2 C1 C2 bn (fun _ _ => true) fuel st key =
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel st key' := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rfl
  | succ fuel ih =>
    intro st key key'
    rw [goK_succ, goK_succ]
    congr 1
    exact anyIdx_congr (fun c i => ih c _ _) _ _

/-- If one leaf makes the search succeed and another makes it fail, there is a path on whose
end the two leaves differ. -/
theorem goK_split (k A q2 C1 C2 bn : Nat) (leaf1 leaf2 : St → List Nat → Bool) :
    ∀ (a : Nat) (st : St) (key : List Nat),
      goK k A q2 C1 C2 bn leaf1 a st key = true → goK k A q2 C1 C2 bn leaf2 a st key = false →
      ∃ path : List Nat, leaf1 (stepPath k A q2 C2 st path) (path.reverse ++ key) = true ∧
        leaf2 (stepPath k A q2 C2 st path) (path.reverse ++ key) = false := by
  intro a
  induction a with
  | zero =>
    intro st key h1 h2
    exact ⟨[], h1, h2⟩
  | succ a ih =>
    intro st key h1 h2
    rw [goK_succ] at h1 h2
    cases hb : viol C1 bn st with
    | true =>
      rw [hb] at h2
      cases h2
    | false =>
      rw [hb] at h1 h2
      have h1' : anyIdx (fun c i => goK k A q2 C1 C2 bn leaf1 a c (i :: key))
          (children k A q2 C2 st) 0 = true := h1
      have h2' : anyIdx (fun c i => goK k A q2 C1 C2 bn leaf2 a c (i :: key))
          (children k A q2 C2 st) 0 = false := h2
      obtain ⟨i, hi1, hi2⟩ := anyIdx_split st _ 0 h1' h2'
      rw [Nat.zero_add] at hi1 hi2
      obtain ⟨path, hp1, hp2⟩ := ih _ _ hi1 hi2
      refine ⟨i :: path, ?_, ?_⟩
      · rw [List.reverse_cons, List.append_assoc, stepPath_cons]
        exact hp1
      · rw [List.reverse_cons, List.append_assoc, stepPath_cons]
        exact hp2

/-- Cutting a search: the paths of `cover` are all the paths of length `a` that the search
reaches, and nothing is found below their ends. -/
theorem ref_of_cover (k A q2 C1 C2 bn a b : Nat) (st : St) (cover : List (List Nat))
    (hc : goK k A q2 C1 C2 bn (leafCover cover) a st [] = false)
    (hall : ∀ rp ∈ cover, Ref k A q2 C1 C2 bn b (stepPath k A q2 C2 st rp.reverse)) :
    Ref k A q2 C1 C2 bn (a + b) st := by
  unfold Ref
  rw [← Bool.not_eq_true]
  intro h
  rw [goK_add] at h
  obtain ⟨path, hp1, hp2⟩ := goK_split k A q2 C1 C2 bn _ _ a st [] h hc
  rw [List.append_nil] at hp1 hp2
  have hmem : path.reverse ∈ cover := by
    apply memKey_mem
    have h3 : (!memKey path.reverse cover) = false := hp2
    cases hm : memKey path.reverse cover with
    | true => rfl
    | false =>
      rw [hm] at h3
      cases h3
  have h4 := hall _ hmem
  rw [List.reverse_reverse] at h4
  unfold Ref at h4
  rw [goK_key k A q2 C1 C2 bn b _ path.reverse []] at hp1
  rw [h4] at hp1
  cases hp1

theorem forall_nil {P : List Nat → Prop} : ∀ rp ∈ ([] : List (List Nat)), P rp := by
  intro rp h
  cases h

theorem forall_cons {P : List Nat → Prop} {a : List Nat} {l : List (List Nat)} (ha : P a)
    (hl : ∀ rp ∈ l, P rp) : ∀ rp ∈ a :: l, P rp := by
  intro rp h
  rcases List.mem_cons.mp h with h1 | h1
  · rw [h1]
    exact ha
  · exact hl rp h1

theorem forall_append {P : List Nat → Prop} {l1 l2 : List (List Nat)} (h1 : ∀ rp ∈ l1, P rp)
    (h2 : ∀ rp ∈ l2, P rp) : ∀ rp ∈ l1 ++ l2, P rp := by
  intro rp h
  rcases List.mem_append.mp h with h | h
  · exact h1 rp h
  · exact h2 rp h

/-- A group of paths checked by one evaluation. -/
theorem refs_of_all (k A q2 C1 C2 bn b : Nat) (st : St) (g : List (List Nat))
    (h : g.all (fun rp =>
      !goK k A q2 C1 C2 bn (fun _ _ => true) b (stepPath k A q2 C2 st rp.reverse) []) = true) :
    ∀ rp ∈ g, Ref k A q2 C1 C2 bn b (stepPath k A q2 C2 st rp.reverse) := by
  intro rp hrp
  have h1 := List.all_eq_true.mp h rp hrp
  unfold Ref
  cases hg : goK k A q2 C1 C2 bn (fun _ _ => true) b (stepPath k A q2 C2 st rp.reverse) [] with
  | false => rfl
  | true =>
    rw [hg] at h1
    cases h1

theorem forall_lt_zero {P : Nat → Prop} : ∀ i, i < 0 → P i := by
  intro i h
  cases h

theorem forall_lt_succ {P : Nat → Prop} {m : Nat} (h : ∀ i, i < m → P i) (hm : P m) :
    ∀ i, i < m + 1 → P i := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
  · exact h i h1
  · rw [h1]
    exact hm

/-- The whole search finds nothing if nothing is found below each of the states after the first
piece. -/
theorem search_false (k A q2 C1 C2 bn fuel m : Nat) (d : St)
    (hlen : (rootChildren k A q2 C2).length = m)
    (h : ∀ i, i < m → Ref k A q2 C1 C2 bn fuel (nthD (rootChildren k A q2 C2) i d)) :
    search k A q2 C1 C2 bn fuel = false := by
  unfold search
  apply anyIdx_false d
  intro i hi
  rw [goK_key k A q2 C1 C2 bn fuel _ [0 + i] []]
  exact h i (hlen ▸ hi)

end S
end SuperpermLowerBounds

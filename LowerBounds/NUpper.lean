import LowerBounds.NT4Config

/-!
# Theorems U and S of the written model: a standard configuration is a superpermutation

The upper direction.  `k ≥ 3`.

* `BValid.exists_ham`: a valid block configuration gives a Hamiltonian path `P` with
  `HPV(k) + cost = (k-2)! + wt(P) + k`, that is `D(P) = cost - (k-2)!` exactly.
* `NConfig.Valid.exists_ham`, `NConfig.Valid.exists_word`: a valid standard configuration of
  cost `(k-2)! + D` gives a Hamiltonian path of defect exactly `D` and a word over `Fin k` that
  contains all permutations and has exactly `HPV(k) + D` letters.
* `no_stdConfig_iff` (`k ≥ 5`): no valid standard configuration has defect at most `D` if and
  only if every covering word has at least `HPV(k) + D + 1` letters.  With Lemma T4:
  `no_stdConfig_noT4_iff`.

The path is the depth-first walk of the paper, built by insertion: start with the walk along
the line of the kernel (every block from its entry around the rotation class); then, in the
order of the ranks, insert the walk of a hanging component directly after its vertex `v`, where
the walk so far continues with `σ v`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-! ### The successor in a list, insertion after an element -/

/-- The element after `u` in a list. -/
def nextIn : List (Vtx k) → Vtx k → Option (Vtx k)
  | [], _ => none
  | [_], _ => none
  | a :: b :: l, u => if a = u then some b else nextIn (b :: l) u

theorem nextIn_cons_ne {a u : Vtx k} (l : List (Vtx k)) (h : a ≠ u) :
    nextIn (a :: l) u = nextIn l u := by
  cases l with
  | nil => rfl
  | cons b l =>
      show (if a = u then some b else nextIn (b :: l) u) = _
      rw [if_neg h]

theorem nextIn_cons_self (u : Vtx k) (l : List (Vtx k)) : nextIn (u :: l) u = l.head? := by
  cases l with
  | nil => rfl
  | cons b l =>
      show (if u = u then some b else nextIn (b :: l) u) = _
      rw [if_pos rfl]
      rfl

theorem nextIn_append_right {W : List (Vtx k)} (l : List (Vtx k)) {u : Vtx k} (h : u ∉ W) :
    nextIn (W ++ l) u = nextIn l u := by
  induction W with
  | nil => rfl
  | cons w W ih =>
      have hw : w ≠ u := by
        intro e
        apply h
        rw [← e]
        exact List.mem_cons_self
      have hW : u ∉ W := fun hm => h (List.mem_cons_of_mem _ hm)
      rw [List.cons_append, nextIn_cons_ne _ hw, ih hW]

theorem nextIn_append_left {W : List (Vtx k)} {u b : Vtx k} (l : List (Vtx k))
    (h : nextIn W u = some b) : nextIn (W ++ l) u = some b := by
  induction W with
  | nil => exact absurd h (by simp [nextIn])
  | cons w W ih =>
      by_cases hw : w = u
      · subst hw
        rw [nextIn_cons_self] at h
        rw [List.cons_append, nextIn_cons_self, List.head?_append, h]
        rfl
      · rw [nextIn_cons_ne _ hw] at h
        rw [List.cons_append, nextIn_cons_ne _ hw, ih h]

/-- Insert the list `W` directly after the element `v`. -/
def insAfter (v : Vtx k) (W : List (Vtx k)) : List (Vtx k) → List (Vtx k)
  | [] => []
  | a :: l => if a = v then a :: (W ++ l) else a :: insAfter v W l

theorem insAfter_cons_self (v : Vtx k) (W l : List (Vtx k)) :
    insAfter v W (v :: l) = v :: (W ++ l) := by
  show (if v = v then v :: (W ++ l) else v :: insAfter v W l) = _
  rw [if_pos rfl]

theorem insAfter_cons_ne {a v : Vtx k} (W l : List (Vtx k)) (h : a ≠ v) :
    insAfter v W (a :: l) = a :: insAfter v W l := by
  show (if a = v then a :: (W ++ l) else a :: insAfter v W l) = _
  rw [if_neg h]

theorem mem_insAfter {v x : Vtx k} {W l : List (Vtx k)} :
    x ∈ insAfter v W l ↔ x ∈ l ∨ (v ∈ l ∧ x ∈ W) := by
  induction l with
  | nil =>
      constructor
      · intro h
        exact absurd h (by simp [insAfter])
      · rintro (h | ⟨h, _⟩)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
  | cons a l ih =>
      by_cases h : a = v
      · subst h
        rw [insAfter_cons_self]
        constructor
        · intro hx
          rcases List.mem_cons.mp hx with h1 | h1
          · left
            rw [h1]
            exact List.mem_cons_self
          · rcases List.mem_append.mp h1 with h2 | h2
            · exact Or.inr ⟨List.mem_cons_self, h2⟩
            · exact Or.inl (List.mem_cons_of_mem _ h2)
        · rintro (h1 | ⟨_, h2⟩)
          · rcases List.mem_cons.mp h1 with h3 | h3
            · rw [h3]
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr h3))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl h2))
      · rw [insAfter_cons_ne _ _ h, List.mem_cons, ih]
        constructor
        · rintro (h1 | h1 | ⟨h1, h2⟩)
          · left
            rw [h1]
            exact List.mem_cons_self
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · rcases List.mem_cons.mp h1 with h3 | h3
            · exact Or.inl h3
            · exact Or.inr (Or.inl h3)
          · rcases List.mem_cons.mp h1 with h3 | h3
            · exact absurd h3.symm h
            · exact Or.inr (Or.inr ⟨h3, h2⟩)

theorem length_insAfter {v : Vtx k} {W : List (Vtx k)} : ∀ {l : List (Vtx k)}, v ∈ l →
    (insAfter v W l).length = l.length + W.length
  | [], h => absurd h (by simp)
  | a :: l, h => by
      by_cases ha : a = v
      · subst ha
        rw [insAfter_cons_self]
        simp only [List.length_cons, List.length_append]
        omega
      · have hv : v ∈ l := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1.symm ha
          · exact h1
        rw [insAfter_cons_ne _ _ ha]
        simp only [List.length_cons]
        rw [length_insAfter hv]
        omega

theorem head?_insAfter (v : Vtx k) (W l : List (Vtx k)) : (insAfter v W l).head? = l.head? := by
  cases l with
  | nil => rfl
  | cons a l =>
      by_cases ha : a = v
      · subst ha
        rw [insAfter_cons_self]
        rfl
      · rw [insAfter_cons_ne _ _ ha]
        rfl

theorem insAfter_nodup {v : Vtx k} {W l : List (Vtx k)} (hl : l.Nodup) (hW : W.Nodup)
    (hd : ∀ x ∈ W, x ∉ l) : (insAfter v W l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
      obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
      have hd' : ∀ x ∈ W, x ∉ l := fun x hx hm => hd x hx (List.mem_cons_of_mem _ hm)
      have haW : a ∉ W := fun hm => hd a hm List.mem_cons_self
      by_cases h : a = v
      · subst h
        rw [insAfter_cons_self, List.nodup_cons]
        refine ⟨?_, ?_⟩
        · intro hm
          rcases List.mem_append.mp hm with h1 | h1
          · exact haW h1
          · exact ha h1
        · rw [List.nodup_append]
          refine ⟨hW, hl', ?_⟩
          intro x hx y hy hxy
          apply hd' x hx
          rw [hxy]
          exact hy
      · rw [insAfter_cons_ne _ _ h, List.nodup_cons]
        refine ⟨?_, ih hl' hd'⟩
        intro hm
        rcases mem_insAfter.mp hm with h1 | ⟨_, h1⟩
        · exact ha h1
        · exact haW h1

theorem nextIn_insAfter_ne {v u : Vtx k} {W : List (Vtx k)} (l : List (Vtx k)) (huv : u ≠ v)
    (huW : u ∉ W) : nextIn (insAfter v W l) u = nextIn l u := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : a = v
      · subst h
        rw [insAfter_cons_self, nextIn_cons_ne _ (Ne.symm huv), nextIn_append_right _ huW,
          nextIn_cons_ne _ (Ne.symm huv)]
      · rw [insAfter_cons_ne _ _ h]
        by_cases hau : a = u
        · subst hau
          rw [nextIn_cons_self, nextIn_cons_self, head?_insAfter]
        · rw [nextIn_cons_ne _ hau, nextIn_cons_ne _ hau, ih]

theorem nextIn_insAfter_mem {v u b : Vtx k} {W : List (Vtx k)} : ∀ (l : List (Vtx k)),
    nextIn W u = some b → u ∉ l → v ∈ l → nextIn (insAfter v W l) u = some b
  | [], _, _, hvl => absurd hvl (by simp)
  | a :: l, hW, hul, hvl => by
      have hau : a ≠ u := by
        intro e
        apply hul
        rw [← e]
        exact List.mem_cons_self
      have hul' : u ∉ l := fun hm => hul (List.mem_cons_of_mem _ hm)
      by_cases h : a = v
      · subst h
        rw [insAfter_cons_self, nextIn_cons_ne _ hau, nextIn_append_left _ hW]
      · have hvl' : v ∈ l := by
          rcases List.mem_cons.mp hvl with h1 | h1
          · exact absurd h1.symm h
          · exact h1
        rw [insAfter_cons_ne _ _ h, nextIn_cons_ne _ hau, nextIn_insAfter_mem l hW hul' hvl']

/-! ### Sums over consecutive elements -/

theorem lsum_cons (φ : Vtx k → Vtx k → ℕ) (x : Vtx k) (R : List (Vtx k)) :
    lsum φ (x :: R) = (match R.head? with | some h => φ x h | none => 0) + lsum φ R := by
  cases R with
  | nil => rfl
  | cons b R => rfl

theorem lsum_eq_zipWith (φ : Vtx k → Vtx k → ℕ) : ∀ l : List (Vtx k),
    lsum φ l = (l.zipWith φ l.tail).sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
      have ih := lsum_eq_zipWith φ (b :: l)
      show φ a b + lsum φ (b :: l) = _
      rw [ih]
      rfl

theorem lsum_range_map (φ : Vtx k → Vtx k → ℕ) (f : ℕ → Vtx k) : ∀ m : ℕ,
    lsum φ ((List.range (m + 1)).map f) = ∑ j ∈ Finset.range m, φ (f j) (f (j + 1))
  | 0 => by simp [lsum]
  | m + 1 => by
      have ih := lsum_range_map φ f m
      have hlast : ((List.range (m + 1)).map f).getLast? = some (f m) := by
        simp [List.getLast?_range]
      have hsplit : (List.range (m + 1 + 1)).map f =
          (List.range (m + 1)).map f ++ [f (m + 1)] := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [hsplit, lsum_append φ _ _ (f m) (f (m + 1)) hlast rfl, ih, Finset.sum_range_succ]
      simp [lsum]

/-- Inserting `W` after `v`, where the list continues with `s`: the edge `v → s` is replaced by
`v → head W`, the edges of `W`, and `last W → s`. -/
theorem lsum_insAfter (φ : Vtx k → Vtx k → ℕ) {v s a b : Vtx k} {W : List (Vtx k)}
    (hWa : W.head? = some a) (hWb : W.getLast? = some b) : ∀ l : List (Vtx k),
    nextIn l v = some s →
    lsum φ (insAfter v W l) + φ v s = lsum φ l + φ v a + lsum φ W + φ b s
  | [], h => absurd h (by simp [nextIn])
  | x :: l, h => by
      by_cases hx : x = v
      · subst hx
        rw [nextIn_cons_self] at h
        obtain ⟨l', hl'⟩ := List.head?_eq_some_iff.mp h
        rw [hl', insAfter_cons_self]
        have e1 : x :: (W ++ s :: l') = [x] ++ (W ++ s :: l') := rfl
        have hh : (W ++ s :: l').head? = some a := by
          rw [List.head?_append, hWa]
          rfl
        rw [e1, lsum_append φ [x] (W ++ s :: l') x a rfl hh,
          lsum_append φ W (s :: l') b s hWb rfl]
        simp only [lsum]
        omega
      · rw [nextIn_cons_ne _ hx] at h
        have ih := lsum_insAfter φ hWa hWb l h
        rw [insAfter_cons_ne _ _ hx, lsum_cons, lsum_cons, head?_insAfter]
        omega

/-! ### Blocks and lines as walks -/

/-- A block walked from its entry: `e, σ e, …, σ^(k-1) e`. -/
def blockList (e : Vtx k) : List (Vtx k) := (List.range k).map (fun i => sigma^[i] e)

/-- The walk along a line: its blocks one after the other. -/
def lineWalk (L : List (Vtx k)) : List (Vtx k) := L.flatMap blockList

theorem mem_blockList (hk : 1 ≤ k) {x e : Vtx k} :
    x ∈ blockList e ↔ (x : List ℕ) ~r (e : List ℕ) := by
  unfold blockList
  rw [List.mem_map]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact rotClass_eq_iff.mp (Hunter.ProofsExitless.rotClass_sigma_iter i e)
  · intro h
    have hc : x ∈ cyc e := Hunter.ProofsExitless.mem_cyc.mpr (rotClass_eq_iff.mpr h)
    obtain ⟨r, hr, hx⟩ := (Hunter.ProofsExitless.mem_cyc_iff_exists hk).mp hc
    exact ⟨r, List.mem_range.mpr hr, hx.symm⟩

theorem blockList_nodup (e : Vtx k) : (blockList e).Nodup := by
  unfold blockList
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj h
  exact Hunter.ProofsExitless.sigma_iter_inj e (List.mem_range.mp hi) (List.mem_range.mp hj) h

theorem blockList_length (e : Vtx k) : (blockList e).length = k := by
  simp [blockList]

theorem blockList_head? (hk : 1 ≤ k) (e : Vtx k) : (blockList e).head? = some e := by
  unfold blockList
  rw [List.head?_map, List.head?_range, if_neg (by omega)]
  rfl

theorem blockList_getLast? (hk : 1 ≤ k) (e : Vtx k) :
    (blockList e).getLast? = some (sigmaInv e) := by
  unfold blockList
  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
  show some (sigma^[k - 1] e) = _
  rw [sigma_iter_pred hk]

theorem blockList_ne_nil (hk : 1 ≤ k) (e : Vtx k) : blockList e ≠ [] := by
  intro h
  have h1 := blockList_head? hk e
  rw [h] at h1
  simp at h1

theorem lsum_blockList (hk : 1 ≤ k) (e : Vtx k) : lsum (ew k) (blockList e) = k - 1 := by
  have h1 : ∀ j, ew k (sigma^[j] e) (sigma^[j + 1] e) = 1 := by
    intro j
    rw [Function.iterate_succ_apply']
    exact Hunter.ew_sigma hk _
  have hr : List.range k = List.range (k - 1 + 1) := by
    rw [Nat.sub_add_cancel hk]
  unfold blockList
  rw [hr, lsum_range_map, Finset.sum_congr rfl (fun j _ => h1 j)]
  simp

theorem nextIn_map_range' (f : ℕ → Vtx k) : ∀ (n s i : ℕ),
    (∀ a b, s ≤ a → a < s + n → s ≤ b → b < s + n → f a = f b → a = b) →
    s ≤ i → i + 1 < s + n → nextIn ((List.range' s n).map f) (f i) = some (f (i + 1))
  | 0, s, i, _, h1, h2 => by omega
  | 1, s, i, _, h1, h2 => by omega
  | n + 2, s, i, hinj, h1, h2 => by
      have e : (List.range' s (n + 2)).map f =
          f s :: f (s + 1) :: (List.range' (s + 1 + 1) n).map f := by
        rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons]
      by_cases his : i = s
      · rw [e, his]
        show (if f s = f s then some (f (s + 1)) else _) = _
        rw [if_pos rfl]
      · have hne : f s ≠ f i := by
          intro h
          exact his (hinj s i (le_refl _) (by omega) h1 (by omega) h).symm
        have ih := nextIn_map_range' f (n + 1) (s + 1) i
          (fun a b ha ha' hb hb' => hinj a b (by omega) (by omega) (by omega) (by omega))
          (by omega) (by omega)
        have e2 : (List.range' (s + 1) (n + 1)).map f =
            f (s + 1) :: (List.range' (s + 1 + 1) n).map f := by
          rw [List.range'_succ, List.map_cons]
        rw [e, nextIn_cons_ne _ hne, ← e2]
        exact ih

theorem nextIn_blockList (e : Vtx k) {i : ℕ} (hi : i + 1 < k) :
    nextIn (blockList e) (sigma^[i] e) = some (sigma^[i + 1] e) := by
  unfold blockList
  rw [List.range_eq_range']
  exact nextIn_map_range' (fun i => sigma^[i] e) k 0 i
    (fun a b _ ha _ hb h => Hunter.ProofsExitless.sigma_iter_inj e (by omega) (by omega) h)
    (Nat.zero_le _) (by omega)

theorem mem_lineWalk (hk : 1 ≤ k) {x : Vtx k} {L : List (Vtx k)} :
    x ∈ lineWalk L ↔ ∃ e ∈ L, (x : List ℕ) ~r (e : List ℕ) := by
  unfold lineWalk
  rw [List.mem_flatMap]
  exact ⟨fun ⟨e, he, hx⟩ => ⟨e, he, (mem_blockList hk).mp hx⟩,
    fun ⟨e, he, hx⟩ => ⟨e, he, (mem_blockList hk).mpr hx⟩⟩

theorem lineWalk_nodup (hk : 1 ≤ k) {L : List (Vtx k)}
    (hL : L.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))) :
    (lineWalk L).Nodup := by
  unfold lineWalk
  rw [List.nodup_flatMap]
  refine ⟨fun e _ => blockList_nodup e, hL.imp ?_⟩
  intro a b hab
  show ∀ ⦃x : Vtx k⦄, x ∈ blockList a → x ∈ blockList b → False
  intro x hxa hxb
  exact hab (((mem_blockList hk).mp hxa).symm.trans ((mem_blockList hk).mp hxb))

theorem length_lineWalk : ∀ L : List (Vtx k), (lineWalk L).length = k * L.length
  | [] => by simp [lineWalk]
  | e :: L => by
      have ih := length_lineWalk L
      have e1 : lineWalk (e :: L) = blockList e ++ lineWalk L := by
        unfold lineWalk
        rw [List.flatMap_cons]
      rw [e1, List.length_append, blockList_length, ih, List.length_cons, Nat.mul_succ]
      omega

theorem lineWalk_head? (hk : 1 ≤ k) {L : List (Vtx k)} {a : Vtx k} (h : L.head? = some a) :
    (lineWalk L).head? = some a := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp h
  rw [hys]
  unfold lineWalk
  rw [List.flatMap_cons, List.head?_append, blockList_head? hk]
  rfl

theorem lineWalk_getLast? (hk : 1 ≤ k) {L : List (Vtx k)} {b : Vtx k} (h : L.getLast? = some b) :
    (lineWalk L).getLast? = some (sigmaInv b) := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  rw [hys]
  unfold lineWalk
  rw [List.flatMap_append, List.flatMap_singleton,
    getLast?_append_of_ne_nil (blockList_ne_nil hk b), blockList_getLast? hk]

/-- The weight of the walk along a line: `k - 1` in every block, and the links. -/
theorem lsum_lineWalk (hk : 1 ≤ k) : ∀ L : List (Vtx k),
    lsum (ew k) (lineWalk L) = (k - 1) * L.length + lsum (fun a b => ew k (sigmaInv a) b) L
  | [] => by simp [lineWalk, lsum]
  | [e] => by
      have e0 : lineWalk [e] = blockList e := by
        unfold lineWalk
        rw [List.flatMap_singleton]
      rw [e0, lsum_blockList hk]
      simp [lsum]
  | e :: e' :: rest => by
      have ih := lsum_lineWalk hk (e' :: rest)
      have e1 : lineWalk (e :: e' :: rest) = blockList e ++ lineWalk (e' :: rest) := by
        unfold lineWalk
        rw [List.flatMap_cons]
      have e2 : (k - 1) * (rest.length + 1 + 1) = (k - 1) * (rest.length + 1) + (k - 1) :=
        Nat.mul_succ _ _
      rw [e1, lsum_append (ew k) _ _ (sigmaInv e) e' (blockList_getLast? hk e)
        (lineWalk_head? hk rfl), lsum_blockList hk, ih]
      simp only [lsum, List.length_cons]
      rw [e2]
      omega

/-- In the walk along a line a vertex that is not the exit of its block is followed by its
rotation. -/
theorem nextIn_lineWalk (hk : 1 ≤ k) {L : List (Vtx k)}
    (hL : L.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))) {e u : Vtx k}
    (he : e ∈ L) (hue : (u : List ℕ) ~r (e : List ℕ)) (hne : sigma u ≠ e) :
    nextIn (lineWalk L) u = some (sigma u) := by
  obtain ⟨A, B, hAB⟩ := List.append_of_mem he
  rw [hAB] at hL ⊢
  have hsplit : lineWalk (A ++ e :: B) = lineWalk A ++ (blockList e ++ lineWalk B) := by
    unfold lineWalk
    rw [List.flatMap_append, List.flatMap_cons]
  have huA : u ∉ lineWalk A := by
    intro hm
    obtain ⟨a, ha, hua⟩ := (mem_lineWalk hk).mp hm
    exact (List.pairwise_append.mp hL).2.2 a ha e List.mem_cons_self (hua.symm.trans hue)
  have hc : u ∈ cyc e := Hunter.ProofsExitless.mem_cyc.mpr (rotClass_eq_iff.mpr hue)
  obtain ⟨i, hi, hui⟩ := (Hunter.ProofsExitless.mem_cyc_iff_exists hk).mp hc
  have hi1 : i + 1 < k := by
    by_contra hcon
    have hik : i = k - 1 := by omega
    apply hne
    rw [hui, hik, sigma_iter_pred hk, Hunter.ProofsStructure.sigma_sigmaInv]
  have hsu : sigma u = sigma^[i + 1] e := by
    rw [hui]
    exact (Function.iterate_succ_apply' sigma i e).symm
  rw [hsplit, nextIn_append_right _ huA, hsu, hui]
  exact nextIn_append_left _ (nextIn_blockList e hi1)

/-! ### The walk through a block configuration -/

/-- The two edges of an attachment. -/
noncomputable def attW (k : ℕ) : Option (Vtx k) → Option (Vtx k) → Option (Vtx k) → ℕ
  | some v, some b, some a => ew k (sigmaInv b) (sigma v) + ew k v a
  | _, _, _ => 0

/-- What a hanging component adds to the weight of the walk, plus 1. -/
noncomputable def hangW (H : BComp k) : ℕ :=
  lsum (ew k) (lineWalk H.line) + attW k H.slot H.line.getLast? H.line.head?

/-- The walk `acc` passes the kernel `K` and the hanging components of `Done`. -/
structure PathInv (cs : List (BComp k)) (K : BComp k) (Done : List (BComp k))
    (acc : List (Vtx k)) : Prop where
  nodup : acc.Nodup
  mem : ∀ x : Vtx k, x ∈ acc ↔ (∃ e ∈ K.line, (x : List ℕ) ~r (e : List ℕ)) ∨
    ∃ H ∈ Done, ∃ e ∈ H.line, (x : List ℕ) ~r (e : List ℕ)
  next : ∀ C ∈ cs, C ∉ Done → ∀ v, C.slot = some v → v ∈ acc → nextIn acc v = some (sigma v)
  weight : lsum (ew k) acc + Done.length = lsum (ew k) (lineWalk K.line) + (Done.map hangW).sum
  len : acc.length = k * (K.line.length + (Done.map (fun H => H.line.length)).sum)

theorem pathInv_base (hk : 1 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {K : BComp k}
    (hK : K ∈ cs) : PathInv cs K [] (lineWalk K.line) := by
  refine ⟨lineWalk_nodup hk (hv.inner K hK), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [mem_lineWalk hk]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨H, hH, _⟩)
      · exact h
      · exact absurd hH (by simp)
  · intro C hC _ v hslot hmem
    obtain ⟨e, he, hrot⟩ := (mem_lineWalk hk).mp hmem
    refine nextIn_lineWalk hk (hv.inner K hK) he hrot ?_
    intro h
    apply hv.slot C hC v hslot K hK
    rw [h]
    exact he
  · simp
  · simp [length_lineWalk]

theorem pathInv_step (hk : 1 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {K : BComp k}
    (hK : K ∈ cs) {Done : List (BComp k)} {acc : List (Vtx k)} (inv : PathInv cs K Done acc)
    {H : BComp k} (hH : H ∈ cs) (hHD : H ∉ Done) (hHK : H ≠ K) (hDone : ∀ D ∈ Done, D ∈ cs)
    {v : Vtx k} (hslot : H.slot = some v) (hvacc : v ∈ acc) :
    PathInv cs K (H :: Done) (insAfter v (lineWalk H.line) acc) := by
  have hWdisj : ∀ x ∈ lineWalk H.line, x ∉ acc := by
    intro x hx hxa
    obtain ⟨e, he, hxe⟩ := (mem_lineWalk hk).mp hx
    rcases (inv.mem x).mp hxa with ⟨e', he', hxe'⟩ | ⟨H', hH', e', he', hxe'⟩
    · exact hHK (hv.eq_of_common hH hK he he' (hxe.symm.trans hxe'))
    · have hEq := hv.eq_of_common hH (hDone H' hH') he he' (hxe.symm.trans hxe')
      apply hHD
      rw [hEq]
      exact hH'
  have hLne := hv.line_ne H hH
  obtain ⟨a, ha⟩ : ∃ a, H.line.head? = some a := ⟨_, List.head?_eq_some_head hLne⟩
  obtain ⟨b, hb⟩ : ∃ b, H.line.getLast? = some b := ⟨_, List.getLast?_eq_some_getLast hLne⟩
  have hnextv := inv.next H hH hHD v hslot hvacc
  refine ⟨insAfter_nodup inv.nodup (lineWalk_nodup hk (hv.inner H hH)) hWdisj, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [mem_insAfter, inv.mem x, mem_lineWalk hk]
    constructor
    · rintro ((h | ⟨H', hH', h⟩) | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨H', List.mem_cons_of_mem _ hH', h⟩
      · exact Or.inr ⟨H, List.mem_cons_self, h⟩
    · rintro (h | ⟨H', hH', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hH' with h1 | h1
        · rw [h1] at h
          exact Or.inr ⟨hvacc, h⟩
        · exact Or.inl (Or.inr ⟨H', h1, h⟩)
  · intro C hC hCD v' hslot' hmem'
    have hCH : C ≠ H := by
      intro e
      apply hCD
      rw [e]
      exact List.mem_cons_self
    have hCD' : C ∉ Done := fun h => hCD (List.mem_cons_of_mem _ h)
    have hvv : v' ≠ v := by
      intro e
      apply hCH
      apply hv.slots C hC H hH v' hslot'
      rw [e]
      exact hslot
    rcases mem_insAfter.mp hmem' with h1 | ⟨_, h1⟩
    · have hW' : v' ∉ lineWalk H.line := fun h2 => hWdisj v' h2 h1
      rw [nextIn_insAfter_ne _ hvv hW']
      exact inv.next C hC hCD' v' hslot' h1
    · obtain ⟨e, he, hrot⟩ := (mem_lineWalk hk).mp h1
      have hnx : nextIn (lineWalk H.line) v' = some (sigma v') := by
        refine nextIn_lineWalk hk (hv.inner H hH) he hrot ?_
        intro h
        apply hv.slot C hC v' hslot' H hH
        rw [h]
        exact he
      exact nextIn_insAfter_mem acc hnx (fun h2 => hWdisj v' h1 h2) hvacc
  · have h := lsum_insAfter (ew k) (lineWalk_head? hk ha) (lineWalk_getLast? hk hb) acc hnextv
    have h1 : ew k v (sigma v) = 1 := Hunter.ew_sigma hk v
    have hW : hangW H = lsum (ew k) (lineWalk H.line) +
        (ew k (sigmaInv b) (sigma v) + ew k v a) := by
      unfold hangW
      rw [hslot, hb, ha]
      rfl
    have hw := inv.weight
    rw [List.length_cons, List.map_cons, List.sum_cons, hW]
    omega
  · rw [length_insAfter hvacc, inv.len, length_lineWalk, List.map_cons, List.sum_cons]
    simp only [Nat.mul_add]
    omega

/-- Add the components of a list, one after the other. -/
theorem pathInv_add (hk : 1 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {K : BComp k}
    (hK : K ∈ cs) : ∀ (N Done : List (BComp k)) (acc : List (Vtx k)), PathInv cs K Done acc →
    N.Nodup → Done.Nodup → (∀ H ∈ N, H ∈ cs ∧ H ≠ K ∧ H ∉ Done) → (∀ D ∈ Done, D ∈ cs) →
    (∀ H ∈ N, ∃ v, H.slot = some v ∧ v ∈ acc) →
    ∃ (Done' : List (BComp k)) (acc' : List (Vtx k)), PathInv cs K Done' acc' ∧ Done'.Nodup ∧
      (∀ D ∈ Done', D ∈ cs) ∧ ∀ H, H ∈ Done' ↔ H ∈ N ∨ H ∈ Done
  | [], Done, acc, inv, _, hnd, _, hsub, _ =>
      ⟨Done, acc, inv, hnd, hsub, fun H => ⟨fun h => Or.inr h, fun h => by
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h⟩⟩
  | H :: N, Done, acc, inv, hN, hnd, hmemN, hsub, hslots => by
      obtain ⟨hHN, hN'⟩ := List.nodup_cons.mp hN
      obtain ⟨hHcs, hHK, hHD⟩ := hmemN H List.mem_cons_self
      obtain ⟨v, hslot, hvacc⟩ := hslots H List.mem_cons_self
      have inv' := pathInv_step hk hv hK inv hHcs hHD hHK hsub hslot hvacc
      have hnd' : (H :: Done).Nodup := List.nodup_cons.mpr ⟨hHD, hnd⟩
      have hmemN' : ∀ H' ∈ N, H' ∈ cs ∧ H' ≠ K ∧ H' ∉ H :: Done := by
        intro H' hH'
        obtain ⟨h1, h2, h3⟩ := hmemN H' (List.mem_cons_of_mem _ hH')
        refine ⟨h1, h2, ?_⟩
        intro hm
        rcases List.mem_cons.mp hm with h4 | h4
        · apply hHN
          rw [← h4]
          exact hH'
        · exact h3 h4
      have hsub' : ∀ D ∈ H :: Done, D ∈ cs := by
        intro D hD
        rcases List.mem_cons.mp hD with h4 | h4
        · rw [h4]
          exact hHcs
        · exact hsub D h4
      have hslots' : ∀ H' ∈ N, ∃ v', H'.slot = some v' ∧
          v' ∈ insAfter v (lineWalk H.line) acc := by
        intro H' hH'
        obtain ⟨v', h1, h2⟩ := hslots H' (List.mem_cons_of_mem _ hH')
        exact ⟨v', h1, mem_insAfter.mpr (Or.inl h2)⟩
      obtain ⟨Done', acc', inv'', hnd'', hsub'', hmem''⟩ :=
        pathInv_add hk hv hK N (H :: Done) _ inv' hN' hnd' hmemN' hsub' hslots'
      refine ⟨Done', acc', inv'', hnd'', hsub'', ?_⟩
      intro H'
      rw [hmem'' H']
      constructor
      · rintro (h | h)
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with h4 | h4
          · left
            rw [h4]
            exact List.mem_cons_self
          · exact Or.inr h4
      · rintro (h | h)
        · rcases List.mem_cons.mp h with h4 | h4
          · right
            rw [h4]
            exact List.mem_cons_self
          · exact Or.inl h4
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- All hanging components of rank below `r` can be added. -/
theorem pathInv_rank (hk : 1 ≤ k) {K : BComp k} {Hs : List (BComp k)} (hv : BValid (K :: Hs))
    (hHs : ∀ H ∈ Hs, H.slot ≠ none) : ∀ r : ℕ, ∃ (Done : List (BComp k)) (acc : List (Vtx k)),
      PathInv (K :: Hs) K Done acc ∧ Done.Nodup ∧ (∀ D ∈ Done, D ∈ K :: Hs) ∧
        ∀ H, H ∈ Done ↔ H ∈ Hs ∧ H.rank < r := by
  have hKmem : K ∈ K :: Hs := List.mem_cons_self
  obtain ⟨hKnot, hHsnd⟩ := List.nodup_cons.mp hv.nodup
  intro r
  induction r with
  | zero =>
      refine ⟨[], lineWalk K.line, pathInv_base hk hv hKmem, List.nodup_nil, ?_, ?_⟩
      · intro D hD
        exact absurd hD (by simp)
      · intro H
        constructor
        · intro h
          exact absurd h (by simp)
        · rintro ⟨_, h⟩
          omega
  | succ r ih =>
      obtain ⟨Done, acc, inv, hnd, hsub, hmem⟩ := ih
      obtain ⟨N, hNdef⟩ : ∃ N, N = Hs.filter (fun H => H.rank = r) := ⟨_, rfl⟩
      have hNmem : ∀ H, H ∈ N ↔ H ∈ Hs ∧ H.rank = r := by
        intro H
        rw [hNdef, List.mem_filter]
        simp
      have hNnd : N.Nodup := by
        rw [hNdef]
        exact hHsnd.filter _
      have h1 : ∀ H ∈ N, H ∈ K :: Hs ∧ H ≠ K ∧ H ∉ Done := by
        intro H hH
        obtain ⟨hHs', hr⟩ := (hNmem H).mp hH
        refine ⟨List.mem_cons_of_mem _ hHs', ?_, ?_⟩
        · intro e
          apply hKnot
          rw [← e]
          exact hHs'
        · intro hD
          have := ((hmem H).mp hD).2
          omega
      have h2 : ∀ H ∈ N, ∃ v, H.slot = some v ∧ v ∈ acc := by
        intro H hH
        obtain ⟨hHs', hr⟩ := (hNmem H).mp hH
        obtain ⟨v, hslot⟩ := Option.ne_none_iff_exists'.mp (hHs H hHs')
        refine ⟨v, hslot, ?_⟩
        obtain ⟨D, hD, e, he, hrot⟩ := hv.cover v
        have hlt := hv.forest H (List.mem_cons_of_mem _ hHs') v hslot D hD ⟨e, he, hrot⟩
        rw [inv.mem]
        rcases List.mem_cons.mp hD with h3 | h3
        · rw [h3] at he
          exact Or.inl ⟨e, he, hrot⟩
        · exact Or.inr ⟨D, (hmem D).mpr ⟨h3, by omega⟩, e, he, hrot⟩
      obtain ⟨Done', acc', inv', hnd', hsub', hmem'⟩ :=
        pathInv_add hk hv hKmem N Done acc inv hNnd hnd h1 hsub h2
      refine ⟨Done', acc', inv', hnd', hsub', ?_⟩
      intro H
      rw [hmem' H, hNmem H, hmem H]
      constructor
      · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
        · exact ⟨h3, by omega⟩
        · exact ⟨h3, by omega⟩
      · rintro ⟨h3, h4⟩
        by_cases h5 : H.rank = r
        · exact Or.inl ⟨h3, h5⟩
        · exact Or.inr ⟨h3, by omega⟩

theorem exists_rank_bound : ∀ l : List (BComp k), ∃ r, ∀ H ∈ l, H.rank < r
  | [] => ⟨0, fun H h => absurd h (by simp)⟩
  | C :: l => by
      obtain ⟨r, hr⟩ := exists_rank_bound l
      refine ⟨max r (C.rank + 1), ?_⟩
      intro H hH
      rcases List.mem_cons.mp hH with h | h
      · rw [h]
        omega
      · have := hr H h
        omega

/-! ### The weight -/

theorem lsum_psi : ∀ L : List (Vtx k), L.IsChain (GoodLink k) → L ≠ [] →
    lsum (fun a b => ew k (sigmaInv a) b) L + 2 = lsum (costLink k) L + 2 * L.length
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | e :: e' :: rest, hc, _ => by
      rw [List.isChain_cons_cons] at hc
      have ih := lsum_psi (e' :: rest) hc.2 (List.cons_ne_nil _ _)
      have h2 := hc.1.1
      simp only [lsum, List.length_cons, costLink] at ih ⊢
      omega

theorem BValid.w0_ge (hk : 1 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {H : BComp k}
    (hH : H ∈ cs) {v b : Vtx k} (hslot : H.slot = some v) (hb : H.line.getLast? = some b) :
    2 ≤ ew k (sigmaInv b) (sigma v) := by
  have h1 := Hunter.ProofsExitless.ew_ge_one hk (sigmaInv b) (sigma v)
  have hne : ew k (sigmaInv b) (sigma v) ≠ 1 := by
    intro hone
    have h := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    rw [Hunter.ProofsStructure.sigma_sigmaInv] at h
    apply hv.slot H hH v hslot H hH
    rw [h]
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hb
    rw [hys]
    simp
  omega

theorem BValid.w1_ge (hk : 1 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {H : BComp k}
    (hH : H ∈ cs) {v a : Vtx k} (hslot : H.slot = some v) (ha : H.line.head? = some a) :
    2 ≤ ew k v a := by
  have h1 := Hunter.ProofsExitless.ew_ge_one hk v a
  have hne : ew k v a ≠ 1 := by
    intro hone
    have h := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    apply hv.slot H hH v hslot H hH
    rw [← h]
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp ha
    rw [hys]
    exact List.mem_cons_self
  omega

/-- The walk along the line of a component and its cost. -/
theorem lineWalk_weight (hk : 2 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {C : BComp k}
    (hC : C ∈ cs) :
    lsum (ew k) (lineWalk C.line) + 3 = (k + 1) * C.line.length + lineCost C.line := by
  have h1 := lsum_lineWalk (by omega : 1 ≤ k) C.line
  have h2 := lsum_psi C.line (hv.chain hk hC) (hv.line_ne C hC)
  have h3 : (k + 1) * C.line.length = (k - 1) * C.line.length + 2 * C.line.length := by
    rw [← Nat.add_mul]
    congr 1
    omega
  unfold lineCost
  rw [linkSum_eq_lsum, h1, h3]
  omega

theorem hangW_eq (hk : 2 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {H : BComp k}
    (hH : H ∈ cs) (hs : H.slot ≠ none) :
    hangW H + 2 = (k + 1) * H.line.length + H.cost + 3 := by
  obtain ⟨v, hslot⟩ := Option.ne_none_iff_exists'.mp hs
  have hLne := hv.line_ne H hH
  obtain ⟨a, ha⟩ : ∃ a, H.line.head? = some a := ⟨_, List.head?_eq_some_head hLne⟩
  obtain ⟨b, hb⟩ : ∃ b, H.line.getLast? = some b := ⟨_, List.getLast?_eq_some_getLast hLne⟩
  have h0 := hv.w0_ge (by omega) hH hslot hb
  have h1 := hv.w1_ge (by omega) hH hslot ha
  have hw := lineWalk_weight hk hv hH
  have e1 : hangW H = lsum (ew k) (lineWalk H.line) +
      (ew k (sigmaInv b) (sigma v) + ew k v a) := by
    unfold hangW
    rw [hslot, hb, ha]
    rfl
  have e2 : H.cost = lineCost H.line + (ew k (sigmaInv b) (sigma v) + ew k v a - 4) := by
    unfold BComp.cost BComp.att
    rw [hslot, hb, ha]
    rfl
  rw [e1, e2]
  omega

theorem sum_hangW (hk : 2 ≤ k) {cs : List (BComp k)} (hv : BValid cs) :
    ∀ l : List (BComp k), (∀ H ∈ l, H ∈ cs ∧ H.slot ≠ none) →
      (l.map hangW).sum + 2 * l.length =
        (k + 1) * (l.map (fun H => H.line.length)).sum + (l.map BComp.cost).sum + 3 * l.length
  | [], _ => by simp
  | H :: l, h => by
      have ih := sum_hangW hk hv l (fun H' h' => h H' (List.mem_cons_of_mem _ h'))
      obtain ⟨hH, hs⟩ := h H List.mem_cons_self
      have h1 := hangW_eq hk hv hH hs
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add]
      omega

/-- **Theorems U and S for block configurations.**  A valid block configuration is a
Hamiltonian path whose defect is exactly `cost - (k-2)!`. -/
theorem BValid.exists_ham (hk : 3 ≤ k) {cs : List (BComp k)} (hv : BValid cs) :
    ∃ P : HPath k, P.IsHamiltonian ∧ hpv k + bcost cs = (k - 2).factorial + (P.wtP + k) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨K, Hs, rfl, hKs, hHs⟩ := hv.kernel
  obtain ⟨_, hHsnd⟩ := List.nodup_cons.mp hv.nodup
  obtain ⟨r, hr⟩ := exists_rank_bound Hs
  obtain ⟨Done, acc, inv, hnd, _, hmem⟩ := pathInv_rank hk1 hv hHs r
  have hperm : Done.Perm Hs := by
    rw [List.perm_ext_iff_of_nodup hnd hHsnd]
    intro H
    rw [hmem H]
    exact ⟨fun h => h.1, fun h => ⟨h, hr H h⟩⟩
  have hall : ∀ x : Vtx k, x ∈ acc := by
    intro x
    obtain ⟨C, hC, e, he, hrot⟩ := hv.cover x
    rw [inv.mem]
    rcases List.mem_cons.mp hC with h | h
    · rw [h] at he
      exact Or.inl ⟨e, he, hrot⟩
    · exact Or.inr ⟨C, hperm.mem_iff.mpr h, e, he, hrot⟩
  have hne : acc ≠ [] := by
    obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (hv.line_ne K List.mem_cons_self)
    exact List.ne_nil_of_mem (hall e)
  obtain ⟨P, hPdef⟩ : ∃ P : HPath k, P = ⟨acc, hne, inv.nodup⟩ := ⟨_, rfl⟩
  have hPv : P.verts = acc := by rw [hPdef]
  have hPham : P.IsHamiltonian := by
    intro x
    rw [hPv]
    exact hall x
  refine ⟨P, hPham, ?_⟩
  have hwt : P.wtP = lsum (ew k) acc := by
    unfold HPath.wtP
    rw [hPv]
    exact (lsum_eq_zipWith (ew k) acc).symm
  have hlen : acc.length = k.factorial := by
    have h := HPath.numVerts_eq_card_of_hamiltonian hPham
    rw [Hunter.ProofsRecursion.card_Vtx] at h
    unfold HPath.numVerts at h
    rw [hPv] at h
    exact h
  -- sums over the hanging components
  have hw := inv.weight
  have hl := inv.len
  rw [hperm.length_eq, (hperm.map hangW).sum_eq] at hw
  rw [(hperm.map (fun H => H.line.length)).sum_eq] at hl
  have hK := lineWalk_weight hk2 hv (C := K) List.mem_cons_self
  have hKc : K.cost = lineCost K.line := by
    unfold BComp.cost BComp.att
    rw [hKs, attCost_none]
    rfl
  have hsum := sum_hangW hk2 hv Hs (fun H h => ⟨List.mem_cons_of_mem _ h, hHs H h⟩)
  have hbc : bcost (K :: Hs) = K.cost + (Hs.map BComp.cost).sum := by
    unfold bcost
    rw [List.map_cons, List.sum_cons]
  -- the number of blocks is (k-1)!
  obtain ⟨Nb, hNb⟩ : ∃ Nb, Nb = K.line.length + (Hs.map (fun H => H.line.length)).sum :=
    ⟨_, rfl⟩
  rw [← hNb] at hl
  have hfac : k * (k - 1).factorial = k.factorial := Nat.mul_factorial_pred (by omega)
  have hNbf : Nb = (k - 1).factorial := by
    have h1 : k * Nb = k * (k - 1).factorial := by
      rw [← hl, hlen, hfac]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hexp : (k + 1) * Nb = k.factorial + (k - 1).factorial := by
    rw [Nat.add_mul, Nat.one_mul, hNbf, hfac]
  have hexp2 : (k + 1) * Nb = (k + 1) * K.line.length +
      (k + 1) * (Hs.map (fun H => H.line.length)).sum := by
    rw [hNb, Nat.mul_add]
  have hhpv : hpv k + 3 = k.factorial + (k - 1).factorial + (k - 2).factorial + k := by
    unfold hpv
    omega
  rw [hwt, hbc, hKc]
  omega

end SuperpermLowerBounds

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- **Theorems U and S.**  A valid standard configuration is a Hamiltonian path whose defect
`wt(P) + k - HPV(k)` is exactly `cost - (k-2)!`. -/
theorem NConfig.Valid.exists_ham (hk : 3 ≤ k) {c : NConfig k} (hv : c.Valid) :
    ∃ P : HPath k, P.IsHamiltonian ∧ hpv k + c.cost = (k - 2).factorial + (P.wtP + k) := by
  obtain ⟨P, hP, h⟩ := hv.toB_valid.exists_ham hk
  rw [hv.toB_cost (by omega)] at h
  exact ⟨P, hP, h⟩

/-- **The upper direction.**  A valid standard configuration of cost `(k-2)! + D` is a word over
`Fin k` that contains all permutations and has exactly `HPV(k) + D` letters. -/
theorem NConfig.Valid.exists_word (hk : 3 ≤ k) {c : NConfig k} (hv : c.Valid) :
    ∃ w : List (Fin k), SuperpermutationBounds.Covers w ∧
      hpv k + c.cost = (k - 2).factorial + w.length := by
  obtain ⟨P, hP, h⟩ := hv.exists_ham hk
  obtain ⟨hsuper, hlen⟩ := Hunter.ProofsLstar.exists_superperm_of_ham (by omega : 1 ≤ k) hP
  refine ⟨(Hunter.ProofsLstar.wordOf k (P.verts.map Subtype.val)).map
    (SuperpermBridge.down k (by omega)), SuperpermBridge.covers_map_down (by omega) hsuper, ?_⟩
  rw [List.length_map, hlen]
  exact h

/-- **Exactness of the model** (the written model, Corollary "exactness at row level").  No valid
standard configuration has defect at most `D` if and only if every covering word has at least
`HPV(k) + D + 1` letters. -/
theorem no_stdConfig_iff (hk : 5 ≤ k) (D : ℕ) :
    (∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D) ↔
      ∀ w : List (Fin k), SuperpermutationBounds.Covers w → hpv k + D + 1 ≤ w.length := by
  constructor
  · exact covers_length_gt_of_no_stdConfig hk D
  · intro h c hv hc
    obtain ⟨w, hw, hlen⟩ := hv.exists_word (by omega)
    have h1 := h w hw
    omega

/-- The same with Lemma T4: it is enough to look at the configurations without seams of type
T4. -/
theorem no_stdConfig_noT4_iff (hk : 5 ≤ k) (D : ℕ) :
    (∀ c : NConfig k, c.Valid → c.NoT4 → ¬ c.cost ≤ (k - 2).factorial + D) ↔
      ∀ w : List (Fin k), SuperpermutationBounds.Covers w → hpv k + D + 1 ≤ w.length := by
  constructor
  · exact covers_length_gt_of_no_stdConfig_noT4 hk D
  · intro h c hv _ hc
    obtain ⟨w, hw, hlen⟩ := hv.exists_word (by omega)
    have h1 := h w hw
    omega

/-- The defect `cost - (k-2)!` of a valid standard configuration is not negative. -/
theorem NConfig.Valid.factorial_le_cost (hk : 5 ≤ k) {c : NConfig k} (hv : c.Valid) :
    (k - 2).factorial ≤ c.cost := by
  obtain ⟨P, hP, h⟩ := hv.exists_ham (by omega)
  have hb := coverage_bound hk hP
  have h1 : (k - 1) * hpv k ≤ (k - 1) * (P.wtP + k) := by omega
  have h2 : hpv k ≤ P.wtP + k := Nat.le_of_mul_le_mul_left h1 (by omega)
  omega

/-- **`L(k) = HPV(k) + min D`.**  There is a valid standard configuration of least cost, and
its defect `cost - (k-2)!` is exactly `Ssuper k - HPV(k)`, where `Ssuper k` is the length of a
shortest superpermutation. -/
theorem exists_optimal_stdConfig (hk : 5 ≤ k) :
    ∃ c : NConfig k, c.Valid ∧ hpv k + c.cost = (k - 2).factorial + Ssuper k ∧
      ∀ c' : NConfig k, c'.Valid → c.cost ≤ c'.cost := by
  have hk1 : 1 ≤ k := by omega
  have hset : {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty := by
    obtain ⟨P, hP⟩ := Hunter.ProofsSpine.exists_ham k
    exact ⟨P.wtP, P, hP, rfl⟩
  have hmin : L k ∈ {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m} := by
    unfold L
    exact Nat.sInf_mem hset
  obtain ⟨P₀, hP₀, hwt₀⟩ := hmin
  have hL : ∀ P : HPath k, P.IsHamiltonian → L k ≤ P.wtP := by
    intro P hP
    unfold L
    exact Nat.sInf_le ⟨P, hP, rfl⟩
  have hS : Ssuper k = L k + k := (Hunter.bridge_Lstar_eq_Ssuper hk1).symm
  obtain ⟨c, hv, hc⟩ := exists_stdConfig hk hP₀
  obtain ⟨P₁, hP₁, h₁⟩ := hv.exists_ham (by omega)
  have hL₁ := hL P₁ hP₁
  refine ⟨c, hv, by omega, ?_⟩
  intro c' hv'
  obtain ⟨P₂, hP₂, h₂⟩ := hv'.exists_ham (by omega)
  have hL₂ := hL P₂ hP₂
  omega

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.NConfig.Valid.factorial_le_cost
#print axioms SuperpermLowerBounds.exists_optimal_stdConfig
#print axioms SuperpermLowerBounds.BValid.exists_ham
#print axioms SuperpermLowerBounds.NConfig.Valid.exists_ham
#print axioms SuperpermLowerBounds.NConfig.Valid.exists_word
#print axioms SuperpermLowerBounds.no_stdConfig_iff
#print axioms SuperpermLowerBounds.no_stdConfig_noT4_iff

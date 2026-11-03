import LowerBounds.PArith
import LowerBounds.PTrails

/-!
# Families of trails: Lemma FF and the bound on the number of trails
(the written proof, section 5)

For a list of trails `S` on 7 symbols, `prs S` is the list of the pairs `(holes, rows)` of its
trails, so that `T5899.lE (prs S) = Σ (rows - holes - 5)` and `T5899.lW (prs S) = Σ (holes + 6)`.

* `family_le_49` (Lemma FF): a family of trails of weight at most 84 has value at most 49, given
  the chain caps and the five profile statements.
* `family_le_44`: a family of at least 7 trails of weight at most 90 has value at most 44.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain T5899

/-- The pairs `(holes, rows)` of a list of trails. -/
def prs (S : List (List (NRow 7))) : List (ℕ × ℕ) := S.map fun A => (rowsHoles 7 A, A.length)

theorem prs_nil : prs [] = [] := rfl

theorem prs_cons (A : List (NRow 7)) (S : List (List (NRow 7))) :
    prs (A :: S) = (rowsHoles 7 A, A.length) :: prs S := rfl

theorem prs_append (S S' : List (List (NRow 7))) : prs (S ++ S') = prs S ++ prs S' := by
  unfold prs
  rw [List.map_append]

theorem lW_append (l l' : List (ℕ × ℕ)) : lW (l ++ l') = lW l + lW l' := by
  unfold lW
  rw [List.map_append, List.sum_append]

theorem lE_append (l l' : List (ℕ × ℕ)) : lE (l ++ l') = lE l + lE l' := by
  unfold lE
  rw [List.map_append, List.sum_append]

/-- The weight of a list of trails, from its rows. -/
theorem lW_prs : ∀ S : List (List (NRow 7)),
    lW (prs S) = rowsHoles 7 S.flatten + 6 * S.length
  | [] => by simp [prs, lW, rowsHoles]
  | A :: S => by
      rw [prs_cons, lW_cons, lW_prs S, List.flatten_cons, rowsHoles_append, List.length_cons]
      simp only
      omega

/-- The value of a list of trails, from its rows. -/
theorem lE_prs : ∀ S : List (List (NRow 7)),
    lE (prs S) = (S.flatten.length : ℤ) - (rowsHoles 7 S.flatten : ℤ) - 5 * (S.length : ℤ)
  | [] => by simp [prs, lE, rowsHoles]
  | A :: S => by
      rw [prs_cons, lE_cons, lE_prs S, List.flatten_cons, rowsHoles_append, List.length_append,
        List.length_cons]
      push_cast
      ring

theorem mem_le_lW {l : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ l) : p.1 + 6 ≤ lW l := by
  rw [lW_erase hp]
  omega

theorem rowsEntries_sublist {R R' : List (NRow 7)} (h : R.Sublist R') :
    (rowsEntries R).Sublist (rowsEntries R') := by
  rw [← rowsEntries_eq, ← rowsEntries_eq]
  exact (h.map NRow.entries).flatten

theorem rowsEntries_perm {R R' : List (NRow 7)} (h : R.Perm R') :
    (rowsEntries R).Perm (rowsEntries R') := by
  unfold rowsEntries
  exact h.flatMap_right _

/-- A family of trails stays a family when trails are dropped and reordered. -/
theorem TrailFam.of_subperm {S S' : List (List (NRow 7))} (h : TrailFam 7 S)
    (hs : S'.Subperm S) : TrailFam 7 S' := by
  obtain ⟨l, hl, hsub⟩ := hs
  refine ⟨fun A hA => h.trails A (hsub.subset (hl.symm.subset hA)), ?_⟩
  have h1 : (rowsEntries S'.flatten).Perm (rowsEntries l.flatten) :=
    rowsEntries_perm hl.symm.flatten
  have h2 : (rowsEntries l.flatten).Sublist (rowsEntries S.flatten) :=
    rowsEntries_sublist hsub.flatten
  exact pairwise_of_perm (h.classes.sublist h2) h1

theorem TrailFam.pairs_ok {M : ℕ → ℕ} (h0 : ChainCap M 84) {S : List (List (NRow 7))}
    (h : TrailFam 7 S) (hW : lW (prs S) ≤ 90) :
    (∀ p ∈ prs S, p.2 ≤ M p.1) ∧ ∀ p ∈ prs S, p.1 ≤ 84 := by
  have hx : ∀ p ∈ prs S, p.1 ≤ 84 := by
    intro p hp
    have := mem_le_lW hp
    omega
  refine ⟨?_, hx⟩
  intro p hp
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hp
  exact chain_cap_rows h0 (h.trails A hA) (h.classes.sublist (rowsEntries_sublist_flatten hA))
    (hx _ hp)

/-- The trails of a family are pairwise different lists. -/
theorem TrailFam.nodup {S : List (List (NRow 7))} (h : TrailFam 7 S) : S.Nodup := by
  have hcl := h.classes
  have htr := h.trails
  clear h
  induction S with
  | nil => exact List.nodup_nil
  | cons A S ih =>
      rw [List.flatten_cons, rowsEntries_append, List.pairwise_append] at hcl
      rw [List.nodup_cons]
      refine ⟨?_, ih hcl.2.1 (fun B hB => htr B (List.mem_cons_of_mem _ hB))⟩
      intro hA
      have hT := htr A List.mem_cons_self
      obtain ⟨r, rest, hr⟩ := List.exists_cons_of_ne_nil hT.ne
      have hmem : r.entry ∈ rowsEntries A := by
        rw [hr, rowsEntries_cons]
        exact List.mem_append_left _ (NRow.entry_mem r (hT.len r (by rw [hr]; simp)))
      have hmem' : r.entry ∈ rowsEntries S.flatten :=
        (rowsEntries_sublist_flatten hA).subset hmem
      exact hcl.2.2 _ hmem _ hmem' (List.IsRotated.refl _)

theorem exists_of_count_one {α β : Type*} [BEq β] [LawfulBEq β] (f : α → β) (b : β) {S : List α}
    (h : 1 ≤ (S.map f).count b) : ∃ A ∈ S, f A = b := by
  have hm : b ∈ S.map f := List.count_pos_iff.mp h
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hm
  exact ⟨A, hA, rfl⟩

theorem exists_of_count_two {α β : Type*} [BEq β] [LawfulBEq β] (f : α → β) (b : β) :
    ∀ {S : List α}, S.Nodup → 2 ≤ (S.map f).count b →
      ∃ A B, A ∈ S ∧ B ∈ S ∧ A ≠ B ∧ f A = b ∧ f B = b
  | [], _, h => by simp at h
  | A :: S, hn, h => by
      rw [List.nodup_cons] at hn
      by_cases hA : f A = b
      · have h1 : 1 ≤ (S.map f).count b := by
          rw [List.map_cons, hA, List.count_cons_self] at h
          omega
        obtain ⟨B, hB, hfB⟩ := exists_of_count_one f b h1
        exact ⟨A, B, List.mem_cons_self, List.mem_cons_of_mem _ hB,
          fun e => hn.1 (e ▸ hB), hA, hfB⟩
      · rw [List.map_cons, List.count_cons_of_ne hA] at h
        obtain ⟨A', B, hA', hB, hne, h1, h2⟩ := exists_of_count_two f b hn.2 h
        exact ⟨A', B, List.mem_cons_of_mem _ hA', List.mem_cons_of_mem _ hB, hne, h1, h2⟩

/-- The five profile statements. -/
structure Profiles : Prop where
  p36 : NoProfile [(66, 36), (66, 36)]
  p26 : NoProfile [(50, 26), (50, 26)]
  p34 : NoProfile [(63, 34), (34, 16)]
  p14 : NoProfile [(66, 36), (31, 14)]
  p4 : NoProfile [(31, 14), (31, 14), (34, 16), (34, 16)]

/-- **Lemma FF.**  A family of trails of weight at most 84 has value at most 49. -/
theorem family_le_49 (h0 : ChainCap Mf 84) (hF : Profiles) {S : List (List (NRow 7))}
    (h : TrailFam 7 S) (hW : lW (prs S) ≤ 84) : lE (prs S) ≤ 49 := by
  by_contra hcon
  have hE : 50 ≤ lE (prs S) := by omega
  have hok := (h.pairs_ok h0 (by omega)).1
  have hnd := h.nodup
  have key := profile_of_family hok hW hE
  -- a pair of trails
  have pair : ∀ {A B : List (NRow 7)}, A ∈ S → B ∈ S → A ≠ B → TrailFam 7 [A, B] := by
    intro A B hA hB hne
    refine h.of_subperm (List.Nodup.subperm ?_ ?_)
    · simp [hne]
    · intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
  unfold prs at key
  rcases key with k1 | k1 | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    simp only [Prod.mk.injEq] at fA fB
    refine noProfile_rows hF.p36 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    simp only [Prod.mk.injEq] at fA fB
    refine noProfile_rows hF.p26 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, hA, fA⟩ := exists_of_count_one _ _ k1
    obtain ⟨B, hB, fB⟩ := exists_of_count_one _ _ k2
    simp only [Prod.mk.injEq] at fA fB
    have hne : A ≠ B := by
      rintro rfl
      omega
    refine noProfile_rows hF.p34 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, hA, fA⟩ := exists_of_count_one _ _ k1
    obtain ⟨B, hB, fB⟩ := exists_of_count_one _ _ k2
    simp only [Prod.mk.injEq] at fA fB
    have hne : A ≠ B := by
      rintro rfl
      omega
    refine noProfile_rows hF.p14 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    obtain ⟨C, D, hC, hD, hne', fC, fD⟩ := exists_of_count_two _ _ hnd k2
    simp only [Prod.mk.injEq] at fA fB fC fD
    have hfam : TrailFam 7 [A, B, C, D] := by
      refine h.of_subperm (List.Nodup.subperm ?_ ?_)
      · have h1 : A ≠ C := by rintro rfl; omega
        have h2 : A ≠ D := by rintro rfl; omega
        have h3 : B ≠ C := by rintro rfl; omega
        have h4 : B ≠ D := by rintro rfl; omega
        simp [hne, hne', h1, h2, h3, h4]
      · intro X hX
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
        rcases hX with rfl | rfl | rfl | rfl
        · exact hA
        · exact hB
        · exact hC
        · exact hD
    refine noProfile_rows hF.p4 hfam ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩
        (.cons ⟨by simp only; omega, by simp only; omega⟩
          (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)))

/-- A family of at least 7 trails of weight at most 90 has value at most 44. -/
theorem family_le_44 (h0 : ChainCap Mf 84) {S : List (List (NRow 7))} (h : TrailFam 7 S)
    (hW : lW (prs S) ≤ 90) (h7 : 7 ≤ S.length) : lE (prs S) ≤ 44 := by
  obtain ⟨hok, hx⟩ := h.pairs_ok h0 hW
  exact many_chains hok hx hW (by unfold prs; rw [List.length_map]; exact h7)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.family_le_49
#print axioms SuperpermLowerBounds.family_le_44

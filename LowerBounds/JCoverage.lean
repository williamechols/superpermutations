import LowerBounds.JEntryTree
import LowerBounds.TheoremBCore
import LowerBounds.LemmaZC

/-!
# Theorem J1: coverage and the budget

the written proofs of the joint conditions, section 2.  Not the whole of J1 is here: the link graph on
rows and its trails are not defined in Lean.  What is proved:

* (a) on the level of blocks: `exists_block` (every vertex lies in the rotation class of the
  entry of a block of its component), `block_unique` (two block entries in one rotation class
  are the same block of the same component), `not_isRotated_of_ne` (vertices of different
  components are in different rotation classes).  Inside a piece the entries are `e, τ₂ e, …`
  by `pieceEntries_eq_iterate` (`SBridgeChain.lean`).
* (c): `free_junction_shape` (a junction of cost 0 in a `σ²`-reduced path has one slot, which is
  `σ⁻¹ τ (head B)`, and `tail A = ψ (head B)`), `free_junction_rows` (it is a loop of one row, or
  the two rows have deficits at least 2 with sum at least `k`).  Both are Liu's dichotomy and
  `lemma_ZC` with the hypothesis written as `junctionCost = 0`.
* (e) as a count of components: `card_components_eq` (the number of components is the number
  of free junctions plus the number of paid junctions plus one); and the matching behind "one
  path and cycles": `existsUnique_target` (every component but the root is the target of exactly
  one junction), `existsUnique_not_source` (exactly one component is not the source of a
  junction).
* (f): `budget`, for every Hamiltonian path and `k ≥ 5`:
  `(k-1)·(wt P + k) ≥ (k-1)·HPV(k) + δ + (k-1)·(x + Σ_s c(s) + I)`, that is
  `D ≥ δ/(k-1) + x + Σ_s c(s) + I` with the exact junction costs; and `coverage_bound`, the same
  with `x` replaced by the number of seams of weight at least 4 and `Σ_s c(s)` by the number of
  paid junctions.  Reducedness is not used.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

section Path

variable {P : HPath k}

/-! ### (a) Blocks and rotation classes -/

/-- Vertices of different components are in different rotation classes. -/
theorem not_isRotated_of_ne (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C D : ActualComponent P}
    (hne : C ≠ D) {u v : Vtx k} (hu : u ∈ C.1) (hv : v ∈ D.1) :
    ¬ ((u : List ℕ) ~r (v : List ℕ)) := by
  intro h
  apply hne
  have hvC : v ∈ C.1 := cyc_subset_component hP hk C hu
    (Hunter.ProofsExitless.mem_cyc.mpr (rotClass_eq_iff.mpr h.symm))
  rw [← compOf_eq_of_mem hP hk hvC, compOf_eq_of_mem hP hk hv]

/-- The entry of a block of a component is a vertex of the component. -/
theorem blockEntry_mem (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) {i : ℕ}
    (hi : i < componentClassCount (actualComponentPath hP C)) :
    blockEntry (actualComponentPath hP C) i ∈ C.1 := by
  have hp := actualComponentPath_stronglyExitless hP hk C
  have hN := component_numVerts_eq (by omega : 1 ≤ k) hp
  have hlt : k * i < (actualComponentPath hP C).numVerts := by
    rw [hN]
    exact Nat.mul_lt_mul_of_pos_left hi (by omega)
  rw [← actualComponentPath_vertsFinset hP C, HPath.mem_vertsFinset]
  unfold blockEntry
  rw [Hunter.ProofsExitless.vert_getElem _ hlt]
  exact List.getElem_mem _

/-- **J1 (a), existence.**  Every vertex lies in the rotation class of the entry of a block of
its component. -/
theorem exists_block (hP : P.IsHamiltonian) (hk : 2 ≤ k) (v : Vtx k) :
    ∃ j, j < componentClassCount (actualComponentPath hP (compOf hP hk v)) ∧
      v ∈ cyc (blockEntry (actualComponentPath hP (compOf hP hk v)) j) := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = actualComponentPath hP (compOf hP hk v) := ⟨_, rfl⟩
  rw [← hpdef]
  have hp : p.StronglyExitless := by
    rw [hpdef]
    exact actualComponentPath_stronglyExitless hP hk _
  have hv : v ∈ p.verts := by
    rw [← HPath.mem_vertsFinset, hpdef, actualComponentPath_vertsFinset hP]
    exact mem_compOf hP hk v
  have hk1 : 1 ≤ k := by omega
  have hN := component_numVerts_eq hk1 hp
  have hi : p.pos v < p.numVerts := List.idxOf_lt_length_of_mem hv
  have hdm := Nat.div_add_mod (p.pos v) k
  have hr : p.pos v % k < k := Nat.mod_lt _ (by omega)
  refine ⟨p.pos v / k, ?_, ?_⟩
  · rw [hN] at hi
    exact Nat.div_lt_of_lt_mul hi
  · rw [Hunter.ProofsExitless.mem_cyc_iff_exists hk1]
    refine ⟨p.pos v % k, hr, ?_⟩
    have hb := block_vert hk1 hp.1 (j := p.pos v / k) (r := p.pos v % k) hr
      (by rw [hdm]; exact hi)
    rw [hdm, Hunter.ProofsExitless.vert_pos p hv] at hb
    exact hb

/-- **J1 (a), uniqueness.**  Two block entries in the same rotation class are the same block of
the same component. -/
theorem block_unique (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C D : ActualComponent P} {i j : ℕ}
    (hi : i < componentClassCount (actualComponentPath hP C))
    (hj : j < componentClassCount (actualComponentPath hP D))
    (h : (blockEntry (actualComponentPath hP C) i : List ℕ) ~r
      (blockEntry (actualComponentPath hP D) j : List ℕ)) :
    C = D ∧ i = j := by
  have hk1 : 1 ≤ k := by omega
  have hCD : C = D := by
    by_contra hne
    exact not_isRotated_of_ne hP hk hne (blockEntry_mem hP hk C hi) (blockEntry_mem hP hk D hj) h
  subst hCD
  refine ⟨rfl, ?_⟩
  by_contra hij
  have hp := actualComponentPath_stronglyExitless hP hk C
  have hN := component_numVerts_eq hk1 hp
  exact blockEntry_not_isRotated hk1 hp.1
    (by rw [hN]; exact Nat.mul_lt_mul_of_pos_left hi (by omega))
    (by rw [hN]; exact Nat.mul_lt_mul_of_pos_left hj (by omega)) hij h

/-! ### (c) Free junctions -/

/-- **J1 (c), first part.**  A junction of cost 0 of a `σ²`-reduced path has a single slot
`σ⁻¹ τ (head B)`, and the tail of its target is `ψ (head B)`. -/
theorem free_junction_shape (hk : 2 ≤ k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last)
    (h0 : junctionCost hP s hs = 0) :
    actualChainRoute s = [s.1] ∧
      s.1 = sigmaInv (tau (actualComponentHead hP (actualChainSourceComponent hP hk s))) ∧
      actualComponentTail hP (actualNonterminalTargetComponent hP hk (ntEnd s hs)) =
        psi (actualComponentHead hP (actualChainSourceComponent hP hk s)) := by
  obtain ⟨hz, hmu⟩ := (junctionCost_eq_zero_iff hk hP s hs).mp h0
  have hd := actual_reduced_zero_cost_dichotomy hP hk hred s hs hz hmu
  rw [actualChainSourceComponent_head hP hk s, actualNonterminalTargetComponent_tail hP hk]
  exact ⟨actualChainRoute_eq_singleton_of_routeNatCost_zero hP hk s hz, hd.1, hd.2⟩

/-- **J1 (c), second part.**  A junction of cost 0 of a `σ²`-reduced path, `k ≥ 5`: either the
target is the source and it is a single row, or the last row of the source has deficit
`d ≥ 2`, the first row of the target has deficit `d' ≥ 2`, and `d + d' ≥ k`. -/
theorem free_junction_rows (hk : 5 ≤ k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last)
    (h0 : junctionCost hP s hs = 0) :
    (actualNonterminalTargetComponent hP (by omega) (ntEnd s hs) =
        actualChainSourceComponent hP (by omega) s ∧
      componentPieceCount
          (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) = 1) ∨
    (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces
            (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega)
              (actualChainSourceComponent hP (by omega) s))) ∧
      2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces
            (actualComponentPath hP (actualNonterminalTargetComponent hP (by omega)
              (ntEnd s hs))) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega)
              (actualNonterminalTargetComponent hP (by omega) (ntEnd s hs)))) ∧
      k ≤ lastNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) (by omega)
              (actualComponentPath_stronglyExitless hP (by omega)
                (actualChainSourceComponent hP (by omega) s))) +
          firstNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualNonterminalTargetComponent hP (by omega)
                (ntEnd s hs))) (by omega)
              (actualComponentPath_stronglyExitless hP (by omega)
                (actualNonterminalTargetComponent hP (by omega) (ntEnd s hs))))) := by
  obtain ⟨hz, hmu⟩ := (junctionCost_eq_zero_iff (by omega) hP s hs).mp h0
  exact lemma_ZC hk hP hred s hs hz hmu

/-! ### (e), (f) Counting and the budget -/

/-- The junction cost of a chain, with the value 0 for the chain that ends at `P.last`. -/
noncomputable def junctionCostT (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ℕ :=
  if hs : actualChainRouteEnd s ≠ P.last then junctionCost hP s hs else 0

theorem junctionCostT_of_ne (hP : P.IsHamiltonian) (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) : junctionCostT hP s = junctionCost hP s hs := by
  unfold junctionCostT
  rw [dif_pos hs]

/-- The paid junctions: the chains with a junction cost other than 0. -/
noncomputable def paidJunctions (hP : P.IsHamiltonian) :
    Finset {v : Vtx k // v ∈ chainStarts P} :=
  Finset.univ.filter (fun s => junctionCostT hP s ≠ 0)

/-- The free junctions: the chains that do not end at `P.last` and have junction cost 0. -/
noncomputable def freeJunctions (hP : P.IsHamiltonian) :
    Finset {v : Vtx k // v ∈ chainStarts P} :=
  (nonterminal P).filter (fun s => junctionCostT hP s = 0)

theorem paidJunctions_subset (hP : P.IsHamiltonian) : paidJunctions hP ⊆ nonterminal P := by
  intro s hs
  rw [mem_nonterminal]
  intro hend
  have h := (Finset.mem_filter.mp hs).2
  apply h
  unfold junctionCostT
  rw [dif_neg (not_not.mpr hend)]

/-- There are exactly `c - 1` chains that do not end at `P.last`. -/
theorem card_nonterminal_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    (nonterminal P).card + 1 = Fintype.card (ActualComponent P) := by
  have himg := image_tgt_nonterminal hk hP
  have h1 : ((nonterminal P).image (tgt hk hP)).card = (nonterminal P).card :=
    Finset.card_image_of_injOn (fun a ha b hb h => tgt_inj_nonterminal hk hP a ha b hb h)
  rw [himg, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h1
  have hpos : 0 < Fintype.card (ActualComponent P) :=
    Fintype.card_pos_iff.mpr ⟨actualRootComponent hP (by omega)⟩
  omega

/-- **J1 (e) as a count of components**: one component (the root) is not a target, every other
component is the target of exactly one junction, free or paid. -/
theorem card_components_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    Fintype.card (ActualComponent P) =
      (freeJunctions hP).card + (paidJunctions hP).card + 1 := by
  have hcard := card_nonterminal_eq hk hP
  have hsplit : (freeJunctions hP).card + (paidJunctions hP).card = (nonterminal P).card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := nonterminal P)
      (fun s => junctionCostT hP s = 0)
    have h2 : (nonterminal P).filter (fun s => ¬ junctionCostT hP s = 0) = paidJunctions hP := by
      ext s
      constructor
      · intro hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩
      · intro hs
        exact Finset.mem_filter.mpr ⟨paidJunctions_subset hP hs, (Finset.mem_filter.mp hs).2⟩
    rw [h2] at h1
    exact h1
  omega

/-- **Every component other than the root is the target of exactly one junction.** -/
theorem existsUnique_target (hk : 5 ≤ k) (hP : P.IsHamiltonian) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP (by omega)) :
    ∃! s, s ∈ nonterminal P ∧ tgt hk hP s = C := by
  have hmem : C ∈ (nonterminal P).image (tgt hk hP) := by
    rw [image_tgt_nonterminal hk hP]
    exact Finset.mem_erase.mpr ⟨hC, Finset.mem_univ _⟩
  obtain ⟨s, hs, hsC⟩ := Finset.mem_image.mp hmem
  refine ⟨s, ⟨hs, hsC⟩, ?_⟩
  rintro s' ⟨hs', hs'C⟩
  exact tgt_inj_nonterminal hk hP s' hs' s hs (hs'C.trans hsC.symm)

/-- **Exactly one component is not the source of a junction.**  With `existsUnique_target`: the
junctions are a bijection from the components other than this one to the components other
than the root, so they arrange the components into one path, from the root to this
component, and cycles. -/
theorem existsUnique_not_source (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∃! C : ActualComponent P,
      ∀ s ∈ nonterminal P, actualChainSourceComponent hP (by omega) s ≠ C := by
  have hinj := actualChainSourceComponent_injective hP (by omega : 2 ≤ k)
  have hcard := card_nonterminal_eq hk hP
  obtain ⟨I, hI⟩ : ∃ I : Finset (ActualComponent P),
      I = (nonterminal P).image (actualChainSourceComponent hP (by omega : 2 ≤ k)) := ⟨_, rfl⟩
  have hIc : I.card = (nonterminal P).card := by
    rw [hI]
    exact Finset.card_image_of_injective _ hinj
  have hsplit : (Finset.univ \ I).card + I.card = Fintype.card (ActualComponent P) := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
  have hone : (Finset.univ \ I).card = 1 := by omega
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp hone
  refine ⟨C, ?_, ?_⟩
  · intro s hs heq
    have hmem : C ∈ Finset.univ \ I := by
      rw [hC]
      exact Finset.mem_singleton_self C
    apply (Finset.mem_sdiff.mp hmem).2
    rw [hI, ← heq]
    exact Finset.mem_image_of_mem _ hs
  · intro D hD
    have hmem : D ∈ Finset.univ \ I := by
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hDI => ?_⟩
      rw [hI] at hDI
      obtain ⟨s, hs, hsD⟩ := Finset.mem_image.mp hDI
      exact hD s hs hsD
    rw [hC] at hmem
    exact Finset.mem_singleton.mp hmem

theorem card_paid_le (hP : P.IsHamiltonian) :
    (paidJunctions hP).card ≤ ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s := by
  unfold paidJunctions
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro s _
  split_ifs with h <;> omega

/-- The number of seams of weight at least 4 is at most the seam residual. -/
theorem card_positiveSeams_le (p : HPath k) :
    (componentPositiveSeams p).card ≤ componentSeamResidual p := by
  unfold componentPositiveSeams componentSeamResidual
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h <;> omega

/-- `c(s) ≤ g(s) + (μ - 2)` of the target, in the notation of Theorem A. -/
theorem junctionCostT_le (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    junctionCostT hP s ≤ actualChainRouteNatCost hP (by omega) s + gap hk hP (tgt hk hP s) := by
  by_cases hs : actualChainRouteEnd s ≠ P.last
  · rw [junctionCostT_of_ne hP s hs, junctionCost_eq (by omega) hP s hs]
    have htgt : tgt hk hP s = actualNonterminalTargetComponent hP (by omega) (ntEnd s hs) := by
      unfold tgt
      rw [dif_pos hs]
      rfl
    have hnr : tgt hk hP s ≠ actualRootComponent hP (by omega) := by
      rw [htgt]
      exact target_ne_root hP (by omega) _
    have hgap : gap hk hP (tgt hk hP s) = compMinto (F P) (tgt hk hP s).1 - 2 := by
      unfold gap
      rw [if_neg hnr]
    rw [hgap, htgt]
  · unfold junctionCostT
    rw [dif_neg hs]
    exact Nat.zero_le _

theorem sum_junctionCostT_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s ≤
      actualChainCostSumCore hP (by omega) + ∑ C : ActualComponent P, gap hk hP C := by
  have h1 := Finset.sum_le_sum
    (fun (s : {v : Vtx k // v ∈ chainStarts P}) (_ : s ∈ Finset.univ) =>
      junctionCostT_le hk hP s)
  rw [Finset.sum_add_distrib] at h1
  have h2 := sum_gap_tgt_le hk hP
  have h3 : actualChainCostSumCore hP (by omega : 2 ≤ k) =
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteNatCost hP (by omega) s := rfl
  omega

set_option maxHeartbeats 1600000 in
/-- **The budget (J1 (f) with exact costs).**  For every Hamiltonian path and `k ≥ 5`:
`(k-1)·(wt P + k) ≥ (k-1)·HPV(k) + δ + (k-1)·(x + Σ_s c(s) + I)`, with `δ` the holes, `x` the
seam residual, `c(s)` the junction costs and `I` the indicator of `P.last ∈ S(P)`. -/
theorem budget (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    (k - 1) * hpv k +
        ∑ C : ActualComponent P, componentPieceDeficit (actualComponentPath hP C) +
        (k - 1) * (∑ C : ActualComponent P, componentSeamResidual (actualComponentPath hP C) +
          ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s +
          indicatorI P (Sset P)) ≤
      (k - 1) * (P.wtP + k) := by
  have hk2 : 2 ≤ k := by omega
  have hw : ∀ C : ActualComponent P, (actualGeom hP C).WeightEquations k :=
    fun C => actualComponentGeometry_weightEquations hP (by omega) C
  have hsumT : ∑ C : ActualComponent P, (actualGeom hP C).t = ((k - 1).factorial : ℤ) :=
    sum_actual_component_t hP hk2
  have hsumP : ∑ C : ActualComponent P, (actualGeom hP C).pValue =
      (actualBaseline P : ℤ) + 1 + (actualMu (distinguishedComponent hP hk2) : ℤ) :=
    sum_actual_component_pValue hP hk2
  obtain ⟨Rz, hRz⟩ : ∃ Rz : ℤ, Rz = ∑ C : ActualComponent P, (actualGeom hP C).r := ⟨_, rfl⟩
  obtain ⟨Xz, hXz⟩ : ∃ Xz : ℤ, Xz = ∑ C : ActualComponent P, (actualGeom hP C).x := ⟨_, rfl⟩
  obtain ⟨Dz, hDz⟩ : ∃ Dz : ℤ, Dz = ∑ C : ActualComponent P, (actualGeom hP C).Delta :=
    ⟨_, rfl⟩
  obtain ⟨Gz, hGz⟩ : ∃ Gz : ℤ, Gz = ∑ C : ActualComponent P, ((actualGeom hP C).mu - 2) :=
    ⟨_, rfl⟩
  obtain ⟨gs, hgs⟩ : ∃ gs : ℤ, gs = ∑ C : ActualComponent P, (gap hk hP C : ℤ) := ⟨_, rfl⟩
  -- the weight equations, summed
  have hF1 : ((k - 1).factorial : ℤ) = ((k : ℤ) - 1) * Rz - Dz := by
    rw [← hsumT, hRz, hDz, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _ => (hw C).1)
  have hF2 : (actualBaseline P : ℤ) + 1 + (actualMu (distinguishedComponent hP hk2) : ℤ) =
      ((k : ℤ) + 1) * ((k - 1).factorial : ℤ) + Rz + Xz + Gz := by
    rw [← hsumP, ← hsumT, hRz, hXz, hGz, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    rw [(hw C).2]
    ring
  -- minimum entry weights
  have hmu : ∀ C : ActualComponent P, (actualGeom hP C).mu = (compMinto (F P) C.1 : ℤ) := by
    intro C
    show ((actualComponentPath hP C).minto : ℤ) = _
    rw [actualComponentPath_minto hP C]
  have hterm : ∀ C : ActualComponent P, (actualGeom hP C).mu - 2 = (gap hk hP C : ℤ) +
      (if C = actualRootComponent hP hk2 then
        (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2 else 0) := by
    intro C
    rw [hmu C]
    by_cases hC : C = actualRootComponent hP hk2
    · have hg : gap hk hP C = 0 := by
        unfold gap
        rw [if_pos hC]
      rw [if_pos hC, hg, hC]
      simp
    · have h2 := two_le_minto_of_ne_root hk hP hC
      have hg : gap hk hP C = compMinto (F P) C.1 - 2 := by
        unfold gap
        rw [if_neg hC]
      rw [if_neg hC, hg, Nat.cast_sub h2]
      simp
  have hGap : Gz = gs + ((compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2) := by
    rw [hGz, hgs, Finset.sum_congr rfl (fun C _ => hterm C), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (actualRootComponent hP hk2)
        (fun _ => (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2)]
    simp
  -- the budget of Liu's identity
  have hroot_le := actualMu_le_distinguished hP hk2 (actualRootComponent hP hk2)
  have hmur : (actualMu (actualRootComponent hP hk2) : ℤ) =
      (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) := rfl
  have hbud : (actualBaseline P : ℤ) + ((actualMu (distinguishedComponent hP hk2) : ℤ) -
      (actualMu (actualRootComponent hP hk2) : ℤ)) + (actualTerminalIndicatorCore P : ℤ) +
      (actualChainCostSumCore hP hk2 : ℤ) ≤ (P.wtP : ℤ) := by
    have h := actualBaseline_add_actualPathPaymentCore_le hP hk2
    unfold actualPathPaymentCore actualRootGap at h
    have h' : ((actualBaseline P + (actualMu (distinguishedComponent hP hk2) -
        actualMu (actualRootComponent hP hk2) + actualTerminalIndicatorCore P +
        actualChainCostSumCore hP hk2) : ℕ) : ℤ) ≤ (P.wtP : ℤ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hroot_le] at h'
    linarith
  -- factorials
  have hf1 : ((k - 1).factorial : ℤ) = ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by
    have h := Nat.mul_factorial_pred (n := k - 1) (by omega)
    rw [show k - 1 - 1 = k - 2 by omega] at h
    rw [← h]
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  have hf0 : (k.factorial : ℤ) = (k : ℤ) * ((k - 1).factorial : ℤ) := by
    have h := Nat.mul_factorial_pred (n := k) (by omega)
    rw [← h]
    push_cast
    ring
  have hH : (hpv k : ℤ) = (k : ℤ) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) +
      ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) + ((k - 2).factorial : ℤ) + (k : ℤ) - 3 := by
    have h : hpv k + 3 = k.factorial + (k - 1).factorial + (k - 2).factorial + k := by
      unfold hpv
      omega
    have h' : ((hpv k + 3 : ℕ) : ℤ) =
        ((k.factorial + (k - 1).factorial + (k - 2).factorial + k : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    rw [hf0, hf1] at h'
    linarith
  -- the junction costs
  obtain ⟨Jz, hJz⟩ : ∃ Jz : ℤ,
      Jz = ∑ s : {v : Vtx k // v ∈ chainStarts P}, ((junctionCostT hP s : ℕ) : ℤ) := ⟨_, rfl⟩
  have hJ : Jz ≤ (actualChainCostSumCore hP hk2 : ℤ) + gs := by
    rw [hJz, hgs]
    exact_mod_cast sum_junctionCostT_le hk hP
  -- arithmetic
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [hf1] at hF1 hF2
  rw [hGap] at hF2
  have hDz' : Dz = ((k : ℤ) - 1) * Rz - ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by linarith
  have hA : ((k : ℤ) + 1) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) + Rz + Xz + gs - 3 +
      (actualTerminalIndicatorCore P : ℤ) + (actualChainCostSumCore hP hk2 : ℤ) ≤
      (P.wtP : ℤ) := by
    rw [hmur] at hbud
    linarith
  have hDcast : ∑ C : ActualComponent P,
      ((componentPieceDeficit (actualComponentPath hP C) : ℕ) : ℤ) = Dz := by
    rw [hDz]
    exact Finset.sum_congr rfl (fun C _ => rfl)
  have hXcast : ∑ C : ActualComponent P,
      ((componentSeamResidual (actualComponentPath hP C) : ℕ) : ℤ) = Xz := by
    rw [hXz]
    exact Finset.sum_congr rfl (fun C _ => rfl)
  have hZ : ((k : ℤ) - 1) * (hpv k : ℤ) + Dz +
      ((k : ℤ) - 1) * (Xz + Jz + (actualTerminalIndicatorCore P : ℤ)) ≤
      ((k : ℤ) - 1) * ((P.wtP : ℤ) + (k : ℤ)) := by
    rw [hH, hDz']
    have hK1 : (0 : ℤ) ≤ (k : ℤ) - 1 := by linarith
    linarith [mul_nonneg hK1 (sub_nonneg.mpr hA), mul_nonneg hK1 (sub_nonneg.mpr hJ)]
  have h1 : 1 ≤ k := by omega
  zify [h1]
  rw [hDcast, hXcast, ← hJz]
  exact hZ

/-- **J1 (f).**  `D ≥ δ/(k-1) + x⁺ + J⁺`, with `x⁺` the number of seams of weight at least 4
and `J⁺` the number of paid junctions, for every Hamiltonian path and `k ≥ 5`. -/
theorem coverage_bound (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    (k - 1) * hpv k +
        ∑ C : ActualComponent P, componentPieceDeficit (actualComponentPath hP C) +
        (k - 1) * (∑ C : ActualComponent P,
            (componentPositiveSeams (actualComponentPath hP C)).card +
          (paidJunctions hP).card) ≤
      (k - 1) * (P.wtP + k) := by
  have hb := budget hk hP
  have h1 : ∑ C : ActualComponent P, (componentPositiveSeams (actualComponentPath hP C)).card ≤
      ∑ C : ActualComponent P, componentSeamResidual (actualComponentPath hP C) :=
    Finset.sum_le_sum (fun C _ => card_positiveSeams_le _)
  have h2 := card_paid_le hP
  have h3 : (k - 1) * (∑ C : ActualComponent P,
        (componentPositiveSeams (actualComponentPath hP C)).card + (paidJunctions hP).card) ≤
      (k - 1) * (∑ C : ActualComponent P, componentSeamResidual (actualComponentPath hP C) +
        ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s + indicatorI P (Sset P)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end Path

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.exists_block
#print axioms SuperpermLowerBounds.block_unique
#print axioms SuperpermLowerBounds.free_junction_shape
#print axioms SuperpermLowerBounds.free_junction_rows
#print axioms SuperpermLowerBounds.card_components_eq
#print axioms SuperpermLowerBounds.existsUnique_target
#print axioms SuperpermLowerBounds.existsUnique_not_source
#print axioms SuperpermLowerBounds.budget
#print axioms SuperpermLowerBounds.coverage_bound

import Hunter.ProofsGB2
import PreimageChain.PathwiseDistinguishedCore
import PreimageChain.PathwiseLayerBudgetArithmetic
import PreimageChain.DistinguishedSumAlgebra

/-!
# Actual-component bookkeeping for the pathwise layer

This module proves the real component-sum identities needed for equation (29), using only the
actual Hunter component API.  In particular it does not rely on the earlier placeholder names
for component sums.
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- The actual components partition all `k!` vertices. -/
theorem sum_actual_component_cards
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P, C.1.card = k.factorial := by
  calc
    ∑ C : ActualComponents P, C.1.card =
        ∑ C ∈ Comps (F P), C.card :=
      Finset.sum_coe_sort (Comps (F P)) Finset.card
    _ = (vertsOf (F P)).card :=
      (Hunter.ProofsGB2.card_verts_eq_sum (F P)).symm
    _ = k.factorial := by
      rw [Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk,
        Finset.card_univ, Hunter.ProofsRecursion.card_Vtx]

/-- Each actual component contains `k` vertices per rotation class. -/
theorem actual_component_card_eq_mul_classCount
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponents P) :
    C.1.card = k * componentClassCount (actualComponentPath hP C) := by
  rw [← actualComponentPath_vertsFinset hP C,
    Hunter.ProofsGB2.card_vertsFinset,
    component_numVerts_eq (by omega)
      (actualComponentPath_stronglyExitless hP hk C)]

/-- The total number of actual rotation classes is `(k-1)!`. -/
theorem sum_actual_component_classCount_nat
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P,
      componentClassCount (actualComponentPath hP C) = (k - 1).factorial := by
  have hcards := sum_actual_component_cards hP hk
  have hmul :
      k * (∑ C : ActualComponents P,
        componentClassCount (actualComponentPath hP C)) = k.factorial := by
    rw [Finset.mul_sum]
    calc
      ∑ C : ActualComponents P,
          k * componentClassCount (actualComponentPath hP C) =
          ∑ C : ActualComponents P, C.1.card := by
        apply Finset.sum_congr rfl
        intro C _
        exact (actual_component_card_eq_mul_classCount hP hk C).symm
      _ = k.factorial := hcards
  have hfac : k.factorial = k * (k - 1).factorial := by
    have hkEq : k = (k - 1) + 1 := by omega
    calc
      k.factorial = ((k - 1) + 1).factorial := by rw [← hkEq]
      _ = ((k - 1) + 1) * (k - 1).factorial := Nat.factorial_succ _
      _ = k * (k - 1).factorial := by rw [← hkEq]
  rw [hfac] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

/-- Integer form of the total rotation-class count. -/
theorem sum_actual_component_t
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P, (actualGeom hP C).t =
      ((k - 1).factorial : ℤ) := by
  have hnat := sum_actual_component_classCount_nat hP hk
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
  push_cast at hcast
  simpa [actualGeom, actualComponentGeometry, componentGeometry] using hcast

/-- The selected path weight of an actual component is its induced edge weight. -/
theorem actual_component_path_weight_eq_induced
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponents P) :
    (actualComponentPath hP C).wtP = wEdges (inducedEdges (F P) C.1) := by
  have hpc := actualComponentPath_isPathComponent hP C
  rw [← actualComponentPath_vertsFinset hP C,
    Hunter.ProofsGB2.inducedEdges_eq_edges hpc,
    Hunter.Proved.bridge_wEdges_edges_eq_wtP]

/-- Component path weights sum to `wEdges(F(P))`. -/
theorem sum_actual_component_path_weight
    {P : HPath k} (hP : P.IsHamiltonian) :
    ∑ C : ActualComponents P, (actualComponentPath hP C).wtP = wEdges (F P) := by
  calc
    ∑ C : ActualComponents P, (actualComponentPath hP C).wtP =
        ∑ C : ActualComponents P, wEdges (inducedEdges (F P) C.1) := by
      apply Finset.sum_congr rfl
      intro C _
      exact actual_component_path_weight_eq_induced hP C
    _ = ∑ C ∈ Comps (F P), wEdges (inducedEdges (F P) C) :=
      Finset.sum_coe_sort (Comps (F P)) (fun C => wEdges (inducedEdges (F P) C))
    _ = wEdges (F P) := (Hunter.ProofsGB2.wEdges_eq_sum (F P)).symm

/-- Integer form of the component path-weight sum. -/
theorem sum_actual_component_weight_int
    {P : HPath k} (hP : P.IsHamiltonian) :
    ∑ C : ActualComponents P, ((actualComponentPath hP C).wtP : ℤ) =
      (wEdges (F P) : ℤ) := by
  exact_mod_cast sum_actual_component_path_weight hP

/-- The component minimum-entry weights split into `MinThrough + μ⋆`. -/
theorem sum_actual_component_mu_int
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P, (actualMu C : ℤ) =
      (MinThrough (F P) : ℤ) +
        (actualMu (distinguishedComponent hP hk) : ℤ) := by
  have hcoe :
      (∑ C : ActualComponents P, (actualMu C : ℤ)) =
        ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
    simpa [actualMu] using
      (Finset.sum_coe_sort (Comps (F P))
        (fun C => (compMinto (F P) C : ℤ)))
  have hnat := Hunter.ProofsGB2.minThrough_add_sup (F P)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
  push_cast at hcast
  rw [← distinguished_mu_eq_sup hP hk] at hcast
  rw [hcoe]
  exact hcast.symm

/-- Integer expansion of the actual Bound-1 baseline. -/
theorem actualBaseline_int_eq_components
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualBaseline P : ℤ) =
      (numComps (F P) : ℤ) - 1 +
        (MinThrough (F P) : ℤ) + (wEdges (F P) : ℤ) := by
  have hnc : 1 ≤ numComps (F P) := Hunter.ProofsWP.one_le_numComps_F hP hk
  unfold actualBaseline actualBaselineCore
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hnc]
  ring

/-- The total signed `pValue` is `B₁(F(P)) + 1 + μ⋆`. -/
theorem sum_actual_component_pValue
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P, (actualGeom hP C).pValue =
      (actualBaseline P : ℤ) + 1 +
        (actualMu (distinguishedComponent hP hk) : ℤ) := by
  have hpoint : ∀ C : ActualComponents P,
      (actualGeom hP C).pValue =
        1 + (actualMu C : ℤ) + ((actualComponentPath hP C).wtP : ℤ) := by
    intro C
    dsimp [actualGeom, actualComponentGeometry, componentGeometry, actualMu]
    rw [actualComponentPath_minto hP C]
  calc
    ∑ C : ActualComponents P, (actualGeom hP C).pValue =
        ∑ C : ActualComponents P,
          (1 + (actualMu C : ℤ) + ((actualComponentPath hP C).wtP : ℤ)) := by
      apply Finset.sum_congr rfl
      intro C _
      exact hpoint C
    _ = (Fintype.card (ActualComponents P) : ℤ) +
          (∑ C : ActualComponents P, (actualMu C : ℤ)) +
          (∑ C : ActualComponents P, ((actualComponentPath hP C).wtP : ℤ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
    _ = (numComps (F P) : ℤ) +
          ((MinThrough (F P) : ℤ) +
            (actualMu (distinguishedComponent hP hk) : ℤ)) +
          (wEdges (F P) : ℤ) := by
      rw [sum_actual_component_mu_int hP hk,
        sum_actual_component_weight_int hP]
      simp [ActualComponents, numComps]
    _ = (actualBaseline P : ℤ) + 1 +
          (actualMu (distinguishedComponent hP hk) : ℤ) := by
      rw [actualBaseline_int_eq_components hP hk]
      ring

/-- Total signed defect over all actual components. -/
theorem sum_actual_component_defect
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∑ C : ActualComponents P, (actualGeom hP C).defect =
      D (k : ℤ) *
          ((actualBaseline P : ℤ) + 1 +
            (actualMu (distinguishedComponent hP hk) : ℤ)) -
        A (k : ℤ) * ((k - 1).factorial : ℤ) := by
  have hpoint : ∀ C : ActualComponents P,
      (actualGeom hP C).defect =
        D (k : ℤ) * (actualGeom hP C).pValue -
          A (k : ℤ) * (actualGeom hP C).t := by
    intro C
    exact (actualComponentGeometry_defectEquations hP C).1
  calc
    ∑ C : ActualComponents P, (actualGeom hP C).defect =
        ∑ C : ActualComponents P,
          (D (k : ℤ) * (actualGeom hP C).pValue -
            A (k : ℤ) * (actualGeom hP C).t) := by
      apply Finset.sum_congr rfl
      intro C _
      exact hpoint C
    _ = D (k : ℤ) *
          (∑ C : ActualComponents P, (actualGeom hP C).pValue) -
        A (k : ℤ) *
          (∑ C : ActualComponents P, (actualGeom hP C).t) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = D (k : ℤ) *
          ((actualBaseline P : ℤ) + 1 +
            (actualMu (distinguishedComponent hP hk) : ℤ)) -
        A (k : ℤ) * ((k - 1).factorial : ℤ) := by
      rw [sum_actual_component_pValue hP hk,
        sum_actual_component_t hP hk]

/-- Sum of all non-distinguished signed defects. -/
noncomputable def nondistinguishedDefectSumCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℤ :=
  sumExcept (distinguishedComponent hP hk)
    (fun C : ActualComponents P => (actualGeom hP C).defect)

/-- Adding the distinguished defect recovers the total signed defect. -/
theorem nondistinguishedDefectSumCore_add_distinguished
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    nondistinguishedDefectSumCore hP hk +
        (actualGeom hP (distinguishedComponent hP hk)).defect =
      ∑ C : ActualComponents P, (actualGeom hP C).defect := by
  exact sumExcept_add (distinguishedComponent hP hk)
    (fun C : ActualComponents P => (actualGeom hP C).defect)

/-- Equation (29) for the actual Hunter components. -/
theorem actual_layer_root_identity_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let star := distinguishedComponent hP (by omega : 2 ≤ k)
    let g := actualGeom hP star
    let K := nondistinguishedDefectSumCore hP (by omega : 2 ≤ k)
    let Ks := (Numerics.K k (actualLayer hk hP) : ℤ)
    Ks - K =
      D (k : ℤ) * (g.r + g.x) - ((k : ℤ) - 2) * (g.t - 1) := by
  dsimp
  let hk2 : 2 ≤ k := by omega
  let star := distinguishedComponent hP hk2
  let g := actualGeom hP star
  let K := nondistinguishedDefectSumCore hP hk2
  have htotal := sum_actual_component_defect hP hk2
  have hsplit := nondistinguishedDefectSumCore_add_distinguished hP hk2
  have hstarDef := (actualComponentGeometry_defectEquations hP star).1
  have hstarPV := (actualComponentGeometry_weightEquations hP (by omega : 4 ≤ k) star).2
  have hmu : g.mu = (actualMu star : ℤ) := by
    dsimp [g, actualGeom, actualComponentGeometry, componentGeometry, actualMu]
    rw [actualComponentPath_minto hP star]
  have hbase := actualBaseline_int_eq_hunterPath_add_layer hk hP
  have hKs := K_cast_affine hk (actualLayer hk hP)
  have hAD : A (k : ℤ) = ((k : ℤ) + 1) * D (k : ℤ) + ((k : ℤ) - 2) := by
    simp only [A, D]
    ring
  change (Numerics.K k (actualLayer hk hP) : ℤ) - K =
    D (k : ℤ) * (g.r + g.x) - ((k : ℤ) - 2) * (g.t - 1)
  change K + g.defect =
    ∑ C : ActualComponents P, (actualGeom hP C).defect at hsplit
  change (∑ C : ActualComponents P, (actualGeom hP C).defect) =
    D (k : ℤ) * ((actualBaseline P : ℤ) + 1 + (actualMu star : ℤ)) -
      A (k : ℤ) * ((k - 1).factorial : ℤ) at htotal
  change g.defect = D (k : ℤ) * g.pValue - A (k : ℤ) * g.t at hstarDef
  change g.pValue = ((k : ℤ) + 1) * g.t + g.r + g.x + g.mu - 2 at hstarPV
  have hK : K =
      (∑ C : ActualComponents P, (actualGeom hP C).defect) - g.defect := by
    linarith [hsplit]
  rw [hK, htotal, hstarDef, hstarPV, hmu, hbase, hKs, hAD]
  ring

end PreimageChain

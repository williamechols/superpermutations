import PreimageChain.PathwiseAssemblyCore
import PreimageChain.ActualPrimitiveStability
import PreimageChain.Layerwise

/-!
# Actual layer defect budget and distinguished-component envelope

This module instantiates the abstract arithmetic of Section 9 with the actual Hunter components.
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- Geometry of the root-biased distinguished actual component. -/
noncomputable def distinguishedGeomCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : Geometry :=
  actualGeom hP (distinguishedComponent hP hk)

/-- All non-distinguished actual defects are nonnegative. -/
theorem nondistinguished_defect_nonneg_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponents P)
    (hne : C ≠ distinguishedComponent hP (by omega : 2 ≤ k)) :
    0 ≤ (actualGeom hP C).defect := by
  apply actual_component_defect_nonneg hk hP C
  exact nondistinguished_nonspanning hP (by omega : 2 ≤ k) C hne

/-- The sum of non-distinguished actual defects is nonnegative. -/
theorem nondistinguishedDefectSumCore_nonneg
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    0 ≤ nondistinguishedDefectSumCore hP (by omega : 2 ≤ k) := by
  unfold nondistinguishedDefectSumCore
  apply sumExcept_nonneg
  intro C hne
  exact nondistinguished_defect_nonneg_core hk hP C hne

/-- The two full-endpoint bits of the distinguished component sum to at most two. -/
theorem distinguished_endpoint_bits_le_two_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    let C := distinguishedComponent hP hk2
    let p := actualComponentPath hP C
    let hp := actualComponentPath_stronglyExitless hP hk2 C
    (componentFirstFullBit p (by omega) hp : ℤ) +
      componentLastFullBit p (by omega) hp ≤ 2 := by
  dsimp
  have ha := componentFirstFullBit_le_one
    (actualComponentPath hP (distinguishedComponent hP (by omega)))
    (by omega)
    (actualComponentPath_stronglyExitless hP (by omega)
      (distinguishedComponent hP (by omega)))
  have hb := componentLastFullBit_le_one
    (actualComponentPath hP (distinguishedComponent hP (by omega)))
    (by omega)
    (actualComponentPath_stronglyExitless hP (by omega)
      (distinguishedComponent hP (by omega)))
  exact_mod_cast (by omega :
    componentFirstFullBit
        (actualComponentPath hP (distinguishedComponent hP (by omega))) (by omega)
        (actualComponentPath_stronglyExitless hP (by omega)
          (distinguishedComponent hP (by omega))) +
      componentLastFullBit
        (actualComponentPath hP (distinguishedComponent hP (by omega))) (by omega)
        (actualComponentPath_stronglyExitless hP (by omega)
          (distinguishedComponent hP (by omega))) ≤ 2)

/-- Actual component capacity for the distinguished component. -/
theorem distinguished_component_capacity_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    let C := distinguishedComponent hP hk2
    let g := distinguishedGeomCore hP hk2
    let p := actualComponentPath hP C
    let hp := actualComponentPath_stronglyExitless hP hk2 C
    2 * g.r ≤ ((k : ℤ) - 2) *
      (g.Delta + 2 * g.x +
        (componentFirstFullBit p (by omega) hp : ℤ) +
          componentLastFullBit p (by omega) hp) := by
  dsimp [distinguishedGeomCore, actualGeom]
  exact actual_component_capacity_int hk hP
    (distinguishedComponent hP (by omega : 2 ≤ k))

/-- The actual non-distinguished defect budget satisfies `0 ≤ K ≤ K_s`. -/
theorem actual_defect_budget_bounds_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    let K := nondistinguishedDefectSumCore hP hk2
    0 ≤ K ∧ K ≤ (Numerics.K k (actualLayer hk hP) : ℤ) := by
  dsimp
  let hk2 : 2 ≤ k := by omega
  let C := distinguishedComponent hP hk2
  let g := distinguishedGeomCore hP hk2
  let p := actualComponentPath hP C
  let hp := actualComponentPath_stronglyExitless hP hk2 C
  let a := componentFirstFullBit p (by omega) hp
  let b := componentLastFullBit p (by omega) hp
  apply defect_budget_bounds
    (k := (k : ℤ))
    (Ks := (Numerics.K k (actualLayer hk hP) : ℤ))
    (K := nondistinguishedDefectSumCore hP hk2)
    (r := g.r) (x := g.x) (t := g.t) (Delta := g.Delta)
    (a := (a : ℤ)) (b := (b : ℤ))
  · exact_mod_cast hk
  · exact nondistinguishedDefectSumCore_nonneg hk hP
  · dsimp [g, distinguishedGeomCore, actualGeom,
      actualComponentGeometry, componentGeometry, p]
    positivity
  · dsimp [g, distinguishedGeomCore, actualGeom,
      actualComponentGeometry, componentGeometry, p]
    positivity
  · simpa [C, g, hk2, distinguishedGeomCore] using
      actual_layer_root_identity_core hk hP
  · dsimp [g, distinguishedGeomCore, actualGeom]
    exact (actualComponentGeometry_weightEquations hP
      (by omega : 4 ≤ k) C).1
  · simpa [C, g, p, hp, a, b, hk2] using
      distinguished_component_capacity_core hk hP
  · simpa [C, p, hp, a, b, hk2] using
      distinguished_endpoint_bits_le_two_core hk hP

/-- Distinguished-component size envelope from Theorem 9.2. -/
theorem actual_distinguished_component_size_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    let K := nondistinguishedDefectSumCore hP hk2
    (distinguishedGeomCore hP hk2).t ≤
      ((k : ℤ) - 1) * ((k : ℤ) - 2) +
        ((k : ℤ) - 1) *
          ((Numerics.K k (actualLayer hk hP) : ℤ) - K) := by
  dsimp
  let hk2 : 2 ≤ k := by omega
  let C := distinguishedComponent hP hk2
  let g := distinguishedGeomCore hP hk2
  let p := actualComponentPath hP C
  let hp := actualComponentPath_stronglyExitless hP hk2 C
  let a := componentFirstFullBit p (by omega) hp
  let b := componentLastFullBit p (by omega) hp
  apply distinguished_component_size
    (k := (k : ℤ))
    (Ks := (Numerics.K k (actualLayer hk hP) : ℤ))
    (K := nondistinguishedDefectSumCore hP hk2)
    (r := g.r) (x := g.x) (t := g.t) (Delta := g.Delta)
    (a := (a : ℤ)) (b := (b : ℤ))
  · exact_mod_cast hk
  · dsimp [g, distinguishedGeomCore, actualGeom,
      actualComponentGeometry, componentGeometry, p]
    positivity
  · dsimp [g, distinguishedGeomCore, actualGeom,
      actualComponentGeometry, componentGeometry, p]
    positivity
  · dsimp [g, distinguishedGeomCore, actualGeom]
    exact (actualComponentGeometry_weightEquations hP
      (by omega : 4 ≤ k) C).1
  · simpa [C, g, p, hp, a, b, hk2] using
      distinguished_component_capacity_core hk hP
  · simpa [C, p, hp, a, b, hk2] using
      distinguished_endpoint_bits_le_two_core hk hP
  · exact defect_budget_monotonicity
      (k := (k : ℤ))
      (Ks := (Numerics.K k (actualLayer hk hP) : ℤ))
      (K := nondistinguishedDefectSumCore hP hk2)
      (r := g.r) (x := g.x) (t := g.t) (Delta := g.Delta)
      (a := (a : ℤ)) (b := (b : ℤ))
      (by exact_mod_cast hk)
      (by simpa [C, g, hk2, distinguishedGeomCore] using
      actual_layer_root_identity_core hk hP)
      (by
        dsimp [g, distinguishedGeomCore, actualGeom]
        exact (actualComponentGeometry_weightEquations hP
          (by omega : 4 ≤ k) C).1)
      (by simpa [C, g, p, hp, a, b, hk2] using
        distinguished_component_capacity_core hk hP)
      (by simpa [C, p, hp, a, b, hk2] using
        distinguished_endpoint_bits_le_two_core hk hP)

/-- Weighted distinguished-component envelope used in the portal count. -/
theorem actual_distinguished_component_weighted_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    let K := nondistinguishedDefectSumCore hP hk2
    ((k : ℤ) - 2) * (distinguishedGeomCore hP hk2).t +
        (D (k : ℤ) - 1) * K ≤
      ((k : ℤ) - 1) * ((k : ℤ) - 2) ^ 2 +
        (D (k : ℤ) + 1) *
          (Numerics.K k (actualLayer hk hP) : ℤ) := by
  dsimp
  apply distinguished_component_weighted
    (k := (k : ℤ))
    (Ks := (Numerics.K k (actualLayer hk hP) : ℤ))
    (K := nondistinguishedDefectSumCore hP (by omega : 2 ≤ k))
    (t := (distinguishedGeomCore hP (by omega : 2 ≤ k)).t)
  · exact_mod_cast hk
  · exact (actual_defect_budget_bounds_core hk hP).1
  · exact actual_distinguished_component_size_core hk hP

end PreimageChain

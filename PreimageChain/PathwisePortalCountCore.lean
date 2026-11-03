import PreimageChain.PathwiseLayerCore
import PreimageChain.PathwisePortalCountArithmetic

/-!
# Actual non-distinguished portal count

This module sums primitive-block stability over the actual non-distinguished components and
extracts the paper's closed portal lower bound.
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- Number of terminal primitive-block portals outside the distinguished component. -/
noncomputable def nondistinguishedPortalCountCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  ∑ C : ActualComponents P,
    if C = distinguishedComponent hP hk then 0 else actualPortalBit hP C

/-- Integer sum of non-distinguished rotation-class counts. -/
noncomputable def nondistinguishedClassSumCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℤ :=
  sumExcept (distinguishedComponent hP hk)
    (fun C : ActualComponents P => (actualGeom hP C).t)

/-- Integer cast of the portal count is the corresponding `sumExcept`. -/
theorem nondistinguishedPortalCountCore_cast
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (nondistinguishedPortalCountCore hP hk : ℤ) =
      sumExcept (distinguishedComponent hP hk)
        (fun C : ActualComponents P => (actualPortalBit hP C : ℤ)) := by
  simpa [nondistinguishedPortalCountCore] using
    (sumExcept_natCast (distinguishedComponent hP hk)
      (fun C : ActualComponents P => actualPortalBit hP C)).symm

/-- Adding back the distinguished class count recovers `(k-1)!`. -/
theorem nondistinguishedClassSumCore_add_distinguished
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    nondistinguishedClassSumCore hP hk +
        (actualGeom hP (distinguishedComponent hP hk)).t =
      ((k - 1).factorial : ℤ) := by
  rw [nondistinguishedClassSumCore, sumExcept_add]
  exact sum_actual_component_t hP hk

/-- Primitive-block stability summed over every non-distinguished actual component. -/
theorem sum_nondistinguished_block_affine_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    ((k : ℤ) - 2) * nondistinguishedClassSumCore hP hk2 ≤
      ((k : ℤ) - 2) * D (k : ℤ) *
          (nondistinguishedPortalCountCore hP hk2 : ℤ) +
        (D (k : ℤ) - 1) * nondistinguishedDefectSumCore hP hk2 := by
  dsimp
  let hk2 : 2 ≤ k := by omega
  let star := distinguishedComponent hP hk2
  have hsum := sumExcept_affine
    (ι := ActualComponents P)
    star
    ((k : ℤ) - 2)
    (((k : ℤ) - 2) * D (k : ℤ))
    (D (k : ℤ) - 1)
    (fun C => (actualGeom hP C).t)
    (fun C => (actualPortalBit hP C : ℤ))
    (fun C => (actualGeom hP C).defect)
    (by
      intro C hne
      exact actual_component_block_affine hk hP C
        (nondistinguished_nonspanning hP hk2 C hne))
  change ((k : ℤ) - 2) * nondistinguishedClassSumCore hP hk2 ≤
    ((k : ℤ) - 2) * D (k : ℤ) *
        sumExcept star (fun C : ActualComponents P => (actualPortalBit hP C : ℤ)) +
      (D (k : ℤ) - 1) * nondistinguishedDefectSumCore hP hk2 at hsum
  rw [← nondistinguishedPortalCountCore_cast hP hk2] at hsum
  exact hsum

/-- Actual version of the aggregate portal inequality (paper formula (35)). -/
theorem actual_portal_count_aggregate_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    let hk2 : 2 ≤ k := by omega
    ((k : ℤ) - 2) * ((k - 1).factorial : ℤ) ≤
      ((k : ℤ) - 1) * ((k : ℤ) - 2) ^ 2 +
        (D (k : ℤ) + 1) * (Numerics.K k (actualLayer hk hP) : ℤ) +
        ((k : ℤ) - 2) * D (k : ℤ) *
          (nondistinguishedPortalCountCore hP hk2 : ℤ) := by
  dsimp
  let hk2 : 2 ≤ k := by omega
  let star := distinguishedComponent hP hk2
  let tstar := (actualGeom hP star).t
  let K := nondistinguishedDefectSumCore hP hk2
  let z := (nondistinguishedPortalCountCore hP hk2 : ℤ)
  have hpartition := nondistinguishedClassSumCore_add_distinguished hP hk2
  have hsub :
      ((k - 1).factorial : ℤ) - tstar =
        nondistinguishedClassSumCore hP hk2 := by
    dsimp [tstar]
    nlinarith [hpartition]
  have hnon := sum_nondistinguished_block_affine_core hk hP
  have hweighted := actual_distinguished_component_weighted_core hk hP
  apply portal_count_aggregate
    (k := (k : ℤ))
    (M := ((k - 1).factorial : ℤ))
    (tStar := tstar)
    (K := K) (z := z)
    (Cs := ((k : ℤ) - 1) * ((k : ℤ) - 2) ^ 2 +
      (D (k : ℤ) + 1) * (Numerics.K k (actualLayer hk hP) : ℤ))
  · rw [hsub]
    simpa [K, z, tstar, star, hk2] using hnon
  · simpa [K, tstar, star, hk2, distinguishedGeomCore] using hweighted

/-- Natural form of the aggregate portal inequality. -/
theorem actual_portal_count_aggregate_nat_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (k - 2) * (k - 1).factorial ≤
      Numerics.C k (actualLayer hk hP) +
        ((k - 2) * Numerics.dNat k) *
          nondistinguishedPortalCountCore hP (by omega : 2 ≤ k) := by
  have hagg := actual_portal_count_aggregate_core hk hP
  have hD := dNat_cast_int (by omega : 3 ≤ k)
  have hC :
      (Numerics.C k (actualLayer hk hP) : ℤ) =
        ((k : ℤ) - 1) * ((k : ℤ) - 2) ^ 2 +
          (D (k : ℤ) + 1) *
            (Numerics.K k (actualLayer hk hP) : ℤ) := by
    unfold Numerics.C
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_one, hD]
    ring
  have hcoef :
      (((k - 2) * Numerics.dNat k : ℕ) : ℤ) =
        ((k : ℤ) - 2) * D (k : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ k), hD]
    norm_num
  have hleft :
      (((k - 2) * (k - 1).factorial : ℕ) : ℤ) =
        ((k : ℤ) - 2) * ((k - 1).factorial : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ k)]
    norm_num
  rw [← hC, ← hcoef, ← hleft] at hagg
  exact_mod_cast hagg

/-- The paper's closed portal quantity is bounded by the actual portal count. -/
theorem actual_zClosed_le_portalCount_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    Numerics.zClosed k (actualLayer hk hP) ≤
      nondistinguishedPortalCountCore hP (by omega : 2 ≤ k) := by
  apply zClosed_le_of_aggregate_nat hk
  exact actual_portal_count_aggregate_nat_core hk hP

end PreimageChain

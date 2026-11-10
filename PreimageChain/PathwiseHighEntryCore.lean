import PreimageChain.PathwiseLayerCore

/-!
# Actual high-entry absorbers

This module instantiates Lemma 9.3 for the actual non-distinguished Hunter components and
converts the per-component defect cost into the layerwise absorber-count bound.
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- Actual non-distinguished components whose minimum entry weight is at least three. -/
noncomputable def nondistinguishedHighEntryComponentsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset (ActualComponents P) :=
  Finset.univ.filter fun C =>
    C ≠ distinguishedComponent hP hk ∧ 3 ≤ actualMu C

@[simp] theorem mem_nondistinguishedHighEntryComponentsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponents P) :
    C ∈ nondistinguishedHighEntryComponentsCore hP hk ↔
      C ≠ distinguishedComponent hP hk ∧ 3 ≤ actualMu C := by
  simp [nondistinguishedHighEntryComponentsCore]

/-- Integer cast of `E_k = (k-1)(k-3)`. -/
theorem eNat_cast_int (hk : 4 ≤ k) :
    (Numerics.eNat k : ℤ) = E (k : ℤ) := by
  unfold Numerics.eNat E
  rw [Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ k),
    Nat.cast_sub (by omega : 3 ≤ k)]
  norm_num

/-- Every actual high-entry non-distinguished component consumes at least `E_k` defect. -/
theorem nondistinguished_high_entry_defect_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponents P)
    (hC : C ∈ nondistinguishedHighEntryComponentsCore hP (by omega : 2 ≤ k)) :
    (Numerics.eNat k : ℤ) ≤ (actualGeom hP C).defect := by
  have hmem :=
    (mem_nondistinguishedHighEntryComponentsCore hP (by omega : 2 ≤ k) C).mp hC
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless :=
    actualComponentPath_stronglyExitless hP (by omega : 2 ≤ k) C
  let g := actualGeom hP C
  let a : ℤ := componentFirstFullBit p (by omega) hp
  let b : ℤ := componentLastFullBit p (by omega) hp

  have hcapacity :
      2 * g.r ≤ ((k : ℤ) - 2) *
        (g.Delta + 2 * g.x + a + b) := by
    dsimp [g, actualGeom]
    simpa [p, a, b] using actual_component_capacity_int hk hP C

  have hdefect :
      g.defect =
        D (k : ℤ) * (g.x + g.mu - 2) +
          ((k : ℤ) - 2) * g.Delta - g.r := by
    dsimp [g, actualGeom]
    simpa using actual_component_defect_geometry hP (by omega : 4 ≤ k) C

  have hx : 0 ≤ g.x := by
    dsimp [g, actualGeom, actualComponentGeometry, componentGeometry, p]
    positivity
  have hDelta : 0 ≤ g.Delta := by
    dsimp [g, actualGeom, actualComponentGeometry, componentGeometry, p]
    positivity
  have hmu : 3 ≤ g.mu := by
    dsimp [g, actualGeom, actualComponentGeometry, componentGeometry, p, actualMu]
    rw [actualComponentPath_minto hP C]
    exact_mod_cast hmem.2

  have habNat :
      componentFirstFullBit p (by omega) hp +
          componentLastFullBit p (by omega) hp ≤ 2 := by
    have ha := componentFirstFullBit_le_one p (by omega) hp
    have hb := componentLastFullBit_le_one p (by omega) hp
    omega
  have hab : a + b ≤ 2 := by
    dsimp [a, b]
    exact_mod_cast habNat

  have hk2 : 0 ≤ (k : ℤ) - 2 := by omega
  have hD0 : 0 ≤ D (k : ℤ) := le_of_lt (D_pos (by omega))
  have hE0 : 0 ≤ E (k : ℤ) := le_of_lt (E_pos (by omega))
  have hmu0 : 0 ≤ g.mu - 3 := by linarith
  have hab0 : 0 ≤ 2 - (a + b) := by linarith
  have hcapacityGap :
      0 ≤ ((k : ℤ) - 2) *
          (g.Delta + 2 * g.x + a + b) - 2 * g.r := by
    linarith

  have hEx : 0 ≤ 2 * E (k : ℤ) * g.x := by positivity
  have hDmu : 0 ≤ 2 * D (k : ℤ) * (g.mu - 3) := by positivity
  have hDeltaTerm : 0 ≤ ((k : ℤ) - 2) * g.Delta := by positivity
  have hEndpointTerm :
      0 ≤ ((k : ℤ) - 2) * (2 - (a + b)) := by positivity

  have hidentity :
      2 * g.defect - 2 * E (k : ℤ) =
        (((k : ℤ) - 2) *
            (g.Delta + 2 * g.x + a + b) - 2 * g.r) +
          2 * E (k : ℤ) * g.x +
          2 * D (k : ℤ) * (g.mu - 3) +
          ((k : ℤ) - 2) * g.Delta +
          ((k : ℤ) - 2) * (2 - (a + b)) := by
    rw [hdefect]
    simp only [D, E]
    ring

  rw [eNat_cast_int (by omega : 4 ≤ k)]
  nlinarith

/-- The total high-entry defect charge is bounded by the actual non-distinguished budget. -/
theorem highEntry_card_mul_le_defectSumCore
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (Numerics.eNat k : ℤ) *
        ((nondistinguishedHighEntryComponentsCore hP (by omega : 2 ≤ k)).card : ℤ) ≤
      nondistinguishedDefectSumCore hP (by omega : 2 ≤ k) := by
  let high := nondistinguishedHighEntryComponentsCore hP (by omega : 2 ≤ k)
  let star := distinguishedComponent hP (by omega : 2 ≤ k)
  have hsum :
      ∑ C ∈ high, (Numerics.eNat k : ℤ) ≤
        ∑ C ∈ high, (actualGeom hP C).defect := by
    apply Finset.sum_le_sum
    intro C hC
    exact nondistinguished_high_entry_defect_core hk hP C hC
  have hrewrite :
      (∑ C ∈ high, (actualGeom hP C).defect) =
        ∑ C ∈ high,
          if C = star then 0 else (actualGeom hP C).defect := by
    apply Finset.sum_congr rfl
    intro C hC
    have hC' : C ≠ star ∧ 3 ≤ actualMu C := by
      simpa [high, star] using
        (mem_nondistinguishedHighEntryComponentsCore hP
          (by omega : 2 ≤ k) C).mp (by simpa [high] using hC)
    simp [hC'.1]
  have hsubset :
      ∑ C ∈ high, (actualGeom hP C).defect ≤
        nondistinguishedDefectSumCore hP (by omega : 2 ≤ k) := by
    rw [hrewrite]
    unfold nondistinguishedDefectSumCore sumExcept
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ high
    · intro C _ hCnot
      by_cases hCstar : C = star
      · simp [hCstar]
      · simp only [hCstar, if_false]
        exact nondistinguished_defect_nonneg_core hk hP C hCstar
  calc
    (Numerics.eNat k : ℤ) * (high.card : ℤ) =
        ∑ _C ∈ high, (Numerics.eNat k : ℤ) := by
      simp [mul_comm]
    _ ≤ ∑ C ∈ high, (actualGeom hP C).defect := hsum
    _ ≤ nondistinguishedDefectSumCore hP (by omega : 2 ≤ k) := hsubset

/-- The number of actual high-entry absorbers is at most `⌊K_s/E_k⌋`. -/
theorem card_highEntry_le_K_div_E_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (nondistinguishedHighEntryComponentsCore hP (by omega : 2 ≤ k)).card ≤
      Numerics.K k (actualLayer hk hP) / Numerics.eNat k := by
  have hcost := highEntry_card_mul_le_defectSumCore hk hP
  have hbudget := (actual_defect_budget_bounds_core hk hP).2
  have hmulInt :
      (Numerics.eNat k : ℤ) *
          ((nondistinguishedHighEntryComponentsCore hP
            (by omega : 2 ≤ k)).card : ℤ) ≤
        (Numerics.K k (actualLayer hk hP) : ℤ) := hcost.trans hbudget
  have hmulNat :
      Numerics.eNat k *
          (nondistinguishedHighEntryComponentsCore hP
            (by omega : 2 ≤ k)).card ≤
        Numerics.K k (actualLayer hk hP) := by
    exact_mod_cast hmulInt
  have hEpos : 0 < Numerics.eNat k := Numerics.eNat_pos (by omega : 4 ≤ k)
  exact (Nat.le_div_iff_mul_le hEpos).2 (by
    simpa [Nat.mul_comm] using hmulNat)

end PreimageChain

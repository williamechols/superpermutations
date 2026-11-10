import PreimageChain.PathwiseActualB2Core

/-!
# Pointwise Hunter baseline for an actual image

The analytic pivot and fixed-image Bound-2 regrouping are checked in separate modules; this file
preserves the public theorem used by the integer layer construction.
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- The exact pivot lower bound holds pointwise for every actual Hamilton image. -/
theorem actualBaselineCore_real_ge_pivot
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (actualBaselineCore P : ℝ) ≥
      (iExitless k (k * (k - 1) * (k - 2)) : ℝ) +
        (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))) *
        ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) := by
  have hbase := actualBaselineCore_ge_Rk_gInner hP (by omega : 2 ≤ k)
  have hmono :
      pathwisePivotRatio k * (k.factorial : ℝ) +
          Hunter.ProofsGB2.gInner k (pathwisePivotRatio k) ≤
        Rk k * (k.factorial : ℝ) + Hunter.ProofsGB2.gInner k (Rk k) :=
    Hunter.Proved.gInner_mono (by omega : 2 ≤ k)
      (pathwisePivotRatio k) (Rk k) (pathwisePivotRatio_le_Rk hk)
  have hinner := pathwisePivot_gInner_lower hk
  have hfinal :
      pathwisePivotRatio k * (k.factorial : ℝ) +
          ((iExitless k (pathwisePivot k) : ℝ) -
            pathwisePivotRatio k * (pathwisePivot k : ℝ)) ≤
        (actualBaselineCore P : ℝ) := by
    linarith
  change (iExitless k (pathwisePivot k) : ℝ) +
      pathwisePivotRatio k *
        ((k.factorial : ℝ) - (pathwisePivot k : ℝ)) ≤ _
  linarith

end PreimageChain

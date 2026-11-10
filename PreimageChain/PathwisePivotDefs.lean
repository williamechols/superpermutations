import Hunter.ProofsHeadline
import PreimageChain.Numerics

namespace PreimageChain

open Hunter

/-- The exact pivot length used by Hunter's reduction. -/
def pathwisePivot (k : ℕ) : ℕ := k * (k - 1) * (k - 2)

/-- The pivot cost ratio. -/
noncomputable def pathwisePivotRatio (k : ℕ) : ℝ :=
  ((iExitless k (pathwisePivot k) : ℝ) - (k : ℝ) + 2) /
    ((pathwisePivot k : ℝ) - (k : ℝ))

/-- The pivot denominator is positive. -/
theorem pathwisePivot_sub_pos {k : ℕ} (hk : 3 ≤ k) :
    (0 : ℝ) < (pathwisePivot k : ℝ) - (k : ℝ) := by
  unfold pathwisePivot
  rw [Hunter.ProofsReductions.castP (by omega : 2 ≤ k)]
  exact Hunter.ProofsReductions.D_pos hk

/-- Multiplying the pivot ratio by its denominator recovers the pivot numerator. -/
theorem pathwisePivotRatio_mul_sub {k : ℕ} (hk : 3 ≤ k) :
    pathwisePivotRatio k * ((pathwisePivot k : ℝ) - (k : ℝ)) =
      (iExitless k (pathwisePivot k) : ℝ) - (k : ℝ) + 2 := by
  unfold pathwisePivotRatio
  field_simp [ne_of_gt (pathwisePivot_sub_pos hk)]

end PreimageChain

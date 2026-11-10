import PreimageChain.PathwisePivotDefs

namespace PreimageChain

open Hunter
open scoped Classical

/-- The pivot ratio is no larger than Hunter's global reduction rate. -/
theorem pathwisePivotRatio_le_Rk {k : ℕ} (hk : 3 ≤ k) :
    pathwisePivotRatio k ≤ Rk k := by
  have hpivot : HasExitlessPath k (pathwisePivot k) := by
    simpa [pathwisePivot] using Hunter.Proved.hasExitlessPath_pivot k hk
  have hratioSetNonempty :
      {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
        q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) /
          ((ℓ : ℝ) - (k : ℝ))}.Nonempty := by
    refine ⟨pathwisePivotRatio k, pathwisePivot k, ?_, hpivot, rfl⟩
    have hltR : (k : ℝ) < (pathwisePivot k : ℝ) := by
      linarith [pathwisePivot_sub_pos hk]
    exact_mod_cast hltR
  have hle : pathwisePivotRatio k ≤
      sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
        q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) /
          ((ℓ : ℝ) - (k : ℝ))} := by
    apply le_csInf hratioSetNonempty
    rintro q ⟨ℓ, hℓ, hex, rfl⟩
    simpa [pathwisePivotRatio, pathwisePivot] using
      Hunter.ProofsHeadline.prop4_closed hk hℓ hex
        (by simpa [pathwisePivot] using hpivot)
  exact hle.trans (Hunter.Proved.red_R_closed hk)

end PreimageChain

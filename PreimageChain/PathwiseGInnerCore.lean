import PreimageChain.PathwisePivotRatioCore

namespace PreimageChain

open Hunter
open scoped Classical

/-- The concrete `gInner` is bounded below by the pivot affine value. -/
theorem pathwisePivot_gInner_lower {k : ℕ} (hk : 3 ≤ k) :
    (iExitless k (pathwisePivot k) : ℝ) -
        pathwisePivotRatio k * (pathwisePivot k : ℝ) ≤
      Hunter.ProofsGB2.gInner k (pathwisePivotRatio k) := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hpivot : HasExitlessPath k (pathwisePivot k) := by
    simpa [pathwisePivot] using Hunter.Proved.hasExitlessPath_pivot k hk
  have hXkPrimeNonempty : (Xk' k).Nonempty :=
    Hunter.ProofsB2.Xk'_nonempty_of_Xk_nonempty hk2
      (Hunter.Proved.Xk_nonempty k)
  have hstronglyExitless :
      Xk' k = {p : HPath k | p.StronglyExitless} :=
    Hunter.Proved.prp_Xkcomps_closed hk2
  rw [Hunter.ProofsGB2.gInner]
  apply le_csInf
  · obtain ⟨p, hp⟩ := hXkPrimeNonempty
    exact ⟨_, p, hp, rfl⟩
  rintro q ⟨p, hp, rfl⟩
  have hse : p.StronglyExitless := by
    rw [hstronglyExitless] at hp
    exact hp
  have hexit : p.Exitless := hse.1
  have hdvd : k ∣ p.numVerts :=
    Hunter.Proved.dvd_numVerts_of_stronglyExitless hk1 hse
  have hge : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
  rcases eq_or_lt_of_le hge with heq | hlt
  · have hnv : (p.numVerts : ℝ) = (k : ℝ) := by rw [← heq]
    have hwNat := Hunter.ProofsHeadline.wtP_ge_numVerts_sub_one hk1 hexit
    have hw : (k : ℝ) - 1 ≤ (p.wtP : ℝ) := by
      rw [← heq] at hwNat
      have hwCast : ((k - 1 : ℕ) : ℝ) ≤ (p.wtP : ℝ) := by
        exact_mod_cast hwNat
      rwa [Nat.cast_sub hk1, Nat.cast_one] at hwCast
    rw [hnv]
    nlinarith [pathwisePivotRatio_mul_sub hk]
  · have hexWitness : HasExitlessPath k p.numVerts := ⟨p, hexit, rfl⟩
    have hiw : (iExitless k p.numVerts : ℝ) ≤ (p.wtP : ℝ) := by
      exact_mod_cast Hunter.ProofsHeadline.iExitless_le_wtP hexit
    have hratio := Hunter.ProofsHeadline.prop4_closed hk hlt hexWitness
      (by simpa [pathwisePivot] using hpivot)
    have hd : (0 : ℝ) < (p.numVerts : ℝ) - (k : ℝ) := by
      have hltR : (k : ℝ) < (p.numVerts : ℝ) := by
        exact_mod_cast hlt
      linarith
    have hmul : pathwisePivotRatio k *
        ((p.numVerts : ℝ) - (k : ℝ)) ≤
          (iExitless k p.numVerts : ℝ) - (k : ℝ) + 2 := by
      simpa [pathwisePivotRatio, pathwisePivot] using
        (le_div_iff₀ hd).mp hratio
    nlinarith [pathwisePivotRatio_mul_sub hk, hmul, hiw]

end PreimageChain

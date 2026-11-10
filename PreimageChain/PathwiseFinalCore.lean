import PreimageChain.PathwisePortalCostCore
import PreimageChain.RotationProgress
import PreimageChain.Main

/-!
# Unconditional pathwise and superpermutation lower bounds

This final module combines the exact actual payment, the reduced-path portal correction, and the
non-increasing `σ²` normal form.  It is intentionally small so the final trust boundary is easy to
audit.
-/

namespace PreimageChain

open Hunter

/-- Every `σ²`-reduced Hamilton path satisfies the corrected lower bound. -/
theorem actual_reduced_pathwise_bound_closed
    {k : ℕ} (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    Numerics.hunterBound k + Numerics.gamma k hk ≤ P.wtP + k := by
  have hG := actual_G_le_actualPathPaymentCore hk hP hred
  have hbudget := actualBaseline_add_actualPathPaymentCore_le hP (by omega : 2 ≤ k)
  have hbase := actualBaseline_eq_hunterPath_add_layer hk hP
  have hgamma := Numerics.gamma_le_objective
    (k := k) (s := actualLayer hk hP) hk
  have hrestore := hunterPathBound_add_k hk
  omega

/-- Unconditional pointwise theorem, after replacing an arbitrary path by a reduced representative. -/
theorem pathwise_new_bound_closed (k : ℕ) (hk : 5 ≤ k) :
    PathwiseNewBound k hk := by
  intro P hP
  obtain ⟨Q, hQ, hred, hwt⟩ :=
    sigma2_reduced_normal_form (by omega : 3 ≤ k) hP
  have hQbound := actual_reduced_pathwise_bound_closed hk hQ hred
  omega

/-- Final unconditional superpermutation lower bound. -/
theorem superperm_new_bound_closed
    {k : ℕ} (hk : 5 ≤ k) :
    Numerics.hunterBound k + Numerics.gamma k hk ≤ Ssuper k :=
  superperm_bound_of_pathwise hk (pathwise_new_bound_closed k hk)

end PreimageChain

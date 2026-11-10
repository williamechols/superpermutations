import PreimageChain.PathwisePortalNoTerminalPaymentCore
import PreimageChain.PathwisePortalTerminalPaymentCore

/-!
# Complete actual pathwise portal payment
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- The complete exact payment bounds the actual layer correction in both terminal cases. -/
theorem actual_G_le_actualPathPaymentCore
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    Numerics.G k (actualLayer hk hP) ≤
      actualPathPaymentCore hP (by omega : 2 ≤ k) := by
  by_cases hlast : P.last ∈ heads (F P)
  · have h := noTerminal_G_le_rootGap_add_cost_core hk hP hred hlast
    unfold actualPathPaymentCore
    omega
  · have h := terminal_G_le_payment_core hk hP hred hlast
    unfold actualPathPaymentCore
    omega

end PreimageChain

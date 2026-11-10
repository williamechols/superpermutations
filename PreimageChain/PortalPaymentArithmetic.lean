import PreimageChain.LayerCorrectionAlgebra

namespace PreimageChain

/-- Pure natural-number bookkeeping behind the capacity-one portal payment. -/
theorem theoretical_portal_payment_arithmetic
    {theoretical portals unionCard ordinary paid highEntryBound rootPayment
      routeCost chainCost : ℕ}
    (hcoverage : theoretical - 1 ≤ portals)
    (hbase : portals - unionCard ≤ routeCost)
    (hunion : unionCard ≤ ordinary + paid)
    (hordinary : ordinary ≤ highEntryBound)
    (hpaid : paid ≤ rootPayment)
    (hcost : routeCost ≤ chainCost) :
    theoretical - 1 - highEntryBound ≤ rootPayment + chainCost := by
  omega

end PreimageChain

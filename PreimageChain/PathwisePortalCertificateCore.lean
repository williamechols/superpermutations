import PreimageChain.PortalPaymentArithmetic
import PreimageChain.PortalCapacityOneCore

/-!
# Current-numerics portal assignment certificate

This module packages the finite capacity-one assignment used in Theorem 9.4 with the current
`zClosed` / `eNat` numerical API.
-/

namespace PreimageChain

open scoped BigOperators Classical

/--
A capacity-one target map pays the complete layer correction once actual portal coverage,
high-entry capacity, paid distinguished targets, and total route cost are supplied.
-/
theorem layerCorrection_le_of_actual_portal_assignment_core
    {Source Target : Type*} [Fintype Source]
    [DecidableEq Source] [DecidableEq Target]
    {k s theoreticalPortals highEntryBound rootPayment chainCost : ℕ}
    (target : Source → Target) (htarget : Function.Injective target)
    (portals : Finset Source)
    (ordinaryAbsorbers paidAbsorbers : Finset Target)
    (cost : Source → ℕ)
    (hcoverage : theoreticalPortals - 1 ≤ portals.card)
    (hordinary : ordinaryAbsorbers.card ≤ highEntryBound)
    (hhigh : highEntryBound ≤ Numerics.K k s / Numerics.eNat k)
    (hpaid : paidAbsorbers.card ≤ rootPayment)
    (hzero : ∀ source ∈ portals, cost source = 0 →
      target source ∈ ordinaryAbsorbers ∪ paidAbsorbers)
    (hcost : ∑ source, cost source ≤ chainCost)
    (hZ : Numerics.zClosed k s ≤ theoreticalPortals) :
    Numerics.G k s ≤ rootPayment + chainCost := by
  have hbase := portal_obligation_cost_lower_bound_core
    target htarget portals (ordinaryAbsorbers ∪ paidAbsorbers) cost hzero
  have hunion : (ordinaryAbsorbers ∪ paidAbsorbers).card ≤
      ordinaryAbsorbers.card + paidAbsorbers.card :=
    Finset.card_union_le _ _
  have hportal : theoreticalPortals - 1 - highEntryBound ≤
      rootPayment + chainCost :=
    theoretical_portal_payment_arithmetic
      hcoverage hbase hunion hordinary hpaid hcost
  exact layerCorrection_le_payment hZ hhigh hportal

end PreimageChain

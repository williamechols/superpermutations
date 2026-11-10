import PreimageChain.PathwiseDistinguishedCore
import PreimageChain.ShortestRouteBridge
import PreimageChain.ComponentIdentity

/-!
# Exact actual pathwise payment budget

The exact preimage-chain identity pays three nonnegative terms: the root `μ` gap, the terminal
indicator, and the sum of the actual chain-route costs.  This module packages their natural-number
sum for the final portal assignment.
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- The terminal-chain indicator in the exact preimage identity. -/
noncomputable def actualTerminalIndicatorCore (P : HPath k) : ℕ :=
  indicatorI P (Sset P)

/-- Sum of all actual route costs, including zero exit cost for the terminal chain. -/
noncomputable def actualChainCostSumCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  ∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteNatCost hP hk s

/-- Complete natural payment available beyond the actual Bound-1 baseline. -/
noncomputable def actualPathPaymentCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  actualRootGap hP hk + actualTerminalIndicatorCore P + actualChainCostSumCore hP hk

/-- The actual route-cost sum is bounded by the exact preimage surplus. -/
theorem actualChainCostSumCore_le_surplus
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualChainCostSumCore hP hk : ℤ) ≤ actualPreimageSurplus hP := by
  unfold actualChainCostSumCore
  exact cast_actualChainAssignmentNatCost_le_surplus hP hk

/-- Integer cast of the natural root gap is the exact max-minus-root term. -/
theorem actualRootGap_cast_core
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualRootGap hP hk : ℤ) =
      (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) -
        (compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) : ℤ) := by
  have hroot := actualRootMu_le_componentMuMax hP hk
  have hroot' :
      compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) ≤
        (Comps (F P)).sup (compMinto (F P)) := by
    simpa [actualComponentMuMax] using hroot
  rw [actualRootGap_eq_sup_sub_root hP hk, Nat.cast_sub hroot']

/-- Integer expansion of the concrete actual baseline. -/
theorem actualBaseline_cast_components_core
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualBaseline P : ℤ) =
      (numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) +
        (wEdges (F P) : ℤ) := by
  have hnc : 1 ≤ numComps (F P) := Hunter.ProofsWP.one_le_numComps_F hP hk
  unfold actualBaseline actualBaselineCore
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hnc]
  ring

/-- The actual baseline plus the complete payment is bounded by the original path weight. -/
theorem actualBaseline_add_actualPathPaymentCore_le_int
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualBaseline P : ℤ) + (actualPathPaymentCore hP hk : ℤ) ≤ (P.wtP : ℤ) := by
  have hid := actual_preimage_chain_identity_components hP hk
  have hcost := actualChainCostSumCore_le_surplus hP hk
  have hbase := actualBaseline_cast_components_core hP hk
  have hgap := actualRootGap_cast_core hP hk
  unfold actualPathPaymentCore actualTerminalIndicatorCore
  push_cast
  rw [hbase, hgap]
  linarith

/-- Natural-number form of the exact payment budget. -/
theorem actualBaseline_add_actualPathPaymentCore_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualBaseline P + actualPathPaymentCore hP hk ≤ P.wtP := by
  exact_mod_cast actualBaseline_add_actualPathPaymentCore_le_int hP hk

end PreimageChain

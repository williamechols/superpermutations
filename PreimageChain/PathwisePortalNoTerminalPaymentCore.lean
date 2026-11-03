import PreimageChain.PathwisePortalCertificateCore
import PreimageChain.PathwisePortalNoTerminalZeroCore

/-!
# Capacity-one payment without a terminal chain
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- The propositional zero-cost classification gives membership in the two absorber sets. -/
theorem noTerminal_zero_portal_target_mem_core
    (hk : 5 ≤ k) (hk2 : 2 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : s ∈ actualPortalSourcesCore hP hk2)
    (hcost : actualChainRouteNatCost hP hk2 s = 0) :
    (actualChainMatchingZero hP hk2 hlast).target s ∈
      ordinaryComponentTargetsCore hP hk2 ∪
        distinguishedComponentTargetsCore hP hk2 := by
  let A : ActualNonRootTarget hP hk2 :=
    (actualChainMatchingZero hP hk2 hlast).target s
  have hclass :
      A.1 = distinguishedComponent hP hk2 ∨
        (A.1 ≠ distinguishedComponent hP hk2 ∧ 3 ≤ actualMu A.1) := by
    simpa [A] using
      noTerminal_zero_portal_target_class_core hk hk2 hP hred hlast s hs hcost
  change A ∈ ordinaryComponentTargetsCore hP hk2 ∪
    distinguishedComponentTargetsCore hP hk2
  rcases hclass with hstar | hordinary
  · exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar⟩
  · exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hordinary⟩

/-- No-terminal actual matching pays the layer correction by root gap plus route costs. -/
theorem noTerminal_G_le_rootGap_add_cost_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P)
    (hlast : P.last ∈ heads (F P)) :
    Numerics.G k (actualLayer hk hP) ≤
      actualRootGap hP (by omega : 2 ≤ k) +
        actualChainCostSumCore hP (by omega : 2 ≤ k) := by
  let hk2 : 2 ≤ k := by omega
  let M := actualChainMatchingZero hP hk2 hlast
  apply layerCorrection_le_of_actual_portal_assignment_core
    (k := k) (s := actualLayer hk hP)
    (theoreticalPortals := nondistinguishedPortalCountCore hP hk2)
    (highEntryBound :=
      (nondistinguishedHighEntryComponentsCore hP hk2).card)
    (rootPayment := actualRootGap hP hk2)
    (chainCost := actualChainCostSumCore hP hk2)
    M.target M.target.injective
    (actualPortalSourcesCore hP hk2)
    (ordinaryComponentTargetsCore hP hk2)
    (distinguishedComponentTargetsCore hP hk2)
    (actualChainRouteNatCost hP hk2)
  · exact nondistinguishedPortalCountCore_sub_one_le_sources hP hk2
  · exact ordinaryComponentTargetsCore_card_le_highEntry hP hk2
  · exact card_highEntry_le_K_div_E_core hk hP
  · exact distinguishedComponentTargetsCore_card_le_rootGap hP hk2
  · intro s hs hzero
    exact noTerminal_zero_portal_target_mem_core
      hk hk2 hP hred hlast s hs hzero
  · exact le_rfl
  · exact actual_zClosed_le_portalCount_core hk hP

end PreimageChain

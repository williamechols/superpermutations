import PreimageChain.PathwisePortalCertificateCore
import PreimageChain.PathwisePortalTerminalZeroCore

/-!
# Capacity-one payment with the unique terminal chain
-/

namespace PreimageChain

open Hunter
open scoped BigOperators Classical

variable {k : ℕ}

/-- The propositional terminal classification gives membership in the ordinary/paid target union. -/
theorem terminal_zero_portal_target_mem_core
    (hk : 5 ≤ k) (hk2 : 2 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : s ∈ actualPortalSourcesCore hP hk2)
    (hcost : actualChainRouteNatCost hP hk2 s = 0) :
    (actualChainMatchingOne hP hk2 hlast).target s ∈
      terminalOrdinaryTargetsCore hP hk2 ∪ terminalPaidTargetsCore hP hk2 := by
  have hclass :=
    terminal_zero_portal_target_class_core hk hk2 hP hred hlast s hs hcost
  rcases hclass with hterminal | ⟨A, htarget, hA⟩
  · rw [hterminal]
    apply Finset.mem_union.mpr
    apply Or.inr
    unfold terminalPaidTargetsCore
    exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_singleton_self _
  · rw [htarget]
    rcases hA with hstar | hordinary
    · apply Finset.mem_union.mpr
      apply Or.inr
      unfold terminalPaidTargetsCore
      apply Finset.mem_union.mpr
      apply Or.inl
      exact Finset.mem_image.mpr
        ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar⟩, rfl⟩
    · apply Finset.mem_union.mpr
      apply Or.inl
      unfold terminalOrdinaryTargetsCore
      exact Finset.mem_image.mpr
        ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hordinary⟩, rfl⟩

/-- Unique-terminal actual matching pays the layer correction by all exact payment terms. -/
theorem terminal_G_le_payment_core
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P)
    (hlast : P.last ∉ heads (F P)) :
    Numerics.G k (actualLayer hk hP) ≤
      actualRootGap hP (by omega : 2 ≤ k) + actualTerminalIndicatorCore P +
        actualChainCostSumCore hP (by omega : 2 ≤ k) := by
  let hk2 : 2 ≤ k := by omega
  let M := actualChainMatchingOne hP hk2 hlast
  have hmain := layerCorrection_le_of_actual_portal_assignment_core
    (k := k) (s := actualLayer hk hP)
    (theoreticalPortals := nondistinguishedPortalCountCore hP hk2)
    (highEntryBound :=
      (nondistinguishedHighEntryComponentsCore hP hk2).card)
    (rootPayment := actualRootGap hP hk2 + actualTerminalIndicatorCore P)
    (chainCost := actualChainCostSumCore hP hk2)
    M.target M.target.injective
    (actualPortalSourcesCore hP hk2)
    (terminalOrdinaryTargetsCore hP hk2)
    (terminalPaidTargetsCore hP hk2)
    (actualChainRouteNatCost hP hk2)
    (nondistinguishedPortalCountCore_sub_one_le_sources hP hk2)
    (terminalOrdinaryTargetsCore_card_le_highEntry hP hk2)
    (card_highEntry_le_K_div_E_core hk hP)
    (terminalPaidTargetsCore_card_le_payment hP hk2 hlast)
    (terminal_zero_portal_target_mem_core hk hk2 hP hred hlast)
    (le_refl _)
    (actual_zClosed_le_portalCount_core hk hP)
  omega

end PreimageChain

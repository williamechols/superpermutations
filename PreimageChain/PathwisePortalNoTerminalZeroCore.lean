import PreimageChain.PathwisePortalSourceRigidityCore
import PreimageChain.PathwisePortalTargetsCore
import PreimageChain.PiRelaxation

/-!
# Zero-cost portal classification without a terminal chain
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/--
A zero-cost rigid portal target is either the distinguished component or a non-distinguished
component of minimum entry at least three.  The conclusion is purely propositional so it is
independent of finite-set equality implementations.
-/
theorem noTerminal_zero_portal_target_class_core
    (hk : 5 ≤ k) (hk2 : 2 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : s ∈ actualPortalSourcesCore hP hk2)
    (hcost : actualChainRouteNatCost hP hk2 s = 0) :
    let A : ActualNonRootTarget hP hk2 :=
      (actualChainMatchingZero hP hk2 hlast).target s
    A.1 = distinguishedComponent hP hk2 ∨
      (A.1 ≠ distinguishedComponent hP hk2 ∧ 3 ≤ actualMu A.1) := by
  dsimp only
  let A : ActualNonRootTarget hP hk2 :=
    (actualChainMatchingZero hP hk2 hlast).target s
  change A.1 = distinguishedComponent hP hk2 ∨
    (A.1 ≠ distinguishedComponent hP hk2 ∧ 3 ≤ actualMu A.1)
  have hportal := actualPortalSourcesCore_terminalPortal hk hk2 hP s hs
  have hsEnd := chainEnd_ne_last_of_last_mem_heads hP hlast s
  have hAval := actualChainMatchingZero_target_val hP hk2 hlast s
  by_cases hstar : A.1 = distinguishedComponent hP hk2
  · exact Or.inl hstar
  · have hnonspan : A.1.1 ≠ Finset.univ :=
      nondistinguished_nonspanning hP hk2 A.1 hstar
    have hge2 : 2 ≤ actualMu A.1 := by
      simpa [actualMu] using actual_component_minto_ge_two hP hk2 A.1 hnonspan
    have hne2 : actualMu A.1 ≠ 2 := by
      intro hmu2
      have htargetMu : compMinto (F P)
          (actualNonterminalTargetComponent hP hk2
            ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2 := by
        simpa [actualMu, A, hAval] using hmu2
      have hpositive := actual_terminal_portal_positive hP (by omega : 4 ≤ k)
        hred s hsEnd hportal htargetMu
      omega
    exact Or.inr ⟨hstar, by omega⟩

end PreimageChain

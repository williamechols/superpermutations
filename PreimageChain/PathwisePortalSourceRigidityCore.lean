import PreimageChain.PathwisePortalSourceCore
import PreimageChain.ComponentEndpointRigidity

/-!
# Actual portal source rigidity

A source selected by the actual portal filter is a genuine rigid terminal portal.
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- Membership in the actual portal-source filter gives a genuine rigid terminal portal. -/
theorem actualPortalSourcesCore_terminalPortal
    (hk : 5 ≤ k) (hk2 : 2 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : s ∈ actualPortalSourcesCore hP hk2) :
    ActualTerminalPortal hP (actualChainSourceComponent hP hk2 s) := by
  have hmem := Finset.mem_filter.mp hs
  exact actualPortalBit_one_implies_terminalPortal hk hP _ hmem.2.2

end PreimageChain

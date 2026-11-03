import PreimageChain.ActualChainCapacity

/-!
# 实际 Hunter 分量的无条件端点容量

把组件在正 seam 剩余处切成精确权三链，对每条链使用自动生成的实际容量证书，
再以标准首末满片指标汇总链端点，得到正文组件容量
`2r ≤ (k-2)(Δ+2x+a+b)`。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- 任意 strongly-exitless 实际组件路径满足正文端点容量。 -/
theorem actual_component_capacity
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    2 * componentPieceCount p ≤
      (k - 2) * (componentPieceDeficit p +
        2 * componentSeamResidual p +
          componentFirstFullBit p (by omega) hp +
            componentLastFullBit p (by omega) hp) := by
  classical
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by omega) hp
  let certificate : ∀ chain : ExactWeightThreePieceChain p,
      ExactWeightThreeChainRunCertificate chain := fun chain =>
    (actualChainCapacityPackage hk hp chain).certificate
  have hendpoint : ∀ chain ∈ chains,
      (certificate chain).endpointFullCount =
        chainFirstFullBit chain + chainLastFullBit chain := by
    intro chain _
    exact (actualChainCapacityPackage hk hp chain).endpoint_eq
  have hendpoints := actualComponent_standardEndpointBudget
    (by omega : 1 ≤ k) hp chains hflatten hlength certificate hendpoint
  exact actual_component_capacity_of_chainRunCertificates hk hp chains hflatten
    certificate
    (componentFirstFullBit p (by omega) hp)
    (componentLastFullBit p (by omega) hp)
    hendpoints

end PreimageChain

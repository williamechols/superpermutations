import PreimageChain.Numerics

/-!
# 分层修正的纯自然数支付代数

本模块只把论文定义
`G_s = max(0, Z_s - 1 - ⌊K_s/E_k⌋)`
转换成一个支付量下界，不依赖组件几何或路径结构。
-/

namespace PreimageChain

/--
若真实门户数至少为 `Z_s`，吸收器数不超过 `K_s/E_k`，而所有未吸收门户由
非负整数 `payment` 支付，则论文层修正 `G_s` 不超过该支付量。
-/
theorem layerCorrection_le_payment
    {k s z absorbers payment : ℕ}
    (hZ : Numerics.zClosed k s ≤ z)
    (habsorbers : absorbers ≤ Numerics.K k s / Numerics.eNat k)
    (hpayment : z - 1 - absorbers ≤ payment) :
    Numerics.G k s ≤ payment := by
  unfold Numerics.G
  omega

/-- 用一个更大的吸收器上界替换实际吸收器数。 -/
theorem layerCorrection_le_payment_of_absorber_bound
    {k s z actualAbsorbers absorberBound payment : ℕ}
    (hZ : Numerics.zClosed k s ≤ z)
    (hactual : actualAbsorbers ≤ absorberBound)
    (hbound : absorberBound ≤ Numerics.K k s / Numerics.eNat k)
    (hpayment : z - 1 - actualAbsorbers ≤ payment) :
    Numerics.G k s ≤ payment := by
  apply layerCorrection_le_payment hZ (hactual.trans hbound)
  omega

end PreimageChain

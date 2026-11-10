import PreimageChain.Parameters

/-!
# 门户游程容量与本原块稳定性

本模块形式化正文定理 7.2、公式 (21) 的求和步骤，以及定理 8.2 的完整代数闭包。
所有计数使用整数，并显式携带非负性条件。
-/

namespace PreimageChain

/-- 由局部门户几何的四项约束推出端点匹配容量。

参数与正文证明一致：`n1,n2` 是两类部分片数量，`R` 是正满游程数，`F` 是满片数，
`N` 是长度 `k-3` 的内部长游程数，`excess = Delta - p`。 -/
theorem endpoint_matching_capacity
    {k n1 n2 e R F N p Delta excess r : ℤ}
    (hk : 5 ≤ k)
    (hN0 : 0 ≤ N)
    (honeSided : 2 * R - e ≤ n1 + 2 * n2)
    (hdeficit : n1 + 2 * n2 ≤ Delta)
    (hfull : F ≤ (k - 4) * R + e + N)
    (hexcess : excess = Delta - p)
    (hlong : (k - 3) * N ≤ 2 * excess)
    (hr : r = p + F) :
    2 * r ≤ (k - 2) * (Delta + e) := by
  have hR : 2 * R ≤ Delta + e := by linarith
  have hcoefN : 2 * N ≤ (k - 3) * N := by
    have hprod : 0 ≤ (k - 5) * N := mul_nonneg (by omega) hN0
    nlinarith
  have hNE : N ≤ excess := by linarith
  have hk4 : 0 ≤ k - 4 := by omega
  have hscaled : (k - 4) * (2 * R) ≤ (k - 4) * (Delta + e) :=
    mul_le_mul_of_nonneg_left hR hk4
  nlinarith

/-- 将切开正剩余接缝后各条精确权三链的容量逐项求和，得到正文公式 (21)。 -/
theorem component_capacity
    {ι : Type*} [Fintype ι]
    {k totalR totalDelta x a b : ℤ}
    (hk : 2 ≤ k)
    (r delta endpoints : ι → ℤ)
    (hlocal : ∀ i, 2 * r i ≤ (k - 2) * (delta i + endpoints i))
    (hr : totalR = ∑ i, r i)
    (hDelta : totalDelta = ∑ i, delta i)
    (hendpoints : ∑ i, endpoints i ≤ 2 * x + a + b) :
    2 * totalR ≤ (k - 2) * (totalDelta + 2 * x + a + b) := by
  have hsum : ∑ i, 2 * r i ≤ ∑ i, (k - 2) * (delta i + endpoints i) :=
    Finset.sum_le_sum fun i _ => hlocal i
  have hsum' : 2 * (∑ i, r i) ≤ (k - 2) * ((∑ i, delta i) + ∑ i, endpoints i) := by
    calc
      2 * (∑ i, r i) = ∑ i, 2 * r i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, (k - 2) * (delta i + endpoints i) := hsum
      _ = (k - 2) * ((∑ i, delta i) + ∑ i, endpoints i) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hk0 : 0 ≤ k - 2 := by omega
  have hadd : (∑ i, delta i) + ∑ i, endpoints i ≤
      (∑ i, delta i) + (2 * x + a + b) := add_le_add_right hendpoints _
  have hmul := mul_le_mul_of_nonneg_left hadd hk0
  calc
    2 * totalR = 2 * (∑ i, r i) := by rw [hr]
    _ ≤ (k - 2) * ((∑ i, delta i) + ∑ i, endpoints i) := hsum'
    _ ≤ (k - 2) * ((∑ i, delta i) + (2 * x + a + b)) := hmul
    _ = (k - 2) * (totalDelta + 2 * x + a + b) := by rw [hDelta]; ring

/-- `μ=2` 分支的本原块稳定性。此时首片必为部分片，末片指标即 `π`。 -/
theorem block_stability_mu_two
    {k d m x Delta r a b pi : ℤ}
    (hk : 5 ≤ k) (hx : 0 ≤ x)
    (hidentity :
      2 * d - (k - 2) * m =
        (D k - 1) * x + (k - 2) * Delta - 2 * r)
    (hcapacity : 2 * r ≤ (k - 2) * (Delta + 2 * x + a + b))
    (ha : a = 0) (hb : b = pi) :
    (k - 2) * (m - pi) ≤ 2 * d := by
  have hcoef : D k - 1 - 2 * (k - 2) = (k - 1) * (k - 4) := by
    simp only [D]
    ring
  have hnonneg : 0 ≤ (k - 1) * (k - 4) * x :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) hx
  rw [ha, hb] at hcapacity
  nlinarith

/-- `μ≥3` 分支的本原块稳定性。此时 `π=0`，两个端点指标之和至多二。 -/
theorem block_stability_mu_ge_three
    {k d m x mu Delta r a b pi : ℤ}
    (hk : 5 ≤ k) (hx : 0 ≤ x) (hmu : 3 ≤ mu)
    (hidentity :
      2 * d - (k - 2) * m =
        (D k - 1) * (x + mu - 2) + (k - 2) * Delta - 2 * r)
    (hcapacity : 2 * r ≤ (k - 2) * (Delta + 2 * x + a + b))
    (hab : a + b ≤ 2) (hpi : pi = 0) :
    (k - 2) * (m - pi) ≤ 2 * d := by
  have hcoef : D k - 1 - 2 * (k - 2) = (k - 1) * (k - 4) := by
    simp only [D]
    ring
  have hcoef0 : 0 ≤ D k - 1 - 2 * (k - 2) := by
    rw [hcoef]
    exact mul_nonneg (by omega) (by omega)
  have hDx : 0 ≤ (D k - 1 - 2 * (k - 2)) * x := mul_nonneg hcoef0 hx
  have hD0 : 0 ≤ D k - 1 := by
    have := D_pos (show (3 : ℤ) ≤ k by omega)
    omega
  have hmu1 : 1 ≤ mu - 2 := by omega
  have hDmu : D k - 1 ≤ (D k - 1) * (mu - 2) := by nlinarith
  have hbase : 0 ≤ (D k - 1) - 2 * (k - 2) := hcoef0
  rw [hpi]
  nlinarith

/-- 稳定性不等式与正文仿射形式 (24) 之间的变换。 -/
theorem block_affine_of_stability
    {k t m d pi : ℤ}
    (hk : 5 ≤ k)
    (ht : t = D k * m - (k - 1) * d)
    (hstable : (k - 2) * (m - pi) ≤ 2 * d) :
    (k - 2) * t ≤ (k - 2) * D k * pi + (D k - 1) * d := by
  have hD0 : 0 ≤ D k := le_of_lt (D_pos (by omega))
  have hmul := mul_le_mul_of_nonneg_left hstable hD0
  have hnonneg : 0 ≤ D k * (2 * d - (k - 2) * (m - pi)) := by nlinarith
  have hid :
      (k - 2) * D k * pi + (D k - 1) * d - (k - 2) * t =
        D k * (2 * d - (k - 2) * (m - pi)) := by
    rw [ht]
    simp only [D]
    ring
  linarith

end PreimageChain

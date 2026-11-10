import PreimageChain.PortalCapacity

/-!
# 分层缺陷预算与特选分量包络

对应正文引理 9.1、定理 9.2、公式 (35) 及高入权吸收器计数的算术部分。
-/

namespace PreimageChain

/-- 引理 9.1 的无分数（整体乘二）版本。 -/
theorem defect_budget_monotonicity
    {k Ks K r x t Delta a b : ℤ}
    (hk : 5 ≤ k)
    (hroot : Ks - K = D k * (r + x) - (k - 2) * (t - 1))
    (ht : t = (k - 1) * r - Delta)
    (hcapacity : 2 * r ≤ (k - 2) * (Delta + 2 * x + a + b))
    (hab : a + b ≤ 2) :
    2 * (Ks - K) ≥ 2 * E k * x + (k - 2) * Delta := by
  have hk2 : 0 ≤ k - 2 := by omega
  have hgap : 0 ≤ 2 - (a + b) := by omega
  have hgapScaled : 0 ≤ (k - 2) * (2 - (a + b)) := mul_nonneg hk2 hgap
  have hcapGap : 0 ≤ (k - 2) * (Delta + 2 * x + a + b) - 2 * r := by linarith
  have hid :
      2 * (Ks - K) - (2 * E k * x + (k - 2) * Delta) =
        ((k - 2) * (Delta + 2 * x + a + b) - 2 * r) +
          (k - 2) * (2 - (a + b)) := by
    rw [hroot, ht]
    simp only [D, E]
    ring
  linarith

/-- 缺陷非负时得到 `0 ≤ K ≤ K_s`。 -/
theorem defect_budget_bounds
    {k Ks K r x t Delta a b : ℤ}
    (hk : 5 ≤ k) (hK : 0 ≤ K) (hx : 0 ≤ x) (hDelta : 0 ≤ Delta)
    (hroot : Ks - K = D k * (r + x) - (k - 2) * (t - 1))
    (ht : t = (k - 1) * r - Delta)
    (hcapacity : 2 * r ≤ (k - 2) * (Delta + 2 * x + a + b))
    (hab : a + b ≤ 2) :
    0 ≤ K ∧ K ≤ Ks := by
  refine ⟨hK, ?_⟩
  have hmono := defect_budget_monotonicity hk hroot ht hcapacity hab
  have hEx : 0 ≤ E k * x := mul_nonneg (le_of_lt (E_pos (by omega))) hx
  have hDeltax : 0 ≤ (k - 2) * Delta := mul_nonneg (by omega) hDelta
  linarith

/-- 定理 9.2 的特选分量大小包络。 -/
theorem distinguished_component_size
    {k Ks K r x t Delta a b : ℤ}
    (hk : 5 ≤ k) (hx : 0 ≤ x) (hDelta : 0 ≤ Delta)
    (ht : t = (k - 1) * r - Delta)
    (hcapacity : 2 * r ≤ (k - 2) * (Delta + 2 * x + a + b))
    (hab : a + b ≤ 2)
    (hslack : 2 * (Ks - K) ≥ 2 * E k * x + (k - 2) * Delta) :
    t ≤ (k - 1) * (k - 2) + (k - 1) * (Ks - K) := by
  have hk1 : 0 ≤ k - 1 := by omega
  have hk2 : 0 ≤ k - 2 := by omega
  have hcapScaled := mul_le_mul_of_nonneg_left hcapacity hk1
  have hslackScaled := mul_le_mul_of_nonneg_left hslack hk1
  have hgap : 0 ≤ 2 - (a + b) := by omega
  have hgapScaled : 0 ≤ (k - 1) * (k - 2) * (2 - (a + b)) :=
    mul_nonneg (mul_nonneg hk1 hk2) hgap
  have hSgap : 0 ≤ 2 * (Ks - K) - (2 * E k * x + (k - 2) * Delta) := by linarith
  have hCgap : 0 ≤ (k - 2) * (Delta + 2 * x + a + b) - 2 * r := by linarith
  have hcoef : 0 ≤ E k - (k - 2) := by
    simp only [E]
    nlinarith [sq_nonneg (k - 5)]
  have hcoefScaled : 0 ≤ 2 * (k - 1) * (E k - (k - 2)) * x := by
    positivity
  have hDeltaScaled : 0 ≤ 2 * Delta := by linarith
  have hid :
      2 * ((k - 1) * (k - 2) + (k - 1) * (Ks - K) - t) =
        (k - 1) * (2 * (Ks - K) - (2 * E k * x + (k - 2) * Delta)) +
          (k - 1) * ((k - 2) * (Delta + 2 * x + a + b) - 2 * r) +
          (k - 1) * (k - 2) * (2 - (a + b)) + 2 * Delta +
          2 * (k - 1) * (E k - (k - 2)) * x := by
    rw [ht]
    ring
  have hSscaled : 0 ≤ (k - 1) *
      (2 * (Ks - K) - (2 * E k * x + (k - 2) * Delta)) := mul_nonneg hk1 hSgap
  have hCscaled : 0 ≤ (k - 1) *
      ((k - 2) * (Delta + 2 * x + a + b) - 2 * r) := mul_nonneg hk1 hCgap
  nlinarith

/-- 定理 9.2 的加权包络。 -/
theorem distinguished_component_weighted
    {k Ks K t : ℤ}
    (hk : 5 ≤ k) (hK : 0 ≤ K)
    (hsize : t ≤ (k - 1) * (k - 2) + (k - 1) * (Ks - K)) :
    (k - 2) * t + (D k - 1) * K ≤
      (k - 1) * (k - 2) ^ 2 + (D k + 1) * Ks := by
  have hscaled := mul_le_mul_of_nonneg_left hsize (show 0 ≤ k - 2 by omega)
  have hsizeGap : 0 ≤ (k - 1) * (k - 2) + (k - 1) * (Ks - K) - t := by linarith
  have hk2 : 0 ≤ k - 2 := by omega
  have hprod : 0 ≤ (k - 2) *
      ((k - 1) * (k - 2) + (k - 1) * (Ks - K) - t) := mul_nonneg hk2 hsizeGap
  have htwoK : 0 ≤ 2 * K := by linarith
  have hid :
      (k - 1) * (k - 2) ^ 2 + (D k + 1) * Ks -
          ((k - 2) * t + (D k - 1) * K) =
        (k - 2) * ((k - 1) * (k - 2) + (k - 1) * (Ks - K) - t) + 2 * K := by
    simp only [D]
    ring
  nlinarith

/-- 将非特选分量的仿射稳定性总和与特选分量包络合并，得到公式 (35)。 -/
theorem portal_count_aggregate
    {k M tStar K z Cs : ℤ}
    (hnondistinguished :
      (k - 2) * (M - tStar) ≤ (k - 2) * D k * z + (D k - 1) * K)
    (hroot : (k - 2) * tStar + (D k - 1) * K ≤ Cs) :
    (k - 2) * M ≤ Cs + (k - 2) * D k * z := by
  nlinarith

/-- 若每个高入权目标至少消耗 `E_k` 缺陷，则其数量至多为缺陷预算的商。
这里采用乘法形式，避免在结构证明中引入整数除法。 -/
theorem high_entry_target_capacity
    {k count K Ks : ℤ}
    (hcost : E k * count ≤ K) (hbudget : K ≤ Ks) :
    E k * count ≤ Ks := by
  linarith

end PreimageChain

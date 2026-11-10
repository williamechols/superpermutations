import PreimageChain.PreimageIdentity

/-!
# 门户区间、桥族与中性细分

对应附录 B、命题 11.2 与命题 11.3。这里形式化门户边界区间的精确交集、
双桥族代入仿射包络后的必要系数，以及切开权三接缝时 `B₁` 的不变量。
-/

namespace PreimageChain

open Finset

/-- 附录坐标中的左边界占用区间 `L_a`。 -/
def leftOccupied (n a : ℕ) : Finset ℕ :=
  {0} ∪ Icc (a + 1) (n - 1)

/-- 附录坐标中的右边界占用区间 `R_b`。 -/
def rightOccupied (n b : ℕ) : Finset ℕ :=
  Icc 1 (n - b)

/-- 两个边界片的共同旋转类恰为闭区间 `[a+1,n-b]`。 -/
theorem portal_intersection {n a b : ℕ} (hb : 1 ≤ b) :
    leftOccupied n a ∩ rightOccupied n b = Icc (a + 1) (n - b) := by
  ext x
  simp only [leftOccupied, rightOccupied, mem_inter, mem_union, mem_singleton,
    mem_Icc]
  omega

/-- 附录公式 (54)：共同类数为 `max(0,n-a-b)` 的自然数版本。 -/
theorem portal_intersection_card {n a b : ℕ} (hb : 1 ≤ b) :
    (leftOccupied n a ∩ rightOccupied n b).card = n - (a + b) := by
  rw [portal_intersection hb, Nat.card_Icc]
  omega

/-- 门户两端互不相交当且仅当总缺口达到区间长度。 -/
theorem portal_disjoint_iff {n a b : ℕ} (hb : 1 ≤ b) :
    Disjoint (leftOccupied n a) (rightOccupied n b) ↔ n ≤ a + b := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero,
    portal_intersection_card hb]
  omega

/-- 单个桥块的旋转类数 `P_k=k²-4k+1`。 -/
theorem bridge_block_classes (k : ℤ) :
    (k - 3) + (k - 4) * (k - 1) = k ^ 2 - 4 * k + 1 := by
  ring

/-- 两个桥块合并后的论文参数。 -/
theorem two_bridge_parameters (k : ℤ) :
    2 * ((k - 1) * (k - 3) - 2) = 2 * (k ^ 2 - 4 * k + 1) := by
  ring

/--
双桥族代入任意仿射包络 `t ≤ Dπ+cd` 后，强迫正文公式 (50) 的无分母形式。
-/
theorem two_bridge_forces_linear_coefficient
    {k c : ℤ}
    (henvelope :
      2 * (k ^ 2 - 4 * k + 1) ≤ D k + c * (2 * (k - 1))) :
    k ^ 2 - 5 * k + 1 ≤ 2 * (k - 1) * c := by
  simp only [D] at henvelope
  nlinarith

/-- 上一必要系数至少线性增长：对整数系数有 `2c ≥ k-5`。 -/
theorem two_bridge_coefficient_omega
    {k c : ℤ} (hk : 8 ≤ k)
    (hforced : k ^ 2 - 5 * k + 1 ≤ 2 * (k - 1) * c) :
    k - 5 ≤ 2 * c := by
  have hk1 : 0 < k - 1 := by omega
  have hnum : (k - 1) * (k - 5) ≤ k ^ 2 - 5 * k + 1 := by
    nlinarith
  have hmul : (k - 1) * (k - 5) ≤ (k - 1) * (2 * c) := by
    calc
      (k - 1) * (k - 5) ≤ k ^ 2 - 5 * k + 1 := hnum
      _ ≤ 2 * (k - 1) * c := hforced
      _ = (k - 1) * (2 * c) := by ring
  by_contra hnot
  have hlt : 2 * c < k - 5 := lt_of_not_ge hnot
  have hstrict : (k - 1) * (2 * c) < (k - 1) * (k - 5) :=
    mul_lt_mul_of_pos_left hlt hk1
  omega

/-- 切开 `q` 条权三边时，`-3q+q+2q=0`，故 `B₁` 不变。 -/
theorem neutral_refinement_baseline
    (componentCount imageWeight muSum muMax q : ℤ) :
    baselineOne (componentCount + q) (imageWeight - 3 * q)
        (muSum + 2 * q) muMax =
      baselineOne componentCount imageWeight muSum muMax := by
  simp only [baselineOne]
  ring

/-- 每条被切开的权三接缝相对于新基线的剩余成本为零。 -/
theorem neutral_seam_surplus : (3 : ℤ) - (1 + 2) = 0 := by
  norm_num

end PreimageChain

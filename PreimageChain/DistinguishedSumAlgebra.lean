import PreimageChain.Parameters

/-!
# 去掉特选项的有限和代数

分层证明频繁使用“所有非特选组件之和”以及“再加回特选组件恢复总和”。
-/

namespace PreimageChain

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 去掉一个特选索引的整数和。 -/
def sumExcept (star : ι) (f : ι → ℤ) : ℤ :=
  ∑ i : ι, if i = star then 0 else f i

/-- 去掉特选项再加回该项，恢复完整有限和。 -/
theorem sumExcept_add
    (star : ι) (f : ι → ℤ) :
    sumExcept star f + f star = ∑ i : ι, f i := by
  classical
  unfold sumExcept
  change (∑ i ∈ (Finset.univ : Finset ι), if i = star then 0 else f i) + f star =
    ∑ i ∈ (Finset.univ : Finset ι), f i
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  rw [Finset.filter_ne', Finset.sum_erase_add _ _ (Finset.mem_univ star)]

/-- 完整和等于特选项加非特选和。 -/
theorem add_sumExcept
    (star : ι) (f : ι → ℤ) :
    f star + sumExcept star f = ∑ i : ι, f i := by
  rw [add_comm, sumExcept_add]

/-- 非特选项逐项非负时，去掉特选项后的和非负。 -/
theorem sumExcept_nonneg
    (star : ι) (f : ι → ℤ)
    (hf : ∀ i, i ≠ star → 0 ≤ f i) :
    0 ≤ sumExcept star f := by
  unfold sumExcept
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : i = star
  · simp [hi]
  · simp only [hi, if_false]
    exact hf i hi

/-- 非特选项上的逐项不等式可直接求和。 -/
theorem sumExcept_mono
    (star : ι) (f g : ι → ℤ)
    (hfg : ∀ i, i ≠ star → f i ≤ g i) :
    sumExcept star f ≤ sumExcept star g := by
  unfold sumExcept
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = star
  · simp [hi]
  · simp only [hi, if_false]
    exact hfg i hi

/-- 常数可移入去掉特选项的有限和。 -/
theorem mul_sumExcept (a : ℤ) (star : ι) (f : ι → ℤ) :
    a * sumExcept star f = sumExcept star (fun i => a * f i) := by
  unfold sumExcept
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = star <;> simp [hi]

/-- 两个去掉特选项的和相加等于逐项和。 -/
theorem sumExcept_add_distrib
    (star : ι) (f g : ι → ℤ) :
    sumExcept star f + sumExcept star g =
      sumExcept star (fun i => f i + g i) := by
  unfold sumExcept
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = star <;> simp [hi]

/-- 非特选项满足统一仿射不等式时，对应的不等式可以逐项求和。 -/
theorem sumExcept_affine
    (star : ι) (a b c : ℤ)
    (t portal defect : ι → ℤ)
    (hlocal : ∀ i, i ≠ star →
      a * t i ≤ b * portal i + c * defect i) :
    a * sumExcept star t ≤
      b * sumExcept star portal + c * sumExcept star defect := by
  rw [mul_sumExcept, mul_sumExcept, mul_sumExcept]
  rw [sumExcept_add_distrib]
  exact sumExcept_mono star _ _ hlocal

/-- 自然数值函数转成整数后，去掉特选项的定义与 `Nat.cast` 相容。 -/
theorem sumExcept_natCast
    (star : ι) (f : ι → ℕ) :
    sumExcept star (fun i => (f i : ℤ)) =
      ((∑ i : ι, if i = star then 0 else f i : ℕ) : ℤ) := by
  unfold sumExcept
  push_cast
  rfl

end PreimageChain

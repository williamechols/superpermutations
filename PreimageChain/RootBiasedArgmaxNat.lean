import Mathlib.Data.Fintype.Lattice

/-!
# 标量编码的根优先最大元

键 `2 * score x + 1_{x=root}` 保证先最大化自然数分数，再在同分时唯一优先根。
-/

namespace PreimageChain

open scoped Classical

variable {α : Type*} [Finite α]

/-- 根优先最大化使用的自然数标量键。 -/
def rootBiasedKey [DecidableEq α]
    (score : α → ℕ) (root x : α) : ℕ :=
  2 * score x + if x = root then 1 else 0

/-- 标量键的根优先最大元。 -/
noncomputable def rootBiasedArgmaxNat
    (score : α → ℕ) (root : α) : α := by
  letI : Nonempty α := ⟨root⟩
  exact Classical.choose (Finite.exists_max (rootBiasedKey score root))

/-- 根优先指示量至多一。 -/
theorem rootIndicator_le_one [DecidableEq α] (root x : α) :
    (if x = root then 1 else 0) ≤ 1 := by
  split <;> omega

/-- 任意元素的标量键不超过所选最大元的键。 -/
theorem rootBiasedKey_le_argmax
    (score : α → ℕ) (root x : α) :
    rootBiasedKey score root x ≤
      rootBiasedKey score root (rootBiasedArgmaxNat score root) := by
  letI : Nonempty α := ⟨root⟩
  unfold rootBiasedArgmaxNat
  exact Classical.choose_spec
    (Finite.exists_max (rootBiasedKey score root)) x

/-- 所选元素的原始分数至少为任意元素的分数。 -/
theorem score_le_rootBiasedArgmaxNat
    (score : α → ℕ) (root x : α) :
    score x ≤ score (rootBiasedArgmaxNat score root) := by
  have hkey := rootBiasedKey_le_argmax score root x
  have hx := rootIndicator_le_one root x
  have hstar := rootIndicator_le_one root (rootBiasedArgmaxNat score root)
  unfold rootBiasedKey at hkey
  omega

/-- 若根达到最大分数，根优先规则强制所选元素就是根。 -/
theorem rootBiasedArgmaxNat_eq_root_of_score_ge
    (score : α → ℕ) (root : α)
    (hscore : score (rootBiasedArgmaxNat score root) ≤ score root) :
    rootBiasedArgmaxNat score root = root := by
  have hkey := rootBiasedKey_le_argmax score root root
  have hmax := score_le_rootBiasedArgmaxNat score root root
  have hscoreEq : score (rootBiasedArgmaxNat score root) = score root :=
    Nat.le_antisymm hscore hmax
  by_contra hne
  unfold rootBiasedKey at hkey
  simp [hne, hscoreEq] at hkey
  omega

/-- 若最大元不是根，其原始分数至少比根大一。 -/
theorem root_score_add_one_le_argmaxNat
    (score : α → ℕ) (root : α)
    (hne : rootBiasedArgmaxNat score root ≠ root) :
    score root + 1 ≤ score (rootBiasedArgmaxNat score root) := by
  have hle := score_le_rootBiasedArgmaxNat score root root
  by_contra hnot
  have hrev : score (rootBiasedArgmaxNat score root) ≤ score root := by omega
  exact hne (rootBiasedArgmaxNat_eq_root_of_score_ge score root hrev)

end PreimageChain

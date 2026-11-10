import Mathlib.Tactic

/-!
# 论文参数与费率缺陷正规形

对应正文公式 (2)、(16)--(18)、(37)。整数版本避免自然数截断减法掩盖代数内容；
用于计算的自然数版本在 `Numerics` 模块中给出。
-/

namespace PreimageChain

/-- `D_k = k² - 3k + 1` 的整数版本。 -/
def D (k : ℤ) : ℤ := k ^ 2 - 3 * k + 1

/-- `A_k = k³ - 2k² - k - 1` 的整数版本。 -/
def A (k : ℤ) : ℤ := k ^ 3 - 2 * k ^ 2 - k - 1

/-- 高最小入权分量的缺陷阈值 `E_k = (k-1)(k-3)`。 -/
def E (k : ℤ) : ℤ := (k - 1) * (k - 3)

theorem A_eq (k : ℤ) : A k = (k + 1) * D k + (k - 2) := by
  simp only [A, D]
  ring

theorem D_eq (k : ℤ) : D k = (k - 1) * (k - 2) - 1 := by
  simp only [D]
  ring

theorem D_add_one (k : ℤ) : D k + 1 = (k - 1) * (k - 2) := by
  rw [D_eq]
  ring

theorem E_eq_D_sub (k : ℤ) : E k = D k - (k - 2) := by
  simp only [E, D]
  ring

theorem D_pos {k : ℤ} (hk : 3 ≤ k) : 0 < D k := by
  simp only [D]
  nlinarith [sq_nonneg (k - 2)]

theorem E_pos {k : ℤ} (hk : 4 ≤ k) : 0 < E k := by
  simp only [E]
  nlinarith

/-- 一个区间片分量的纯整数记账数据。 -/
structure Geometry where
  /-- 旋转类数量。 -/
  t : ℤ
  /-- 区间片数量。 -/
  r : ℤ
  /-- 总片缺口。 -/
  Delta : ℤ
  /-- 接缝剩余。 -/
  x : ℤ
  /-- 最小入权。 -/
  mu : ℤ
  /-- `1 + μ + wt(C)`。 -/
  pValue : ℤ
  /-- 费率缺陷。 -/
  defect : ℤ
  /-- 正规形中的辅助整数。 -/
  m : ℤ

namespace Geometry

/-- 正文公式 (16) 的区间片权重记账。 -/
def WeightEquations (k : ℤ) (g : Geometry) : Prop :=
  g.t = (k - 1) * g.r - g.Delta ∧
  g.pValue = (k + 1) * g.t + g.r + g.x + g.mu - 2

/-- 费率缺陷和辅助量的定义。 -/
def DefectEquations (k : ℤ) (g : Geometry) : Prop :=
  g.defect = D k * g.pValue - A k * g.t ∧
  g.m = g.Delta + (k - 1) * (g.x + g.mu - 2)

/-- 正文命题 6.1 的第一式：费率缺陷的几何正规形。 -/
theorem defect_geometry {k : ℤ} {g : Geometry}
    (hw : g.WeightEquations k) (hd : g.DefectEquations k) :
    g.defect = D k * (g.x + g.mu - 2) + (k - 2) * g.Delta - g.r := by
  rcases hw with ⟨ht, hp⟩
  rcases hd with ⟨hd, _hm⟩
  rw [hd, hp, ht, A_eq]
  simp only [D]
  ring

/-- 正文公式 (18) 的旋转类数量正规形。 -/
theorem t_normal_form {k : ℤ} {g : Geometry}
    (hw : g.WeightEquations k) (hd : g.DefectEquations k) :
    g.t = D k * g.m - (k - 1) * g.defect := by
  have hdef := defect_geometry hw hd
  rcases hw with ⟨ht, _hp⟩
  rcases hd with ⟨_hd, hm⟩
  rw [hdef, hm, ht, D_eq]
  ring

/-- 正文公式 (18) 的 `pValue` 正规形。 -/
theorem pValue_normal_form {k : ℤ} {g : Geometry} (hk : 3 ≤ k)
    (hw : g.WeightEquations k) (hd : g.DefectEquations k) :
    g.pValue = A k * g.m - k ^ 2 * g.defect := by
  have ht := t_normal_form hw hd
  rcases hd with ⟨hdef, _hm⟩
  have h1 : D k * g.pValue - A k * g.t - g.defect = 0 := by linarith
  have h2 : g.t - D k * g.m + (k - 1) * g.defect = 0 := by linarith
  have hfactor : D k * (g.pValue - A k * g.m + k ^ 2 * g.defect) = 0 := by
    calc
      D k * (g.pValue - A k * g.m + k ^ 2 * g.defect) =
          (D k * g.pValue - A k * g.t - g.defect) +
            A k * (g.t - D k * g.m + (k - 1) * g.defect) := by
              simp only [D, A]
              ring
      _ = 0 := by rw [h1, h2]; ring
  rcases mul_eq_zero.mp hfactor with hD | hresult
  · exact False.elim ((D_pos hk).ne' hD)
  · linarith

/-- 缺陷给出的同余式，以整除形式陈述。 -/
theorem congruence {k : ℤ} {g : Geometry}
    (hw : g.WeightEquations k) (hd : g.DefectEquations k) :
    D k ∣ g.t + (k - 1) * g.defect := by
  use g.m
  have ht := t_normal_form hw hd
  linarith

end Geometry

/-- 由分量容量不等式推出的高最小入权缺陷下界的代数核心。 -/
theorem high_entry_defect
    {k d x mu : ℤ}
    (hk : 5 ≤ k) (hx : 0 ≤ x) (hmu : 3 ≤ mu)
    (hbound : E k * x + D k * (mu - 2) - (k - 2) ≤ d) :
    E k ≤ d := by
  have hE : E k = D k - (k - 2) := E_eq_D_sub k
  have hDx : 0 ≤ E k * x := mul_nonneg (le_of_lt (E_pos (by omega))) hx
  have hDmu : D k ≤ D k * (mu - 2) := by
    have hD0 := le_of_lt (D_pos (by omega : (3 : ℤ) ≤ k))
    nlinarith
  linarith

end PreimageChain

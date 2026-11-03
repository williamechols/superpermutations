import PreimageChain.Layerwise
import Mathlib.Algebra.Order.Floor.Div

/-!
# 精确整数分层最小化与数值下界

本模块对应正文公式 (27)、(34)--(41) 和附录 C。所有定义均使用自然数精确运算；
`gamma` 是满足附录条件 (58) 的最小层，并证明它确实最小化 `s + G_s`。
-/

namespace PreimageChain.Numerics

/-- 自然数版本的 `D_k`；本模块只在 `k ≥ 5` 使用。 -/
def dNat (k : ℕ) : ℕ := (k - 1) * (k - 2) - 1

/-- 自然数版本的 `E_k`。 -/
def eNat (k : ℕ) : ℕ := (k - 1) * (k - 3)

theorem dNat_eq {k : ℕ} (_hk : 3 ≤ k) : dNat k = (k - 1) * (k - 2) - 1 := by
  rfl

theorem dNat_add_one {k : ℕ} (hk : 3 ≤ k) : dNat k + 1 = (k - 1) * (k - 2) := by
  rw [dNat_eq hk]
  exact Nat.sub_add_cancel (by
    have hp : 0 < (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
    omega)

theorem dNat_eq_e_add {k : ℕ} (hk : 3 ≤ k) : dNat k = eNat k + (k - 2) := by
  have hD := dNat_add_one hk
  have hE : eNat k + (k - 2) + 1 = (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    simp only [eNat]
    simp
    ring
  omega

theorem dNat_pos {k : ℕ} (hk : 3 ≤ k) : 0 < dNat k := by
  have hD := dNat_add_one hk
  have hprod : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
    norm_num at this ⊢
    exact this
  omega

theorem eNat_pos {k : ℕ} (hk : 4 ≤ k) : 0 < eNat k := by
  simp only [eNat]
  exact Nat.mul_pos (by omega) (by omega)

/-- Hunter 字符串下界 `H_k`，正文公式 (3)。 -/
def hunterBound (k : ℕ) : ℕ :=
  k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3 +
    (((k - 2).factorial - (k - 2)) ⌈/⌉ dNat k)

/-- 舍入余量 `κ_k`，正文公式 (27)。 -/
def kappa (k : ℕ) : ℕ :=
  dNat k * (((k - 2).factorial - (k - 2)) ⌈/⌉ dNat k) -
    ((k - 2).factorial - (k - 2))

/-- 第 `s` 层的总缺陷预算。 -/
def K (k s : ℕ) : ℕ := kappa k + s * dNat k

/-- 第 `s` 层的特选分量常数 `C_s`。 -/
def C (k s : ℕ) : ℕ :=
  (k - 1) * (k - 2) ^ 2 + (dNat k + 1) * K k s

/-- 由公式 (36) 直接计算的门户数量下界。 -/
def zRaw (k s : ℕ) : ℕ :=
  (((k - 2) * (k - 1).factorial - C k s) ⌈/⌉ ((k - 2) * dNat k))

/-- `Z_0`。 -/
def zZero (k : ℕ) : ℕ := zRaw k 0

/-- 附录公式 (55) 给出的 `Z_s` 闭式。 -/
def zClosed (k s : ℕ) : ℕ := zZero k - (k - 1) * s

/-- 第 `s` 层的修正项 `G_s`。 -/
def G (k s : ℕ) : ℕ := zClosed k s - 1 - K k s / eNat k

/-- 附录条件 (58) 左侧。 -/
def score (k s : ℕ) : ℕ :=
  k * s + (kappa k + s * (k - 2)) / eNat k

/-- 条件 (58)。 -/
def LayerReady (k s : ℕ) : Prop := zZero k - 1 ≤ score k s

instance (k s : ℕ) : Decidable (LayerReady k s) := by
  unfold LayerReady
  infer_instance

theorem score_mono {k s t : ℕ} (hst : s ≤ t) : score k s ≤ score k t := by
  simp only [score]
  gcongr

theorem score_growth {k s t : ℕ} (hst : s ≤ t) :
    score k s + k * (t - s) ≤ score k t := by
  have hdiv : (kappa k + s * (k - 2)) / eNat k ≤
      (kappa k + t * (k - 2)) / eNat k := by gcongr
  simp only [score]
  have hmul : k * s + k * (t - s) = k * t := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hst]
  omega

theorem layerReady_exists {k : ℕ} (hk : 5 ≤ k) : ∃ s, LayerReady k s := by
  refine ⟨zZero k, ?_⟩
  unfold LayerReady score
  have hk1 : 1 ≤ k := by omega
  have hmul : zZero k ≤ k * zZero k := by
    calc
      zZero k = 1 * zZero k := by simp
      _ ≤ k * zZero k := Nat.mul_le_mul_right _ hk1
  calc
    zZero k - 1 ≤ zZero k := Nat.sub_le _ _
    _ ≤ k * zZero k := hmul
    _ ≤ k * zZero k + (kappa k + zZero k * (k - 2)) / eNat k :=
      Nat.le_add_right _ _

/-- 精确修正 `Γ_k`：满足附录条件 (58) 的最小非负层。 -/
noncomputable def gamma (k : ℕ) (hk : 5 ≤ k) : ℕ :=
  by classical exact Nat.find (layerReady_exists hk)

theorem gamma_spec {k : ℕ} (hk : 5 ≤ k) : LayerReady k (gamma k hk) := by
  classical
  exact Nat.find_spec (layerReady_exists hk)

theorem gamma_min {k : ℕ} (hk : 5 ≤ k) {s : ℕ} (hs : s < gamma k hk) :
    ¬LayerReady k s := by
  classical
  unfold gamma at hs
  exact Nat.find_min (layerReady_exists hk) hs

/-- 用临界层及其前一层验证一个具体的 `gamma` 值。 -/
theorem gamma_eq_of_boundary {k s : ℕ} (hk : 5 ≤ k) (hs : 0 < s)
    (hpass : LayerReady k s) (hprev : ¬LayerReady k (s - 1)) :
    gamma k hk = s := by
  classical
  unfold gamma
  rw [Nat.find_eq_iff]
  refine ⟨hpass, ?_⟩
  intro n hn hready
  have hnprev : n ≤ s - 1 := by omega
  have hmono := score_mono (k := k) hnprev
  exact hprev (by
    unfold LayerReady at hready ⊢
    exact le_trans hready hmono)

/-- 公式 (56)：吸收器商的线性分解。 -/
theorem absorber_linear {k s : ℕ} (hk : 5 ≤ k) :
    K k s / eNat k = s + (kappa k + s * (k - 2)) / eNat k := by
  have hE := eNat_pos (by omega : 4 ≤ k)
  have hD := dNat_eq_e_add (by omega : 3 ≤ k)
  rw [K, hD]
  have hrewrite : kappa k + s * (eNat k + (k - 2)) =
      (kappa k + s * (k - 2)) + eNat k * s := by ring
  rw [hrewrite, Nat.add_mul_div_left _ _ hE, Nat.add_comm]

/-- 公式 (57) 的自然数截断形式。 -/
theorem G_closed {k s : ℕ} (hk : 5 ≤ k) :
    G k s = zZero k - 1 - score k s := by
  rw [G, zClosed, absorber_linear hk]
  simp only [score]
  rw [Nat.sub_sub, Nat.sub_sub]
  have hks : (k - 1) * s + s = k * s := by
    calc
      (k - 1) * s + s = ((k - 1) + 1) * s := by ring
      _ = k * s := by rw [Nat.sub_add_cancel (by omega)]
  omega

theorem G_eq_zero_iff {k s : ℕ} (hk : 5 ≤ k) :
    G k s = 0 ↔ LayerReady k s := by
  rw [G_closed hk]
  unfold LayerReady
  omega

/-- 附录命题 C.1：`gamma` 正是 `s + G_s` 的全局最小值。 -/
theorem gamma_le_objective {k s : ℕ} (hk : 5 ≤ k) :
    gamma k hk ≤ s + G k s := by
  by_cases hs : gamma k hk ≤ s
  · omega
  · have hslt : s < gamma k hk := by omega
    have hnot := gamma_min hk hslt
    have hgammaPos : 0 < gamma k hk := by
      by_contra hzero
      have : gamma k hk = 0 := by omega
      rw [this] at hslt
      omega
    have hpredlt : gamma k hk - 1 < gamma k hk := by omega
    have hpredNot := gamma_min hk hpredlt
    have hsPred : s ≤ gamma k hk - 1 := by omega
    have hgrowth := score_growth (k := k) hsPred
    have hpredFail : score k (gamma k hk - 1) < zZero k - 1 := by
      unfold LayerReady at hpredNot
      omega
    have hk1 : 1 ≤ k := by omega
    let d := gamma k hk - 1 - s
    have hsum : score k s + k * d + 1 ≤ zZero k - 1 := by
      dsimp [d]
      omega
    have hkd : d ≤ k * d := by
      calc
        d = 1 * d := by simp
        _ ≤ k * d := Nat.mul_le_mul_right _ hk1
    have hdiff : d + 1 ≤ zZero k - 1 - score k s := by omega
    have hdistance : gamma k hk = s + (d + 1) := by
      dsimp [d]
      omega
    rw [G_closed hk]
    rw [hdistance]
    exact Nat.add_le_add_left hdiff s

/-- `gamma` 层的目标值恰等于 `gamma`。 -/
theorem objective_at_gamma {k : ℕ} (hk : 5 ≤ k) :
    gamma k hk + G k (gamma k hk) = gamma k hk := by
  have := gamma_spec hk
  rw [← G_eq_zero_iff hk] at this
  omega

private theorem gamma5 : gamma 5 (by omega) = 0 := by
  classical
  unfold gamma
  rw [Nat.find_eq_zero]
  norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma6 : gamma 6 (by omega) = 0 := by
  classical
  unfold gamma
  rw [Nat.find_eq_zero]
  norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma7 : gamma 7 (by omega) = 4 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma8 : gamma 8 (by omega) = 15 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma9 : gamma 9 (by omega) = 80 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma10 : gamma 10 (by omega) = 505 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma11 : gamma 11 (by omega) = 3669 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma12 : gamma 12 (by omega) = 30263 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma13 : gamma 13 (by omega) = 279300 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem gamma14 : gamma 14 (by omega) = 2852497 := by
  apply gamma_eq_of_boundary (by omega) (by omega)
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]
  · norm_num [LayerReady, score, zZero, zRaw, C, K, kappa, dNat, eNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound5 :
    hunterBound 5 + gamma 5 (by omega) = 153 := by
  rw [gamma5]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound6 :
    hunterBound 6 + gamma 6 (by omega) = 869 := by
  rw [gamma6]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound7 :
    hunterBound 7 + gamma 7 (by omega) = 5892 := by
  rw [gamma7]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound8 :
    hunterBound 8 + gamma 8 (by omega) = 46118 := by
  rw [gamma8]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound9 :
    hunterBound 9 + gamma 9 (by omega) = 408418 := by
  rw [gamma9]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound10 :
    hunterBound 10 + gamma 10 (by omega) = 4033080 := by
  rw [gamma10]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound11 :
    hunterBound 11 + gamma 11 (by omega) = 43916235 := by
  rw [gamma11]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound12 :
    hunterBound 12 + gamma 12 (by omega) = 522610764 := by
  rw [gamma12]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound13 :
    hunterBound 13 + gamma 13 (by omega) = 6746523219 := by
  rw [gamma13]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

private theorem numericalBound14 :
    hunterBound 14 + gamma 14 (by omega) = 93890256441 := by
  rw [gamma14]
  norm_num [hunterBound, dNat, Nat.ceilDiv_eq_add_pred_div]

/-- 论文表 1 的精确数值。 -/
theorem numerical_bounds :
    hunterBound 5 + gamma 5 (by omega) = 153 ∧
    hunterBound 6 + gamma 6 (by omega) = 869 ∧
    hunterBound 7 + gamma 7 (by omega) = 5892 ∧
    hunterBound 8 + gamma 8 (by omega) = 46118 ∧
    hunterBound 9 + gamma 9 (by omega) = 408418 ∧
    hunterBound 10 + gamma 10 (by omega) = 4033080 ∧
    hunterBound 11 + gamma 11 (by omega) = 43916235 ∧
    hunterBound 12 + gamma 12 (by omega) = 522610764 ∧
    hunterBound 13 + gamma 13 (by omega) = 6746523219 ∧
    hunterBound 14 + gamma 14 (by omega) = 93890256441 := by
  exact ⟨numericalBound5, numericalBound6, numericalBound7, numericalBound8,
    numericalBound9, numericalBound10, numericalBound11, numericalBound12,
    numericalBound13, numericalBound14⟩

end PreimageChain.Numerics

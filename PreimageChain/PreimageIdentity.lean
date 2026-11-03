import PreimageChain.WeightTwo

/-!
# 预像链双端匹配与精确恒等式

本模块把正文定理 4.1--4.2 中不依赖排列坐标的有限组合内容单独形式化。
`ChainMatchingZero` 与 `ChainMatchingOne` 精确记录两种终端情形的双端双射；随后
`exact_preimage_chain_identity` 验证从 Hunter 精确权重记账抽取基线后的整数恒等式。
-/

namespace PreimageChain

/-- 无终端链情形：源端遗漏末分量，靶端遗漏根分量。 -/
structure ChainMatchingZero (Component Chain : Type*) [Fintype Component]
    [DecidableEq Component]
    [Fintype Chain] where
  root : Component
  last : Component
  source : Chain ≃ {C : Component // C ≠ last}
  target : Chain ≃ {C : Component // C ≠ root}

/-- 有唯一终端链情形：源端覆盖所有分量，靶端以 `PUnit` 表示终端符号。 -/
structure ChainMatchingOne (Component Chain : Type*) [Fintype Component]
    [DecidableEq Component]
    [Fintype Chain] where
  root : Component
  source : Chain ≃ Component
  target : Chain ≃ Sum {C : Component // C ≠ root} Unit

namespace ChainMatchingZero

variable {Component Chain : Type*} [Fintype Component] [DecidableEq Component]
  [Fintype Chain]

/-- 源映射为单射；因此每个分量至多发出一条链。 -/
theorem source_injective (M : ChainMatchingZero Component Chain) :
    Function.Injective M.source :=
  M.source.injective

/-- 靶映射为单射；自嵌套链不会破坏容量一。 -/
theorem target_injective (M : ChainMatchingZero Component Chain) :
    Function.Injective M.target :=
  M.target.injective

/-- 无终端链时，链数等于分量数减一。 -/
theorem card_chains (M : ChainMatchingZero Component Chain) :
    Fintype.card Chain + 1 = Fintype.card Component := by
  have hcard : 0 < Fintype.card Component := Fintype.card_pos_iff.mpr ⟨M.root⟩
  rw [Fintype.card_congr M.source]
  simp
  omega

end ChainMatchingZero

namespace ChainMatchingOne

variable {Component Chain : Type*} [Fintype Component] [DecidableEq Component]
  [Fintype Chain]

/-- 有终端链时，源映射仍为单射。 -/
theorem source_injective (M : ChainMatchingOne Component Chain) :
    Function.Injective M.source :=
  M.source.injective

/-- 加入终端符号后的靶映射为单射。 -/
theorem target_injective (M : ChainMatchingOne Component Chain) :
    Function.Injective M.target :=
  M.target.injective

/-- 有终端链时，总链数等于分量数。 -/
theorem card_chains (M : ChainMatchingOne Component Chain) :
    Fintype.card Chain = Fintype.card Component :=
  Fintype.card_congr M.source

/-- 非终端链恰有 `|Comp|-1` 条。 -/
theorem card_nonterminal_targets (M : ChainMatchingOne Component Chain) :
    Fintype.card {C : Component // C ≠ M.root} + 1 = Fintype.card Component := by
  have hcard : 0 < Fintype.card Component := Fintype.card_pos_iff.mpr ⟨M.root⟩
  simp
  omega

end ChainMatchingOne

/-- 正文公式 (10) 中的 Hunter 基线，以有符号整数记账。 -/
def baselineOne (componentCount imageWeight muSum muMax : ℤ) : ℤ :=
  componentCount - 1 + imageWeight + muSum - muMax

/--
正文定理 4.2 的纯整数核心。

`hbook` 是按照链匹配定理划分 `E₁,E₂` 后的精确权重式：
每条链入口抽取 2，每个非根出口抽取 `μ-1`，并保留链及环的剩余成本。
-/
theorem exact_preimage_chain_identity
    {pathWeight imageWeight componentCount muSum muMax muRoot indicator
      chainSurplus cycleSurplus : ℤ}
    (hbook :
      pathWeight = imageWeight + 2 * (componentCount - 1 + indicator) +
        (muSum - muRoot - (componentCount - 1)) - indicator +
        chainSurplus + cycleSurplus) :
    pathWeight - baselineOne componentCount imageWeight muSum muMax =
      muMax - muRoot + indicator + chainSurplus + cycleSurplus := by
  rw [hbook]
  simp only [baselineOne]
  ring

/-- 若根、终端、链、环四类修正均非负，则精确恒等式逐点加强 Hunter 基线。 -/
theorem baselineOne_le_pathWeight
    {pathWeight imageWeight componentCount muSum muMax muRoot indicator
      chainSurplus cycleSurplus : ℤ}
    (hbook :
      pathWeight = imageWeight + 2 * (componentCount - 1 + indicator) +
        (muSum - muRoot - (componentCount - 1)) - indicator +
        chainSurplus + cycleSurplus)
    (hroot : muRoot ≤ muMax) (hindicator : 0 ≤ indicator)
    (hchain : 0 ≤ chainSurplus) (hcycle : 0 ≤ cycleSurplus) :
    baselineOne componentCount imageWeight muSum muMax ≤ pathWeight := by
  have hid := exact_preimage_chain_identity (muMax := muMax) hbook
  linarith

/--
最短路/指派松弛的抽象闭包：只要 `Pi` 不超过实际根项、终端项和链成本之和，
删除非负环成本后仍得到 `B₁+Π` 下界。
-/
theorem preimage_chain_strengthening
    {pathWeight imageWeight componentCount muSum muMax muRoot indicator
      chainSurplus cycleSurplus Pi : ℤ}
    (hbook :
      pathWeight = imageWeight + 2 * (componentCount - 1 + indicator) +
        (muSum - muRoot - (componentCount - 1)) - indicator +
        chainSurplus + cycleSurplus)
    (hPi : Pi ≤ muMax - muRoot + indicator + chainSurplus)
    (hcycle : 0 ≤ cycleSurplus) :
    baselineOne componentCount imageWeight muSum muMax + Pi ≤ pathWeight := by
  have hid := exact_preimage_chain_identity (muMax := muMax) hbook
  linarith

/-- 把各条非负链剩余成本与非负环成本求和。 -/
theorem surplus_sum_nonneg
    {Chain Cycle : Type*} [Fintype Chain] [Fintype Cycle]
    (chainCost : Chain → ℤ) (cycleCost : Cycle → ℤ)
    (hchain : ∀ K, 0 ≤ chainCost K) (hcycle : ∀ Z, 0 ≤ cycleCost Z) :
    0 ≤ (∑ K, chainCost K) + ∑ Z, cycleCost Z := by
  exact add_nonneg (Finset.sum_nonneg fun K _ => hchain K)
    (Finset.sum_nonneg fun Z _ => hcycle Z)

end PreimageChain

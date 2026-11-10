import PreimageChain.ChainCapacity

/-!
# 缺口--满游程轮廓的有限和容量

本模块把一条精确权三片链压缩为交替的满游程长度 `gap` 与正缺口片
`deficit`。它不依赖具体排列坐标；只要局部几何给出三类逐点约束，就自动生成
`ExactWeightThreeChainRunCertificate`。后续模块只需把真实片链实例化为该轮廓。
-/

namespace PreimageChain

open Hunter
open scoped BigOperators

variable {k : ℕ}

/-- 自然数正性指示量。 -/
def positiveIndicator (n : ℕ) : ℕ := if 0 < n then 1 else 0

/-- 单位缺口指示量。 -/
def unitIndicator (n : ℕ) : ℕ := if n = 1 then 1 else 0

/-- 至少二缺口指示量。 -/
def largeIndicator (n : ℕ) : ℕ := if 2 ≤ n then 1 else 0

/-- 第 `i` 条满游程接触左右链端点的次数。 -/
def endpointContribution (partialCount : ℕ) (gap : ℕ → ℕ) (i : ℕ) : ℕ :=
  (if i = 0 then positiveIndicator (gap i) else 0) +
    (if i = partialCount then positiveIndicator (gap i) else 0)

/-- 内部长游程指示量；只有两个正缺口片之间长度恰为 `k-3` 时为一。 -/
def longInternalIndicator
    (k partialCount : ℕ) (gap : ℕ → ℕ) (i : ℕ) : ℕ :=
  if 1 ≤ i ∧ i < partialCount ∧ gap i = k - 3 then 1 else 0

/-- 一个缺口片可供左右长游程使用的 excess。 -/
def deficitExcess (deficit : ℕ → ℕ) (i : ℕ) : ℕ := deficit i - 1

/-- 第 `i` 个 gap 两侧可见的缺口 excess；链端外侧按零计。 -/
def adjacentExcess
    (partialCount : ℕ) (deficit : ℕ → ℕ) (i : ℕ) : ℕ :=
  (if 1 ≤ i then deficitExcess deficit (i - 1) else 0) +
    (if i < partialCount then deficitExcess deficit i else 0)

/-- 相邻侧计数恒等式：内部 gap 计两侧，两个端 gap 各少一侧。 -/
theorem sum_adjacent_positive
    (partialCount : ℕ) (gap : ℕ → ℕ) :
    (∑ j ∈ Finset.range partialCount,
        (positiveIndicator (gap j) + positiveIndicator (gap (j + 1)))) +
      positiveIndicator (gap 0) + positiveIndicator (gap partialCount) =
        2 * ∑ i ∈ Finset.range (partialCount + 1), positiveIndicator (gap i) := by
  induction partialCount with
  | zero =>
      simp [two_mul]
  | succ partialCount ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- 端点贡献求和恰为首尾两个正满游程指示量。 -/
theorem sum_endpointContribution
    (partialCount : ℕ) (gap : ℕ → ℕ) :
    ∑ i ∈ Finset.range (partialCount + 1),
        endpointContribution partialCount gap i =
      positiveIndicator (gap 0) + positiveIndicator (gap partialCount) := by
  unfold endpointContribution
  rw [Finset.sum_add_distrib]
  simp

/-- 左侧 excess 在全部 gap 上求和时，每个正缺口片恰被计一次。 -/
theorem sum_leftExcess
    (partialCount : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (partialCount + 1),
        (if 1 ≤ i then f (i - 1) else 0) =
      ∑ j ∈ Finset.range partialCount, f j := by
  induction partialCount with
  | zero => simp
  | succ partialCount ih =>
      calc
        (∑ i ∈ Finset.range (partialCount + 1 + 1),
            (if 1 ≤ i then f (i - 1) else 0)) =
            (∑ i ∈ Finset.range (partialCount + 1),
              (if 1 ≤ i then f (i - 1) else 0)) +
                (if 1 ≤ partialCount + 1 then
                  f (partialCount + 1 - 1) else 0) := by
              rw [Finset.sum_range_succ]
        _ = (∑ j ∈ Finset.range partialCount, f j) + f partialCount := by
              rw [ih]
              simp
        _ = ∑ j ∈ Finset.range (partialCount + 1), f j := by
              rw [Finset.sum_range_succ]

/-- 右侧 excess 在全部 gap 上求和时，每个正缺口片恰被计一次。 -/
theorem sum_rightExcess
    (partialCount : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (partialCount + 1),
        (if i < partialCount then f i else 0) =
      ∑ j ∈ Finset.range partialCount, f j := by
  rw [Finset.sum_range_succ]
  have hprefix :
      (∑ i ∈ Finset.range partialCount,
          (if i < partialCount then f i else 0)) =
        ∑ i ∈ Finset.range partialCount, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hprefix]
  simp

/-- 左右 excess 在全部 gap 上求和时，每个正缺口片恰被计两次。 -/
theorem sum_adjacentExcess
    (partialCount : ℕ) (deficit : ℕ → ℕ) :
    ∑ i ∈ Finset.range (partialCount + 1),
        adjacentExcess partialCount deficit i =
      2 * ∑ j ∈ Finset.range partialCount, deficitExcess deficit j := by
  unfold adjacentExcess
  rw [Finset.sum_add_distrib,
    sum_leftExcess partialCount (deficitExcess deficit),
    sum_rightExcess partialCount (deficitExcess deficit)]
  omega

/-- 正缺口列表的总 excess 等于总缺口减去缺口片数。 -/
theorem sum_deficitExcess
    (partialCount : ℕ) (deficit : ℕ → ℕ)
    (hpositive : ∀ j < partialCount, 1 ≤ deficit j) :
    (∑ j ∈ Finset.range partialCount, deficit j) - partialCount =
      ∑ j ∈ Finset.range partialCount, deficitExcess deficit j := by
  have hsum :
      (∑ j ∈ Finset.range partialCount, deficit j) =
        ∑ j ∈ Finset.range partialCount, (deficitExcess deficit j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos := hpositive j (Finset.mem_range.mp hj)
    unfold deficitExcess
    omega
  rw [hsum, Finset.sum_add_distrib]
  simp

/--
一条实际精确权三链的抽象 gap profile。`partialCount+1` 个 gap 依次位于
`partialCount` 个正缺口片之前、之间和之后。

三个局部字段正是实际门户几何需要提供的内容：
* 每条满游程的长度上界；
* 每个单位缺口片不能同时邻接两条正满游程；
* 每条内部 `k-3` 长游程消耗相邻缺口 excess。
-/
structure ExactWeightThreeChainGapProfile {p : HPath k}
    (chain : ExactWeightThreePieceChain p) where
  partialCount : ℕ
  gap : ℕ → ℕ
  deficit : ℕ → ℕ
  deficitPositive : ∀ j < partialCount, 1 ≤ deficit j
  pieceCount :
    exactChainPieceCount chain = partialCount +
      ∑ i ∈ Finset.range (partialCount + 1), gap i
  fullCount :
    exactChainFullCount chain =
      ∑ i ∈ Finset.range (partialCount + 1), gap i
  unitCount :
    exactChainUnitCount chain =
      ∑ j ∈ Finset.range partialCount, unitIndicator (deficit j)
  largeCount :
    exactChainLargeCount chain =
      ∑ j ∈ Finset.range partialCount, largeIndicator (deficit j)
  totalDeficit :
    exactChainTotalDeficit chain =
      ∑ j ∈ Finset.range partialCount, deficit j
  classifyPartial : ∀ j < partialCount,
    unitIndicator (deficit j) + largeIndicator (deficit j) = 1
  gapBound : ∀ i < partialCount + 1,
    gap i ≤
      (k - 4) * positiveIndicator (gap i) +
        endpointContribution partialCount gap i +
          longInternalIndicator k partialCount gap i
  oneSided : ∀ j < partialCount,
    positiveIndicator (gap j) + positiveIndicator (gap (j + 1)) ≤
      unitIndicator (deficit j) + 2 * largeIndicator (deficit j)
  longThreshold : ∀ i < partialCount + 1,
    (k - 3) * longInternalIndicator k partialCount gap i ≤
      adjacentExcess partialCount deficit i

namespace ExactWeightThreeChainGapProfile

/-- profile 中的正满游程数。 -/
def fullRunCount {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainGapProfile chain) : ℕ :=
  ∑ i ∈ Finset.range (profile.partialCount + 1),
    positiveIndicator (profile.gap i)

/-- profile 中的内部 `k-3` 长满游程数。 -/
def longInternalRunCount {p : HPath k}
    {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainGapProfile chain) : ℕ :=
  ∑ i ∈ Finset.range (profile.partialCount + 1),
    longInternalIndicator k profile.partialCount profile.gap i

/-- profile 中被满游程占据的链端点数。 -/
def endpointFullCount {p : HPath k}
    {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainGapProfile chain) : ℕ :=
  positiveIndicator (profile.gap 0) +
    positiveIndicator (profile.gap profile.partialCount)

/-- 任意 gap profile 自动生成 `ChainCapacity` 所需的三项游程证书。 -/
def toRunCertificate
    (hk : 5 ≤ k) {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainGapProfile chain) :
    ExactWeightThreeChainRunCertificate chain := by
  let R := profile.fullRunCount
  let N := profile.longInternalRunCount
  let e := profile.endpointFullCount
  refine
    { fullRunCount := R
      longInternalRunCount := N
      endpointFullCount := e
      oneSided := ?_
      fullBound := ?_
      longBound := ?_ }
  · have hsum :
        (∑ j ∈ Finset.range profile.partialCount,
            (positiveIndicator (profile.gap j) +
              positiveIndicator (profile.gap (j + 1)))) ≤
          (∑ j ∈ Finset.range profile.partialCount,
            unitIndicator (profile.deficit j)) +
            2 * ∑ j ∈ Finset.range profile.partialCount,
              largeIndicator (profile.deficit j) := by
      calc
        _ ≤ ∑ j ∈ Finset.range profile.partialCount,
            (unitIndicator (profile.deficit j) +
              2 * largeIndicator (profile.deficit j)) :=
          Finset.sum_le_sum fun j hj =>
            profile.oneSided j (Finset.mem_range.mp hj)
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hadj := sum_adjacent_positive profile.partialCount profile.gap
    rw [profile.unitCount, profile.largeCount]
    dsimp [R, e, fullRunCount, endpointFullCount]
    calc
      2 * ∑ i ∈ Finset.range (profile.partialCount + 1),
          positiveIndicator (profile.gap i) =
        (∑ j ∈ Finset.range profile.partialCount,
          (positiveIndicator (profile.gap j) +
            positiveIndicator (profile.gap (j + 1)))) +
          positiveIndicator (profile.gap 0) +
            positiveIndicator (profile.gap profile.partialCount) := hadj.symm
      _ ≤ ((∑ j ∈ Finset.range profile.partialCount,
          unitIndicator (profile.deficit j)) +
          2 * ∑ j ∈ Finset.range profile.partialCount,
            largeIndicator (profile.deficit j)) +
          (positiveIndicator (profile.gap 0) +
            positiveIndicator (profile.gap profile.partialCount)) := by
          calc
            ((∑ j ∈ Finset.range profile.partialCount,
                (positiveIndicator (profile.gap j) +
                  positiveIndicator (profile.gap (j + 1)))) +
              positiveIndicator (profile.gap 0)) +
                positiveIndicator (profile.gap profile.partialCount) ≤
              (((∑ j ∈ Finset.range profile.partialCount,
                  unitIndicator (profile.deficit j)) +
                2 * ∑ j ∈ Finset.range profile.partialCount,
                  largeIndicator (profile.deficit j)) +
                positiveIndicator (profile.gap 0)) +
                  positiveIndicator (profile.gap profile.partialCount) :=
              Nat.add_le_add_right
                (Nat.add_le_add_right hsum
                  (positiveIndicator (profile.gap 0)))
                (positiveIndicator (profile.gap profile.partialCount))
            _ = ((∑ j ∈ Finset.range profile.partialCount,
                  unitIndicator (profile.deficit j)) +
                2 * ∑ j ∈ Finset.range profile.partialCount,
                  largeIndicator (profile.deficit j)) +
              (positiveIndicator (profile.gap 0) +
                positiveIndicator (profile.gap profile.partialCount)) :=
              Nat.add_assoc _ _ _
  · have hsum :
        (∑ i ∈ Finset.range (profile.partialCount + 1), profile.gap i) ≤
          (k - 4) * ∑ i ∈ Finset.range (profile.partialCount + 1),
              positiveIndicator (profile.gap i) +
            (∑ i ∈ Finset.range (profile.partialCount + 1),
              endpointContribution profile.partialCount profile.gap i) +
              ∑ i ∈ Finset.range (profile.partialCount + 1),
                longInternalIndicator k profile.partialCount profile.gap i := by
      calc
        _ ≤ ∑ i ∈ Finset.range (profile.partialCount + 1),
            ((k - 4) * positiveIndicator (profile.gap i) +
              endpointContribution profile.partialCount profile.gap i +
                longInternalIndicator k profile.partialCount profile.gap i) :=
          Finset.sum_le_sum fun i hi =>
            profile.gapBound i (Finset.mem_range.mp hi)
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
    have hend := sum_endpointContribution profile.partialCount profile.gap
    rw [profile.fullCount]
    dsimp [R, N, e, fullRunCount, longInternalRunCount,
      endpointFullCount]
    calc
      (∑ i ∈ Finset.range (profile.partialCount + 1), profile.gap i) ≤
        (k - 4) * ∑ i ∈ Finset.range (profile.partialCount + 1),
            positiveIndicator (profile.gap i) +
          (∑ i ∈ Finset.range (profile.partialCount + 1),
            endpointContribution profile.partialCount profile.gap i) +
            ∑ i ∈ Finset.range (profile.partialCount + 1),
              longInternalIndicator k profile.partialCount profile.gap i := hsum
      _ = _ := by rw [hend]
  · have hsum :
        (k - 3) * ∑ i ∈ Finset.range (profile.partialCount + 1),
            longInternalIndicator k profile.partialCount profile.gap i ≤
          ∑ i ∈ Finset.range (profile.partialCount + 1),
            adjacentExcess profile.partialCount profile.deficit i := by
      calc
        _ = ∑ i ∈ Finset.range (profile.partialCount + 1),
            (k - 3) * longInternalIndicator k profile.partialCount profile.gap i := by
          rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i hi =>
          profile.longThreshold i (Finset.mem_range.mp hi)
    have hadj := sum_adjacentExcess profile.partialCount profile.deficit
    have hexcess := sum_deficitExcess profile.partialCount profile.deficit
      profile.deficitPositive
    have hpartial :
        profile.partialCount = exactChainUnitCount chain +
          exactChainLargeCount chain := by
      calc
        profile.partialCount = ∑ _j ∈ Finset.range profile.partialCount, 1 := by simp
        _ = ∑ j ∈ Finset.range profile.partialCount,
            (unitIndicator (profile.deficit j) +
              largeIndicator (profile.deficit j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          symm
          exact profile.classifyPartial j (Finset.mem_range.mp hj)
        _ = (∑ j ∈ Finset.range profile.partialCount,
            unitIndicator (profile.deficit j)) +
              ∑ j ∈ Finset.range profile.partialCount,
                largeIndicator (profile.deficit j) := Finset.sum_add_distrib
        _ = exactChainUnitCount chain + exactChainLargeCount chain := by
          rw [← profile.unitCount, ← profile.largeCount]
    dsimp [N, longInternalRunCount]
    calc
      (k - 3) * ∑ i ∈ Finset.range (profile.partialCount + 1),
          longInternalIndicator k profile.partialCount profile.gap i ≤
        ∑ i ∈ Finset.range (profile.partialCount + 1),
          adjacentExcess profile.partialCount profile.deficit i := hsum
      _ = 2 * ∑ j ∈ Finset.range profile.partialCount,
          deficitExcess profile.deficit j := hadj
      _ = 2 * ((∑ j ∈ Finset.range profile.partialCount,
          profile.deficit j) - profile.partialCount) := by rw [hexcess]
      _ = 2 * (exactChainTotalDeficit chain -
          (exactChainUnitCount chain + exactChainLargeCount chain)) := by
        rw [← profile.totalDeficit, hpartial]

end ExactWeightThreeChainGapProfile

end PreimageChain

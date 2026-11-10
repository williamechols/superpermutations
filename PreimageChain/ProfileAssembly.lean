import PreimageChain.GapCapacity

/-!
# 从局部游程界装配精确权三链容量轮廓

本模块把 `GapCapacity` 所需的三个逐点不等式归约为门户几何直接提供的四个
局部事实：全满链界、含部分片时的端点/内部游程界、单位缺口单侧性，以及
长度 `k-3` 的内部游程缺口阈值。
-/

namespace PreimageChain

open Hunter
open scoped BigOperators

variable {k : ℕ}

/--
一个精确权三链的组合分解数据，连同局部门户几何已经证明的四类事实。
结构中的前五个等式只描述缺口列表的零游程分解；最后四个字段是几何输入。
-/
structure ExactWeightThreeChainLocalProfile {p : HPath k}
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
  allFullBound : partialCount = 0 → gap 0 ≤ k - 2
  partialGapBound : 0 < partialCount → ∀ i < partialCount + 1, gap i ≤ k - 3
  unitOneSided : ∀ j < partialCount, deficit j = 1 →
    positiveIndicator (gap j) + positiveIndicator (gap (j + 1)) ≤ 1
  internalLongThreshold : ∀ i, 1 ≤ i → i < partialCount → gap i = k - 3 →
    k - 1 ≤ deficit (i - 1) + deficit i

namespace ExactWeightThreeChainLocalProfile

private theorem positiveIndicator_le_one (n : ℕ) : positiveIndicator n ≤ 1 := by
  unfold positiveIndicator
  split <;> omega

private theorem positiveIndicator_eq_one_of_pos {n : ℕ} (hn : 0 < n) :
    positiveIndicator n = 1 := by
  simp [positiveIndicator, hn]

private theorem unitIndicator_eq_one_of_eq {n : ℕ} (hn : n = 1) :
    unitIndicator n = 1 := by
  simp [unitIndicator, hn]

private theorem largeIndicator_eq_one_of_ge {n : ℕ} (hn : 2 ≤ n) :
    largeIndicator n = 1 := by
  simp [largeIndicator, hn]

/-- 局部几何输入自动满足 `GapCapacity` 的逐 gap 长度不等式。 -/
theorem gapBound
    (hk : 5 ≤ k) {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainLocalProfile chain) :
    ∀ i < profile.partialCount + 1,
      profile.gap i ≤
        (k - 4) * positiveIndicator (profile.gap i) +
          endpointContribution profile.partialCount profile.gap i +
            longInternalIndicator k profile.partialCount profile.gap i := by
  intro i hi
  by_cases hpartial : profile.partialCount = 0
  · have hi0 : i = 0 := by omega
    subst i
    have hbound := profile.allFullBound hpartial
    by_cases hgap : profile.gap 0 = 0
    · simp [hpartial, hgap, positiveIndicator, endpointContribution,
        longInternalIndicator]
    · have hgapPos : 0 < profile.gap 0 := Nat.pos_of_ne_zero hgap
      have hind : positiveIndicator (profile.gap 0) = 1 :=
        positiveIndicator_eq_one_of_pos hgapPos
      simp [hpartial, endpointContribution, longInternalIndicator, hind]
      omega
  · have hpartialPos : 0 < profile.partialCount := Nat.pos_of_ne_zero hpartial
    have hbound := profile.partialGapBound hpartialPos i hi
    by_cases hgap : profile.gap i = 0
    · simp [hgap, positiveIndicator, endpointContribution,
        longInternalIndicator]
    · have hgapPos : 0 < profile.gap i := Nat.pos_of_ne_zero hgap
      have hind : positiveIndicator (profile.gap i) = 1 :=
        positiveIndicator_eq_one_of_pos hgapPos
      by_cases hleft : i = 0
      · subst i
        simp [endpointContribution, longInternalIndicator, hind]
        omega
      · by_cases hright : i = profile.partialCount
        · subst i
          simp [endpointContribution, longInternalIndicator, hind]
          omega
        · have hiInternal : 1 ≤ i ∧ i < profile.partialCount := by omega
          by_cases hlong : profile.gap i = k - 3
          · have hk3pos : 0 < k - 3 := by omega
            simp [endpointContribution, longInternalIndicator,
              positiveIndicator, hk3pos, hleft, hright, hiInternal, hlong]
            omega
          · have hshort : profile.gap i ≤ k - 4 := by omega
            simp [endpointContribution, longInternalIndicator, hind,
              hleft, hright, hiInternal, hlong]
            exact hshort

/-- 单位缺口单侧性和大缺口的平凡二侧容量给出逐部分片不等式。 -/
theorem oneSided
    {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainLocalProfile chain) :
    ∀ j < profile.partialCount,
      positiveIndicator (profile.gap j) +
          positiveIndicator (profile.gap (j + 1)) ≤
        unitIndicator (profile.deficit j) +
          2 * largeIndicator (profile.deficit j) := by
  intro j hj
  have hpos := profile.deficitPositive j hj
  by_cases hunit : profile.deficit j = 1
  · have hgeom := profile.unitOneSided j hj hunit
    rw [unitIndicator_eq_one_of_eq hunit]
    have hlarge : ¬ 2 ≤ profile.deficit j := by omega
    simp [largeIndicator, hlarge]
    exact hgeom
  · have hlarge : 2 ≤ profile.deficit j := by omega
    have hleft := positiveIndicator_le_one (profile.gap j)
    have hright := positiveIndicator_le_one (profile.gap (j + 1))
    rw [largeIndicator_eq_one_of_ge hlarge]
    have hunitZero : unitIndicator (profile.deficit j) = 0 := by
      simp [unitIndicator, hunit]
    rw [hunitZero]
    omega

/-- 内部长游程阈值等价于相邻两个部分片 excess 至少为 `k-3`。 -/
theorem longThreshold
    (hk : 5 ≤ k) {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainLocalProfile chain) :
    ∀ i < profile.partialCount + 1,
      (k - 3) *
          longInternalIndicator k profile.partialCount profile.gap i ≤
        adjacentExcess profile.partialCount profile.deficit i := by
  intro i hi
  by_cases hinternal : 1 ≤ i ∧ i < profile.partialCount ∧
      profile.gap i = k - 3
  · rcases hinternal with ⟨hi1, hiPartial, hgap⟩
    have hthreshold :=
      profile.internalLongThreshold i hi1 hiPartial hgap
    have hleftPos := profile.deficitPositive (i - 1) (by omega)
    have hrightPos := profile.deficitPositive i hiPartial
    simp [longInternalIndicator, hi1, hiPartial, hgap,
      adjacentExcess, deficitExcess]
    omega
  · have hzero :
        longInternalIndicator k profile.partialCount profile.gap i = 0 := by
      simp [longInternalIndicator, hinternal]
    rw [hzero, Nat.mul_zero]
    exact Nat.zero_le _

/-- 把局部轮廓无损提升为 `GapCapacity` 的完整证书接口。 -/
def toGapProfile
    (hk : 5 ≤ k) {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainLocalProfile chain) :
    ExactWeightThreeChainGapProfile chain where
  partialCount := profile.partialCount
  gap := profile.gap
  deficit := profile.deficit
  deficitPositive := profile.deficitPositive
  pieceCount := profile.pieceCount
  fullCount := profile.fullCount
  unitCount := profile.unitCount
  largeCount := profile.largeCount
  totalDeficit := profile.totalDeficit
  classifyPartial := profile.classifyPartial
  gapBound := profile.gapBound hk
  oneSided := profile.oneSided
  longThreshold := profile.longThreshold hk

/-- 局部轮廓直接产生链容量证书。 -/
def toRunCertificate
    (hk : 5 ≤ k) {p : HPath k} {chain : ExactWeightThreePieceChain p}
    (profile : ExactWeightThreeChainLocalProfile chain) :
    ExactWeightThreeChainRunCertificate chain :=
  (profile.toGapProfile hk).toRunCertificate hk

end ExactWeightThreeChainLocalProfile

end PreimageChain

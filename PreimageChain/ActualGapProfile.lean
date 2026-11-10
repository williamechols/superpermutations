import PreimageChain.PieceGapPartition

/-!
# 片链分解到容量轮廓的有限索引桥

本模块把 gap/partial 列表转成 `GapCapacity` 使用的自然数索引函数。所有有限和、
正性和分类等式都由 `ExactPieceGapPartition` 自动提供；剩余字段只保留真实路径
局部几何。
-/

namespace PreimageChain

open Hunter
open scoped BigOperators

variable {k : ℕ} {p : HPath k}

/-- 越界时采用给定缺省值的自然数列表读取。 -/
def natListAt (fallback : ℕ) (xs : List ℕ) (i : ℕ) : ℕ :=
  xs[i]?.getD fallback

@[simp] theorem natListAt_nil (fallback i : ℕ) :
    natListAt fallback [] i = fallback := by
  cases i <;> rfl

@[simp] theorem natListAt_cons_zero (fallback x : ℕ) (xs : List ℕ) :
    natListAt fallback (x :: xs) 0 = x := by rfl

@[simp] theorem natListAt_cons_succ (fallback x i : ℕ) (xs : List ℕ) :
    natListAt fallback (x :: xs) (i + 1) = natListAt fallback xs i := by
  rfl

/-- 合法下标处的读取值来自原列表。 -/
theorem natListAt_mem {fallback : ℕ} {xs : List ℕ} {i : ℕ}
    (hi : i < xs.length) : natListAt fallback xs i ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [natListAt]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          exact List.mem_cons_of_mem x (by
            simpa [natListAt, Nat.succ_eq_add_one] using ih hi')

/-- 有限 range 上的缺省读取求和精确还原列表和。 -/
theorem sum_range_natListAt (fallback : ℕ) (xs : List ℕ) :
    ∑ i ∈ Finset.range xs.length, natListAt fallback xs i = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp [ih, Nat.add_comm]

/-- 在合法下标处，缺省读取与 `List.map` 交换。 -/
theorem natListAt_map_of_lt
    (fallback fallback' : ℕ) (f : ℕ → ℕ)
    {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    natListAt fallback' (xs.map f) i = f (natListAt fallback xs i) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simpa [natListAt, Nat.succ_eq_add_one] using ih hi'

/-- gap 的长度列表。 -/
def gapLengths {p : HPath k}
    (gaps : List (List (ComponentIntervalPiece p))) : List ℕ :=
  gaps.map List.length

/-- 部分片的正缺口列表。 -/
def partialDeficits {p : HPath k}
    (partials : List (ComponentIntervalPiece p)) : List ℕ :=
  partials.map ComponentIntervalPiece.deficit

/--
规范分解之后尚需从真实路径几何提供的四项局部事实。自然数函数与最终
`ExactWeightThreeChainLocalProfile` 完全一致。
-/
structure ExactPieceGapGeometry
    (gaps : List (List (ComponentIntervalPiece p)))
    (partials : List (ComponentIntervalPiece p)) where
  allFullBound : partials.length = 0 →
    natListAt 0 (gapLengths gaps) 0 ≤ k - 2
  partialGapBound : 0 < partials.length → ∀ i < partials.length + 1,
    natListAt 0 (gapLengths gaps) i ≤ k - 3
  unitOneSided : ∀ j < partials.length,
    natListAt 1 (partialDeficits partials) j = 1 →
      positiveIndicator (natListAt 0 (gapLengths gaps) j) +
        positiveIndicator (natListAt 0 (gapLengths gaps) (j + 1)) ≤ 1
  internalLongThreshold : ∀ i, 1 ≤ i → i < partials.length →
    natListAt 0 (gapLengths gaps) i = k - 3 →
      k - 1 ≤
        natListAt 1 (partialDeficits partials) (i - 1) +
          natListAt 1 (partialDeficits partials) i

/-- 分解与四项几何事实自动产生完整的局部容量轮廓。 -/
def ExactPieceGapPartition.toLocalProfile
    {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (partition : ExactPieceGapPartition chain.pieces gaps partials)
    (geometry : ExactPieceGapGeometry gaps partials) :
    ExactWeightThreeChainLocalProfile chain where
  partialCount := partials.length
  gap := natListAt 0 (gapLengths gaps)
  deficit := natListAt 1 (partialDeficits partials)
  deficitPositive := by
    intro j hj
    have hmem : natListAt 1 (partialDeficits partials) j ∈
        partialDeficits partials := natListAt_mem (by
          simpa [partialDeficits] using hj)
    rcases List.mem_map.mp hmem with ⟨piece, hpiece, heq⟩
    rw [← heq]
    exact partition.partials_positive piece hpiece
  pieceCount := by
    have hpLen := partition.pieces_length
    have hsum := sum_range_natListAt 0 (gapLengths gaps)
    have hlen : (gapLengths gaps).length = partials.length + 1 := by
      simpa [gapLengths] using partition.gaps_length
    rw [hlen] at hsum
    change chain.pieces.length = partials.length +
      ∑ i ∈ Finset.range (partials.length + 1),
        natListAt 0 (gapLengths gaps) i
    calc
      chain.pieces.length = (gapLengths gaps).sum + partials.length := by
        simpa [gapLengths] using hpLen
      _ = partials.length + (gapLengths gaps).sum := Nat.add_comm _ _
      _ = partials.length +
          ∑ i ∈ Finset.range (partials.length + 1),
            natListAt 0 (gapLengths gaps) i := by rw [← hsum]
  fullCount := by
    have hcount := partition.full_count
    have hsum := sum_range_natListAt 0 (gapLengths gaps)
    have hlen : (gapLengths gaps).length = partials.length + 1 := by
      simpa [gapLengths] using partition.gaps_length
    rw [hlen] at hsum
    change deficitFullCount (exactChainDeficits chain) =
      ∑ i ∈ Finset.range (partials.length + 1),
        natListAt 0 (gapLengths gaps) i
    calc
      deficitFullCount (exactChainDeficits chain) =
          (gapLengths gaps).sum := by
        simpa [exactChainDeficits, gapLengths] using hcount
      _ = ∑ i ∈ Finset.range (partials.length + 1),
          natListAt 0 (gapLengths gaps) i := hsum.symm
  unitCount := by
    have hcount := partition.unit_count
    let values := partialDeficits partials
    have hsum := sum_range_natListAt 0 (values.map unitIndicator)
    have hlen : (values.map unitIndicator).length = partials.length := by
      simp [values, partialDeficits]
    rw [hlen] at hsum
    change deficitUnitCount (exactChainDeficits chain) =
      ∑ j ∈ Finset.range partials.length,
        unitIndicator (natListAt 1 (partialDeficits partials) j)
    calc
      deficitUnitCount (exactChainDeficits chain) =
          (values.map unitIndicator).sum := by
        simpa [exactChainDeficits, values, partialDeficits,
          List.map_map, Function.comp_def] using hcount
      _ = ∑ j ∈ Finset.range partials.length,
          natListAt 0 (values.map unitIndicator) j := hsum.symm
      _ = ∑ j ∈ Finset.range partials.length,
          unitIndicator (natListAt 1 (partialDeficits partials) j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < (partialDeficits partials).length := by
          simpa [partialDeficits] using Finset.mem_range.mp hj
        simpa [values] using natListAt_map_of_lt
          1 0 unitIndicator (xs := partialDeficits partials) hj'
  largeCount := by
    have hcount := partition.large_count
    let values := partialDeficits partials
    have hsum := sum_range_natListAt 0 (values.map largeIndicator)
    have hlen : (values.map largeIndicator).length = partials.length := by
      simp [values, partialDeficits]
    rw [hlen] at hsum
    change deficitLargeCount (exactChainDeficits chain) =
      ∑ j ∈ Finset.range partials.length,
        largeIndicator (natListAt 1 (partialDeficits partials) j)
    calc
      deficitLargeCount (exactChainDeficits chain) =
          (values.map largeIndicator).sum := by
        simpa [exactChainDeficits, values, partialDeficits,
          List.map_map, Function.comp_def] using hcount
      _ = ∑ j ∈ Finset.range partials.length,
          natListAt 0 (values.map largeIndicator) j := hsum.symm
      _ = ∑ j ∈ Finset.range partials.length,
          largeIndicator (natListAt 1 (partialDeficits partials) j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < (partialDeficits partials).length := by
          simpa [partialDeficits] using Finset.mem_range.mp hj
        simpa [values] using natListAt_map_of_lt
          1 0 largeIndicator (xs := partialDeficits partials) hj'
  totalDeficit := by
    have hcount := partition.total_deficit
    have hsum := sum_range_natListAt 1 (partialDeficits partials)
    have hlen : (partialDeficits partials).length = partials.length := by
      simp [partialDeficits]
    rw [hlen] at hsum
    change (exactChainDeficits chain).sum =
      ∑ j ∈ Finset.range partials.length,
        natListAt 1 (partialDeficits partials) j
    calc
      (exactChainDeficits chain).sum = (partialDeficits partials).sum := by
        simpa [exactChainDeficits, partialDeficits] using hcount
      _ = ∑ j ∈ Finset.range partials.length,
          natListAt 1 (partialDeficits partials) j := hsum.symm
  classifyPartial := by
    intro j hj
    have hmem : natListAt 1 (partialDeficits partials) j ∈
        partialDeficits partials := natListAt_mem (by
          simpa [partialDeficits] using hj)
    rcases List.mem_map.mp hmem with ⟨piece, hpiece, heq⟩
    rw [← heq]
    exact partition.partial_classification piece hpiece
  allFullBound := geometry.allFullBound
  partialGapBound := geometry.partialGapBound
  unitOneSided := geometry.unitOneSided
  internalLongThreshold := geometry.internalLongThreshold

end PreimageChain

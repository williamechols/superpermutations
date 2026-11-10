import PreimageChain.GapCapacity

/-!
# 缺口列表的规范满游程分解

任意缺口列表都唯一地按“零缺口游程--正缺口--零缺口游程”形状递归分解。
本模块先证明存在性及所有计数恒等式；后续实际片链模块再把各游程提升为
`WeightThreeFullRun`，并调用门户局部几何。
-/

namespace PreimageChain

/--
`DeficitGapPartition source gaps partials` 表示 `source` 由 `partials.length+1`
条零缺口游程组成，相邻游程之间依次插入正缺口 `partials`。
`gaps` 记录这些零游程的长度。
-/
inductive DeficitGapPartition : List ℕ → List ℕ → List ℕ → Prop
  | nil : DeficitGapPartition [] [0] []
  | full {source g gaps partials}
      (rest : DeficitGapPartition source (g :: gaps) partials) :
      DeficitGapPartition (0 :: source) ((g + 1) :: gaps) partials
  | positive {d source gaps partials}
      (hd : 1 ≤ d)
      (rest : DeficitGapPartition source gaps partials) :
      DeficitGapPartition (d :: source) (0 :: gaps) (d :: partials)

namespace DeficitGapPartition

/-- 分解总含至少一条（可能为空的）零游程。 -/
theorem gaps_nonempty {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) : gaps ≠ [] := by
  induction partition <;> simp

/-- 任意缺口列表都存在规范游程分解。 -/
theorem exists_partition (source : List ℕ) :
    ∃ gaps partials, DeficitGapPartition source gaps partials := by
  induction source with
  | nil => exact ⟨[0], [], DeficitGapPartition.nil⟩
  | cons d source ih =>
      obtain ⟨gaps, partials, partition⟩ := ih
      by_cases hd : d = 0
      · subst d
        have hne := partition.gaps_nonempty
        cases gaps with
        | nil => exact False.elim (hne rfl)
        | cons g gaps =>
            exact ⟨(g + 1) :: gaps, partials,
              DeficitGapPartition.full partition⟩
      · have hdpos : 1 ≤ d := by omega
        exact ⟨0 :: gaps, d :: partials,
          DeficitGapPartition.positive hdpos partition⟩

/-- 零游程数恰比正缺口数多一。 -/
theorem gaps_length {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    gaps.length = partials.length + 1 := by
  induction partition with
  | nil => rfl
  | full rest ih => simpa using ih
  | positive hd rest ih =>
      simp only [List.length_cons]
      omega

/-- 分解列出的每个部分片缺口都严格为正。 -/
theorem partials_positive {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    ∀ d ∈ partials, 1 ≤ d := by
  induction partition with
  | nil => simp
  | full rest ih => exact ih
  | positive hd rest ih =>
      intro d hdmem
      rcases List.mem_cons.mp hdmem with rfl | hdmem
      · exact hd
      · exact ih d hdmem

/-- 原列表长度等于正缺口数与全部零游程长度之和。 -/
theorem source_length {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    source.length = partials.length + gaps.sum := by
  induction partition with
  | nil => simp
  | @full source g gaps partials rest ih =>
      simp only [List.sum_cons] at ih
      change source.length + 1 = partials.length + (g + 1 + gaps.sum)
      rw [ih]
      omega
  | @positive d source gaps partials hd rest ih =>
      change source.length + 1 = (partials.length + 1) + (0 + gaps.sum)
      rw [ih]
      omega

/-- 原列表总缺口等于正缺口列表之和。 -/
theorem source_sum {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    source.sum = partials.sum := by
  induction partition with
  | nil => simp
  | full rest ih => simpa using ih
  | positive hd rest ih => simp [ih]

/-- 原列表中的满片数等于全部零游程长度之和。 -/
theorem fullCount {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    deficitFullCount source = gaps.sum := by
  induction partition with
  | nil => simp [deficitFullCount]
  | @full source g gaps partials rest ih =>
      simp only [List.sum_cons] at ih
      change 1 + deficitFullCount source = g + 1 + gaps.sum
      rw [ih]
      omega
  | @positive d source gaps partials hd rest ih =>
      have hd0 : d ≠ 0 := by omega
      simp [deficitFullCount, hd0, ih]

/-- 单位缺口计数在删除零游程后保持不变。 -/
theorem unitCount {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    deficitUnitCount source = deficitUnitCount partials := by
  induction partition with
  | nil => simp [deficitUnitCount]
  | full rest ih => simpa [deficitUnitCount] using ih
  | positive hd rest ih => simp [deficitUnitCount, ih]

/-- 至少二缺口计数在删除零游程后保持不变。 -/
theorem largeCount {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    deficitLargeCount source = deficitLargeCount partials := by
  induction partition with
  | nil => simp [deficitLargeCount]
  | full rest ih => simpa [deficitLargeCount] using ih
  | positive hd rest ih => simp [deficitLargeCount, ih]

/-- 正缺口列表自身不含零缺口。 -/
theorem partials_fullCount_zero {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    deficitFullCount partials = 0 := by
  induction partition with
  | nil => simp [deficitFullCount]
  | full rest ih => exact ih
  | @positive d source gaps partials hd rest ih =>
      have hd0 : d ≠ 0 := by omega
      simp [deficitFullCount, hd0, ih]

/-- 正缺口数精确分成单位缺口和至少二缺口两类。 -/
theorem partials_length_eq_unit_add_large {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    partials.length = deficitUnitCount partials + deficitLargeCount partials := by
  have hpartition := deficitCounts_partition partials
  rw [partition.partials_fullCount_zero] at hpartition
  omega

/-- 原列表的部分片数就是正缺口列表长度。 -/
theorem source_partialCount {source gaps partials : List ℕ}
    (partition : DeficitGapPartition source gaps partials) :
    deficitUnitCount source + deficitLargeCount source = partials.length := by
  rw [partition.unitCount, partition.largeCount,
    partition.partials_length_eq_unit_add_large]

end DeficitGapPartition

end PreimageChain

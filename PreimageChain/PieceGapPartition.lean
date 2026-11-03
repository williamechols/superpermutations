import PreimageChain.ProfileAssembly

/-!
# 精确权三片链的规范满游程分解

本模块直接在带路径证书的 `ComponentIntervalPiece` 列表上分解：每个零缺口片进入
某个满游程，每个正缺口片进入部分片列表。分解保留原始顺序，并给出容量轮廓所需
的全部计数恒等式。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

/--
把片列表分成 `partials.length+1` 个满片游程和按顺序夹在中间的正缺口片。
构造从列表头递归，因此第一条 gap 始终是第一片之前的满游程。
-/
inductive ExactPieceGapPartition :
    List (ComponentIntervalPiece p) →
      List (List (ComponentIntervalPiece p)) →
        List (ComponentIntervalPiece p) → Prop
  | nil : ExactPieceGapPartition [] [[]] []
  | full {piece : ComponentIntervalPiece p} {pieces gap gaps partials}
      (hzero : piece.deficit = 0)
      (rest : ExactPieceGapPartition pieces (gap :: gaps) partials) :
      ExactPieceGapPartition (piece :: pieces) ((piece :: gap) :: gaps) partials
  | positive {piece : ComponentIntervalPiece p} {pieces gap gaps partials}
      (hpos : 1 ≤ piece.deficit)
      (rest : ExactPieceGapPartition pieces (gap :: gaps) partials) :
      ExactPieceGapPartition (piece :: pieces) ([] :: gap :: gaps) (piece :: partials)

namespace ExactPieceGapPartition

variable {pieces : List (ComponentIntervalPiece p)}
  {gaps : List (List (ComponentIntervalPiece p))}
  {partials : List (ComponentIntervalPiece p)}

/-- 每个分解至少含一条 gap。 -/
theorem gaps_ne_nil
    (partition : ExactPieceGapPartition pieces gaps partials) : gaps ≠ [] := by
  cases partition <;> simp

/-- 任意实际片列表都存在上述分解。 -/
theorem exists_for (pieces : List (ComponentIntervalPiece p)) :
    ∃ gaps partials, ExactPieceGapPartition pieces gaps partials := by
  induction pieces with
  | nil => exact ⟨[[]], [], .nil⟩
  | cons piece pieces ih =>
      obtain ⟨gaps, partials, rest⟩ := ih
      have hne := rest.gaps_ne_nil
      obtain ⟨gap, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
      by_cases hzero : piece.deficit = 0
      · exact ⟨(piece :: gap) :: tail, partials, .full hzero rest⟩
      · have hpos : 1 ≤ piece.deficit := Nat.one_le_iff_ne_zero.mpr hzero
        exact ⟨[] :: gap :: tail, piece :: partials, .positive hpos rest⟩

/-- gap 数始终比部分片数多一。 -/
theorem gaps_length
    (partition : ExactPieceGapPartition pieces gaps partials) :
    gaps.length = partials.length + 1 := by
  induction partition with
  | nil => simp
  | full hzero rest ih => simpa using ih
  | positive hpos rest ih => simp at ih ⊢; omega

/-- 原片数等于全部满片数与部分片数之和。 -/
theorem pieces_length
    (partition : ExactPieceGapPartition pieces gaps partials) :
    pieces.length = (gaps.map List.length).sum + partials.length := by
  induction partition with
  | nil => simp
  | full hzero rest ih => simp at ih ⊢; omega
  | positive hpos rest ih => simp at ih ⊢; omega

/-- 每条 gap 中的片都具有零缺口。 -/
theorem gaps_all_full
    (partition : ExactPieceGapPartition pieces gaps partials) :
    ∀ gap ∈ gaps, ∀ piece ∈ gap, piece.deficit = 0 := by
  induction partition with
  | nil => simp
  | @full piece pieces gap gaps partials hzero rest ih =>
      intro candidate hcandidate item hitem
      rcases List.mem_cons.mp hcandidate with rfl | htail
      · rcases List.mem_cons.mp hitem with rfl | hitem
        · exact hzero
        · exact ih gap List.mem_cons_self item hitem
      · exact ih candidate (List.mem_cons_of_mem gap htail) item hitem
  | @positive piece pieces gap gaps partials hpos rest ih =>
      intro candidate hcandidate item hitem
      rcases List.mem_cons.mp hcandidate with rfl | hcandidate
      · simp at hitem
      · exact ih candidate hcandidate item hitem

/-- 每个部分片都具有正缺口。 -/
theorem partials_positive
    (partition : ExactPieceGapPartition pieces gaps partials) :
    ∀ piece ∈ partials, 1 ≤ piece.deficit := by
  induction partition with
  | nil => simp
  | full hzero rest ih => exact ih
  | @positive piece pieces gap gaps partials hpos rest ih =>
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hpos
      · exact ih item htail

/-- 原列表中的零缺口片数就是全部 gap 长度之和。 -/
theorem full_count
    (partition : ExactPieceGapPartition pieces gaps partials) :
    deficitFullCount (pieces.map ComponentIntervalPiece.deficit) =
      (gaps.map List.length).sum := by
  induction partition with
  | nil => simp [deficitFullCount]
  | full hzero rest ih =>
      simp [deficitFullCount, hzero, ih]
      omega
  | @positive piece pieces gap gaps partials hpos rest ih =>
      have hne : piece.deficit ≠ 0 := by omega
      simp [deficitFullCount, hne, ih]

/-- 单位缺口计数完全由部分片列表给出。 -/
theorem unit_count
    (partition : ExactPieceGapPartition pieces gaps partials) :
    deficitUnitCount (pieces.map ComponentIntervalPiece.deficit) =
      (partials.map fun piece => unitIndicator piece.deficit).sum := by
  induction partition with
  | nil => simp [deficitUnitCount]
  | full hzero rest ih =>
      simp [deficitUnitCount, unitIndicator, hzero, ih]
  | positive hpos rest ih =>
      simp [deficitUnitCount, unitIndicator, ih]

/-- 至少二缺口计数完全由部分片列表给出。 -/
theorem large_count
    (partition : ExactPieceGapPartition pieces gaps partials) :
    deficitLargeCount (pieces.map ComponentIntervalPiece.deficit) =
      (partials.map fun piece => largeIndicator piece.deficit).sum := by
  induction partition with
  | nil => simp [deficitLargeCount]
  | full hzero rest ih =>
      simp [deficitLargeCount, largeIndicator, hzero, ih]
  | positive hpos rest ih =>
      simp [deficitLargeCount, largeIndicator, ih]

/-- 总缺口完全由部分片列表给出。 -/
theorem total_deficit
    (partition : ExactPieceGapPartition pieces gaps partials) :
    (pieces.map ComponentIntervalPiece.deficit).sum =
      (partials.map ComponentIntervalPiece.deficit).sum := by
  induction partition with
  | nil => simp
  | full hzero rest ih => simp [hzero, ih]
  | positive hpos rest ih => simp [ih]

/-- 部分片按单位缺口和至少二缺口精确分类。 -/
theorem partial_classification
    (partition : ExactPieceGapPartition pieces gaps partials) :
    ∀ piece ∈ partials,
      unitIndicator piece.deficit + largeIndicator piece.deficit = 1 := by
  intro piece hmem
  have hpos := partition.partials_positive piece hmem
  by_cases hunit : piece.deficit = 1
  · simp [unitIndicator, largeIndicator, hunit]
  · have hlarge : 2 ≤ piece.deficit := by omega
    simp [unitIndicator, largeIndicator, hunit, hlarge]

end ExactPieceGapPartition

end PreimageChain

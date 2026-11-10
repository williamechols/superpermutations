import PreimageChain.FullGapRunStable
import PreimageChain.GapGeometryAssembly

/-!
# 满片列表的真实游程提升

本模块保留后续规范 gap 证明使用的接口，并直接复用已经由 Lean 内核验证的
`FullGapRunStable` 实现。这样避免维护两份等价的递归列表证明。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

/-- 两个实际片首尾相接，且公共接缝权重恰为三。 -/
abbrev PieceExactJoin (left right : ComponentIntervalPiece p) : Prop :=
  ExactPieceAdjacent left right

/-- 列表中每对相邻元素满足关系 `R`。 -/
abbrev AdjacentList {α : Type} (R : α → α → Prop) (xs : List α) : Prop :=
  Adjacent R xs

namespace AdjacentList

/-- 逐合法下标的相邻关系合成为 `AdjacentList`。 -/
theorem of_get {α : Type} {R : α → α → Prop} {xs : List α}
    (hget : ∀ i, (hi : i + 1 < xs.length) → R xs[i] xs[i + 1]) :
    AdjacentList R xs := by
  exact Adjacent.of_get hget

/-- `AdjacentList` 可在任意合法相邻下标处取出关系。 -/
theorem get {α : Type} {R : α → α → Prop} {xs : List α}
    (hadj : AdjacentList R xs) (i : ℕ) (hi : i + 1 < xs.length) :
    R xs[i] xs[i + 1] := by
  exact Adjacent.get hadj i hi

end AdjacentList

/-- 精确权三片链的原始片列表处处满足 `PieceExactJoin`。 -/
theorem exactWeightThreeChain_adjacent
    (chain : ExactWeightThreePieceChain p) :
    AdjacentList PieceExactJoin chain.pieces := by
  exact exactChain_pieces_adjacent chain

/--
任意非空、逐片满且精确权三相接的实际片列表构成一条真实满游程。
-/
theorem fullPieceList_isRun
    (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (pieces : List (ComponentIntervalPiece p))
    (hne : pieces ≠ [])
    (hfull : ∀ piece ∈ pieces, piece.deficit = 0)
    (hadj : AdjacentList PieceExactJoin pieces) :
    WeightThreeFullRun p (pieces.head hne).start pieces.length := by
  exact fullPieceList_isWeightThreeRun hk hp pieces hne hfull hadj

end PreimageChain

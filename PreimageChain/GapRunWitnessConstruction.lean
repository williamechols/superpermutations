import PreimageChain.FullGapRun

/-!
# 从规范分解自动构造真实 gap 游程与边界证书

本模块证明规范 gap/partial 分解严格保留原片链顺序。由原链的逐相邻接缝证书，
自动得到每条 gap 的内部邻接、左右边界和端点坐标。除链首非终端满游程界外，
`ExactPieceGapRunWitness` 的其余字段全部在这里无条件生成。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

/-- 按 gap--partial--gap 的顺序重新交织片列表。 -/
def interleavePieceGaps {α : Type} : List (List α) → List α → List α
  | [], partials => partials
  | gaps, [] => gaps.flatten
  | gap :: gaps, part :: partials =>
      gap ++ part :: interleavePieceGaps gaps partials

/-- 规范分解交织后精确还原源列表。 -/
theorem ExactPieceGapPartition.interleave_eq
    {pieces : List (ComponentIntervalPiece p)} {gaps partials}
    (partition : ExactPieceGapPartition pieces gaps partials) :
    interleavePieceGaps gaps partials = pieces := by
  induction partition with
  | nil => rfl
  | @full piece pieces gap gaps partials hzero rest ih =>
      cases partials <;>
        simpa [interleavePieceGaps] using congrArg (piece :: ·) ih
  | @positive piece pieces gap gaps partials hpos rest ih =>
      simpa [interleavePieceGaps] using congrArg (piece :: ·) ih

namespace AdjacentList

/-- 相邻关系传递到列表尾部。 -/
theorem tail {α : Type} {R : α → α → Prop} {xs : List α}
    (hadj : AdjacentList R xs) : AdjacentList R xs.tail := by
  cases xs with
  | nil => simp [AdjacentList, Adjacent]
  | cons x xs =>
      cases xs with
      | nil => simp [AdjacentList, Adjacent]
      | cons y ys => exact hadj.2

/-- 相邻关系传递到任意 drop 后缀。 -/
theorem drop {α : Type} {R : α → α → Prop} {xs : List α}
    (hadj : AdjacentList R xs) (n : ℕ) :
    AdjacentList R (xs.drop n) := by
  induction n generalizing xs with
  | zero => simpa using hadj
  | succ n ih =>
      cases xs with
      | nil => simp [AdjacentList, Adjacent]
      | cons x xs =>
          simpa [List.drop_succ_cons] using ih (tail hadj)

/-- 相邻关系传递到任意 take 前缀。 -/
theorem take {α : Type} {R : α → α → Prop} {xs : List α}
    (hadj : AdjacentList R xs) (n : ℕ) :
    AdjacentList R (xs.take n) := by
  induction n generalizing xs with
  | zero => simp [AdjacentList, Adjacent]
  | succ n ih =>
      cases xs with
      | nil => simp [AdjacentList, Adjacent]
      | cons x xs =>
          cases xs with
          | nil => simp [AdjacentList, Adjacent]
          | cons y ys =>
              cases n with
              | zero => simp [AdjacentList, Adjacent]
              | succ n =>
                  change R x y ∧ AdjacentList R ((y :: ys).take (n + 1))
                  exact ⟨hadj.1, ih hadj.2⟩

/-- 非空前缀的末项与其后第一项保持相邻关系。 -/
theorem getLast_rel_next {α : Type} {R : α → α → Prop}
    (xs : List α) (y : α) (ys : List α) (hne : xs ≠ [])
    (hadj : AdjacentList R (xs ++ y :: ys)) :
    R (xs.getLast hne) y := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
      cases xs with
      | nil => simpa [AdjacentList, Adjacent] using hadj.1
      | cons z zs =>
          have htail : AdjacentList R ((z :: zs) ++ y :: ys) := hadj.2
          simpa using ih (by simp) htail

/-- 一个元素与其后非空列表的首项保持相邻关系。 -/
theorem rel_head_next {α : Type} {R : α → α → Prop}
    (x : α) (xs ys : List α) (hne : xs ≠ [])
    (hadj : AdjacentList R (x :: xs ++ ys)) :
    R x (xs.head hne) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons y ys' => simpa [AdjacentList] using hadj.1

end AdjacentList

private theorem interleave_drop_first
    {α : Type} (gap : List α) (gaps : List (List α))
    (part : α) (partials : List α) :
    (interleavePieceGaps (gap :: gaps) (part :: partials)).drop
        (gap.length + 1) = interleavePieceGaps gaps partials := by
  simp [interleavePieceGaps]

private theorem interleave_drop_gap
    {α : Type} (gap : List α) (gaps : List (List α))
    (part : α) (partials : List α) :
    (interleavePieceGaps (gap :: gaps) (part :: partials)).drop gap.length =
      part :: interleavePieceGaps gaps partials := by
  simp [interleavePieceGaps]

private theorem interleave_take_gap
    {α : Type} (gap : List α) (gaps : List (List α))
    (part : α) (partials : List α) :
    (interleavePieceGaps (gap :: gaps) (part :: partials)).take gap.length = gap := by
  simp [interleavePieceGaps]

private theorem interleave_head_of_first_gap
    {α : Type} (gap : List α) (gaps : List (List α))
    (partials : List α) (hne : gap ≠ []) :
    (interleavePieceGaps (gap :: gaps) partials).head (by
      cases partials <;> simp [interleavePieceGaps, hne]) = gap.head hne := by
  cases partials <;> simp [interleavePieceGaps, hne]

/-- 有效布局中的每条 gap 都继承原链的相邻关系。 -/
theorem gaps_adjacent_of_interleave
    {α : Type} {R : α → α → Prop}
    (gaps : List (List α)) (partials : List α)
    (hlen : gaps.length = partials.length + 1)
    (hadj : AdjacentList R (interleavePieceGaps gaps partials)) :
    ∀ gap ∈ gaps, AdjacentList R gap := by
  induction partials generalizing gaps with
  | nil =>
      have hgaps : ∃ gap, gaps = [gap] := by
        cases gaps with
        | nil => simp at hlen
        | cons gap tail =>
            cases tail with
            | nil => exact ⟨gap, rfl⟩
            | cons next tail => simp at hlen
      obtain ⟨gap, rfl⟩ := hgaps
      intro candidate hcandidate
      simp at hcandidate
      subst candidate
      simpa [interleavePieceGaps] using hadj
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLength : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          have hgapAdj : AdjacentList R gap := by
            have htaken := hadj.take gap.length
            simpa [interleave_take_gap] using htaken
          have htailAdj : AdjacentList R
              (interleavePieceGaps gaps partials) := by
            have hdropped := hadj.drop (gap.length + 1)
            simpa [interleave_drop_first] using hdropped
          have ihTail := ih gaps htailLength htailAdj
          intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | htail
          · exact hgapAdj
          · exact ihTail candidate htail

/-- 第 `i` 条非空 gap 的末片与第 `i` 个部分片精确权三相接。 -/
theorem rightBoundary_of_interleave
    {α : Type} {R : α → α → Prop}
    (gaps : List (List α)) (partials : List α)
    (hlen : gaps.length = partials.length + 1)
    (hadj : AdjacentList R (interleavePieceGaps gaps partials)) :
    ∀ i, (hi : i < partials.length) → (hne : gaps[i] ≠ []) →
      R (gaps[i].getLast hne) partials[i] := by
  induction partials generalizing gaps with
  | nil => intro i hi; simp at hi
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLength : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          intro i hi hne
          cases i with
          | zero =>
              simpa [interleavePieceGaps] using
                AdjacentList.getLast_rel_next gap part
                  (interleavePieceGaps gaps partials) hne hadj
          | succ i =>
              have htailAdj : AdjacentList R
                  (interleavePieceGaps gaps partials) := by
                have hdropped := hadj.drop (gap.length + 1)
                simpa [interleave_drop_first] using hdropped
              have hi' : i < partials.length := by simpa using hi
              simpa only [List.getElem_cons_succ] using
                ih gaps htailLength htailAdj i hi' hne

/-- 第 `i` 个部分片与第 `i+1` 条非空 gap 精确权三相接。 -/
theorem afterPartialBoundary_of_interleave
    {α : Type} {R : α → α → Prop}
    (gaps : List (List α)) (partials : List α)
    (hlen : gaps.length = partials.length + 1)
    (hadj : AdjacentList R (interleavePieceGaps gaps partials)) :
    ∀ i, (hi : i < partials.length) → (hne : gaps[i + 1] ≠ []) →
      R partials[i] (gaps[i + 1].head hne) := by
  induction partials generalizing gaps with
  | nil => intro i hi; simp at hi
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLength : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          intro i hi hne
          cases i with
          | zero =>
              cases gaps with
              | nil => simp at htailLength
              | cons next more =>
                  have hdrop : AdjacentList R
                      (part :: interleavePieceGaps (next :: more) partials) := by
                    have hdropped := AdjacentList.drop hadj gap.length
                    simpa [interleave_drop_gap] using hdropped
                  cases next with
                  | nil => simp at hne
                  | cons y ys =>
                      have hrel : R part y := by
                        cases partials <;>
                          simpa [interleavePieceGaps, AdjacentList, Adjacent] using hdrop.1
                      simpa using hrel
          | succ i =>
              have htailAdj : AdjacentList R
                  (interleavePieceGaps gaps partials) := by
                have hdropped := hadj.drop (gap.length + 1)
                simpa [interleave_drop_first] using hdropped
              have hi' : i < partials.length := by simpa using hi
              simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one,
                Nat.add_assoc] using
                ih gaps htailLength htailAdj i hi' hne

/-- 满片列表的最后终点坐标。 -/
theorem fullPieceList_last_stop_eq
    (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (pieces : List (ComponentIntervalPiece p))
    (hne : pieces ≠ [])
    (hfull : ∀ piece ∈ pieces, piece.deficit = 0)
    (hadj : AdjacentList PieceExactJoin pieces) :
    (pieces.getLast hne).stop =
      (pieces.head hne).start + pieces.length * (k - 1) := by
  induction pieces with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
      cases rest with
      | nil =>
          simpa using fullPiece_stop_eq hk hp first
            (hfull first List.mem_cons_self)
      | cons second tail =>
          have hadjHead : PieceExactJoin first second := hadj.1
          have hadjTail : AdjacentList PieceExactJoin (second :: tail) := hadj.2
          have hfullTail : ∀ piece ∈ second :: tail, piece.deficit = 0 := by
            intro piece hmem
            exact hfull piece (List.mem_cons_of_mem first hmem)
          have htail := ih (by simp) hfullTail hadjTail
          have htail' :
              ((second :: tail).getLast (by simp)).stop =
                second.start + (second :: tail).length * (k - 1) := by
            simpa only [List.head_cons] using htail
          have hfirstStop := fullPiece_stop_eq hk hp first
            (hfull first List.mem_cons_self)
          have hsecondStart : second.start = first.start + (k - 1) := by
            rw [← hfirstStop, hadjHead.1]
          simp only [List.getLast_cons (by simp : second :: tail ≠ []),
            List.head_cons, List.length_cons]
          rw [htail', hsecondStart]
          simp only [List.length_cons]
          ring

/--
给定链首非终端满游程界，规范分解自动生成完整 `ExactPieceGapRunWitness`。
-/
def ExactPieceGapPartition.toRunWitness
    (hk : 4 ≤ k) {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (hp : p.StronglyExitless)
    (partition : ExactPieceGapPartition chain.pieces gaps partials)
    (leadingBound : 0 < partials.length →
      (gaps[0]'(by rw [partition.gaps_length]; omega)).length ≤ k - 3) :
    ExactPieceGapRunWitness partition where
  gapRun := by
    intro i hi hne
    have hgapAdj := gaps_adjacent_of_interleave gaps partials
      partition.gaps_length (by
        rw [partition.interleave_eq]
        exact exactWeightThreeChain_adjacent chain)
      gaps[i] (List.getElem_mem hi)
    exact fullPieceList_isRun hk hp gaps[i] hne
      (partition.gaps_all_full gaps[i] (List.getElem_mem hi)) hgapAdj
  leftJoin := by
    intro i hi hiPrev hi1 hne
    have hafter := afterPartialBoundary_of_interleave gaps partials
      partition.gaps_length (by
        rw [partition.interleave_eq]
        exact exactWeightThreeChain_adjacent chain)
      (i - 1) hiPrev (by simpa [Nat.sub_add_cancel hi1] using hne)
    have hidx : i - 1 + 1 = i := Nat.sub_add_cancel hi1
    rcases hafter with ⟨hstop, hseam⟩
    constructor
    · simpa [hidx] using hstop
    · simpa [hidx] using hseam
  rightJoin := by
    intro i hi hiGap hne
    exact rightBoundary_of_interleave gaps partials partition.gaps_length
      (by
        rw [partition.interleave_eq]
        exact exactWeightThreeChain_adjacent chain)
      i hi hne
  rightCoordinate := by
    intro i hi hiGap hne
    have hboundary := rightBoundary_of_interleave gaps partials
      partition.gaps_length (by
        rw [partition.interleave_eq]
        exact exactWeightThreeChain_adjacent chain)
      i hi hne
    have hgapAdj := gaps_adjacent_of_interleave gaps partials
      partition.gaps_length (by
        rw [partition.interleave_eq]
        exact exactWeightThreeChain_adjacent chain)
      gaps[i] (List.getElem_mem hiGap)
    have hend := fullPieceList_last_stop_eq hk hp gaps[i] hne
      (partition.gaps_all_full gaps[i] (List.getElem_mem hiGap)) hgapAdj
    rw [← hboundary.1, hend]
  leadingGapBound := by
    intro hpartials h0
    simpa using leadingBound hpartials

end PreimageChain

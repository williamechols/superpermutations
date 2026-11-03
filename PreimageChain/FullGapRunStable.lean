import PreimageChain.GapGeometryAssembly

/-!
# 连续满片列表到真实权三满游程
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

/-- 实际片的精确权三邻接。 -/
def ExactPieceAdjacent
    (left right : ComponentIntervalPiece p) : Prop :=
  left.stop = right.start ∧ Hunter.ProofsLedger.bw p right.start = 3

/-- 列表逐相邻满足关系。 -/
def Adjacent {α : Type*} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => R x y ∧ Adjacent R (y :: xs)

namespace Adjacent

/-- 合法相邻下标证书产生逐相邻关系。 -/
theorem of_get {α : Type*} {R : α → α → Prop} {xs : List α}
    (hget : ∀ i, (hi : i + 1 < xs.length) → R xs[i] xs[i + 1]) :
    Adjacent R xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      cases xs with
      | nil => trivial
      | cons y ys =>
          change R x y ∧ Adjacent R (y :: ys)
          constructor
          · simpa using hget 0 (by simp)
          · apply ih
            intro i hi
            have hall := hget (i + 1) (by
              simp only [List.length_cons] at hi ⊢
              omega)
            simpa only [List.getElem_cons_succ, Nat.add_assoc] using hall

/-- 逐相邻关系在合法下标处取值。 -/
theorem get {α : Type*} {R : α → α → Prop} {xs : List α}
    (hadj : Adjacent R xs) (i : ℕ) (hi : i + 1 < xs.length) :
    R xs[i] xs[i + 1] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases xs with
      | nil => simp at hi
      | cons y ys =>
          change R x y ∧ Adjacent R (y :: ys) at hadj
          cases i with
          | zero => simpa using hadj.1
          | succ i =>
              have hi' : i + 1 < (y :: ys).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              simpa only [List.getElem_cons_succ] using ih hadj.2 i hi'

end Adjacent

/-- 原精确权三链的片列表逐邻接。 -/
theorem exactChain_pieces_adjacent
    (chain : ExactWeightThreePieceChain p) :
    Adjacent ExactPieceAdjacent chain.pieces := by
  apply Adjacent.of_get
  intro i hi
  exact ⟨chain.consecutive i hi, chain.seamWeight i hi⟩

/-- 满片的右端坐标。 -/
theorem fullPiece_stop_eq
    (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) (hfull : piece.deficit = 0) :
    piece.stop = piece.start + (k - 1) := by
  have hcap := ComponentIntervalPiece.size_add_deficit hk hp piece
  rw [hfull, Nat.add_zero] at hcap
  simp only [ComponentIntervalPiece.size, actualPieceSize] at hcap
  have hlt := piece.valid.nonempty
  omega

/--
任意非空、逐片满且精确权三相接的实际片列表构成真实满游程。
-/
theorem fullPieceList_isWeightThreeRun
    (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (pieces : List (ComponentIntervalPiece p))
    (hne : pieces ≠ [])
    (hfull : ∀ piece ∈ pieces, piece.deficit = 0)
    (hadj : Adjacent ExactPieceAdjacent pieces) :
    WeightThreeFullRun p (pieces.head hne).start pieces.length := by
  induction pieces with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hfirstFull := hfull first List.mem_cons_self
          have hinterval := fullIntervalPiece_of_actual_deficit_zero hk hp
            first.valid hfirstFull
          have hstop := fullPiece_stop_eq hk hp first hfirstFull
          refine
            { inRange := ?_
              doors := ?_
              seams := ?_ }
          · simp only [List.length_cons, List.length_nil, Nat.zero_add,
              Nat.one_mul, List.head_cons]
            rw [← hstop, component_numVerts_eq (by omega) hp]
            exact Nat.mul_le_mul_left k first.valid.stopLe
          · intro j r hj hr1 hr2
            have hj0 : j = 0 := by simp at hj; omega
            subst j
            simpa only [List.head_cons, Nat.zero_mul, Nat.add_zero] using
              hinterval.doors r hr1 hr2
          · intro c hc1 hcm
            simp only [List.length_cons, List.length_nil, Nat.add_zero] at hcm
            omega
      | cons second tail =>
          have hhead : ExactPieceAdjacent first second := hadj.1
          have hadjTail : Adjacent ExactPieceAdjacent (second :: tail) := hadj.2
          have hfullTail : ∀ piece ∈ second :: tail, piece.deficit = 0 := by
            intro piece hmem
            exact hfull piece (List.mem_cons_of_mem first hmem)
          have hrunTail := ih (by simp) hfullTail hadjTail
          have hfirstFull := hfull first List.mem_cons_self
          have hfirstInterval := fullIntervalPiece_of_actual_deficit_zero hk hp
            first.valid hfirstFull
          have hstop := fullPiece_stop_eq hk hp first hfirstFull
          have hsecondStart : second.start = first.start + (k - 1) := by
            rw [← hstop, hhead.1]
          let m := (second :: tail).length
          have hlength : (first :: second :: tail).length = m + 1 := by
            simp [m]
          refine
            { inRange := ?_
              doors := ?_
              seams := ?_ }
          · simp only [List.head_cons]
            rw [hlength]
            have hcoord : first.start + (m + 1) * (k - 1) =
                second.start + m * (k - 1) := by
              rw [hsecondStart]
              ring
            rw [hcoord]
            exact hrunTail.inRange
          · intro j r hj hr1 hr2
            simp only [List.head_cons]
            by_cases hj0 : j = 0
            · subst j
              simpa using hfirstInterval.doors r hr1 hr2
            · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
                ⟨j - 1, by omega⟩
              have hjTail : j' < m := by
                rw [hlength] at hj
                omega
              have hcoord : first.start + (j' + 1) * (k - 1) + r =
                  second.start + j' * (k - 1) + r := by
                rw [hsecondStart]
                ring
              rw [hcoord]
              simpa only [List.head_cons] using
                hrunTail.doors j' r hjTail hr1 hr2
          · intro c hc1 hcm
            simp only [List.head_cons]
            by_cases hc : c = 1
            · subst c
              have hcoord : first.start + 1 * (k - 1) = second.start := by
                simpa using hsecondStart.symm
              rw [hcoord]
              exact hhead.2
            · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 :=
                ⟨c - 1, by omega⟩
              have hc'1 : 1 ≤ c' := by omega
              have hc'M : c' < m := by
                rw [hlength] at hcm
                omega
              have hcoord : first.start + (c' + 1) * (k - 1) =
                  second.start + c' * (k - 1) := by
                rw [hsecondStart]
                ring
              rw [hcoord]
              simpa only [List.head_cons] using
                hrunTail.seams c' hc'1 hc'M

end PreimageChain

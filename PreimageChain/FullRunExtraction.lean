import PreimageChain.DeficitRuns

/-!
# 从精确权三片链提取连续满片游程

本模块把片列表中连续的零缺口片段提升为真实 `WeightThreeFullRun`。这样，
`DeficitGapPartition` 给出的每个零缺口游程都可以直接调用已经形式化的门户局部几何。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- 连续满片段中第 `j` 片的起点坐标。 -/
theorem exactChain_fullSegment_start_eq
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p)
    (base M j : ℕ)
    (hM : 1 ≤ M)
    (hsegment : base + M ≤ chain.pieces.length)
    (hfull : ∀ q (hq : q < M),
      (chain.pieces[base + q]'(by omega)).deficit = 0)
    (hj : j < M) :
    (chain.pieces[base + j]).start =
      (chain.pieces[base]).start + j * (k - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjM : j < M := by omega
      have hprev : base + j < chain.pieces.length := by omega
      have hnext : base + j + 1 < chain.pieces.length := by omega
      have hcoordinate := ih hjM
      have hjoin := chain.consecutive (base + j) (by omega)
      have hcap := ComponentIntervalPiece.size_add_deficit hk hp
        chain.pieces[base + j]
      have hzero := hfull j hjM
      rw [hzero, Nat.add_zero] at hcap
      have hstop :
          (chain.pieces[base + j]).stop =
            (chain.pieces[base + j]).start + (k - 1) := by
        simp only [ComponentIntervalPiece.size, actualPieceSize] at hcap
        have hnonempty := (chain.pieces[base + j]).valid.nonempty
        omega
      have hindex : base + (j + 1) = base + j + 1 := by omega
      calc
        (chain.pieces[base + (j + 1)]).start =
            (chain.pieces[base + j + 1]).start := by
              simp only [hindex]
        _ = (chain.pieces[base + j]).stop := by symm; exact hjoin
        _ = (chain.pieces[base + j]).start + (k - 1) := hstop
        _ = (chain.pieces[base]).start + (j + 1) * (k - 1) := by
          rw [hcoordinate]
          ring

/-- 任意连续的正长度满片段自动组成 `WeightThreeFullRun`。 -/
theorem exactChain_fullSegment_isRun
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p)
    (base M : ℕ)
    (hM : 1 ≤ M)
    (hsegment : base + M ≤ chain.pieces.length)
    (hfull : ∀ q (hq : q < M),
      (chain.pieces[base + q]'(by omega)).deficit = 0) :
    WeightThreeFullRun p (chain.pieces[base]).start M := by
  have hbase : base < chain.pieces.length := by omega
  have hlast : base + (M - 1) < chain.pieces.length := by omega
  have hlastFull := hfull (M - 1) (by omega)
  have hlastCap := ComponentIntervalPiece.size_add_deficit hk hp
    chain.pieces[base + (M - 1)]
  rw [hlastFull, Nat.add_zero] at hlastCap
  have hlastStop :
      (chain.pieces[base + (M - 1)]).stop =
        (chain.pieces[base + (M - 1)]).start + (k - 1) := by
    simp only [ComponentIntervalPiece.size, actualPieceSize] at hlastCap
    have hnonempty := (chain.pieces[base + (M - 1)]).valid.nonempty
    omega
  have hlastStart := exactChain_fullSegment_start_eq hk hp chain
    base M (M - 1) hM hsegment hfull (by omega)
  have hMsplit : M - 1 + 1 = M := by omega
  have hend :
      (chain.pieces[base]).start + M * (k - 1) =
        (chain.pieces[base + (M - 1)]).stop := by
    rw [hlastStop, hlastStart]
    calc
      (chain.pieces[base]).start + M * (k - 1) =
          (chain.pieces[base]).start + ((M - 1) + 1) * (k - 1) := by
            rw [hMsplit]
      _ = (chain.pieces[base]).start + (M - 1) * (k - 1) +
          (k - 1) := by ring
  refine
    { inRange := ?_
      doors := ?_
      seams := ?_ }
  · rw [component_numVerts_eq (by omega) hp, hend]
    exact Nat.mul_le_mul_left k
      (chain.pieces[base + (M - 1)]).valid.stopLe
  · intro j r hjM hr1 hr2
    have hzero := hfull j hjM
    have hpiece := fullIntervalPiece_of_actual_deficit_zero hk hp
      (chain.pieces[base + j]).valid hzero
    have hcoord := exactChain_fullSegment_start_eq hk hp chain
      base M j hM hsegment hfull hjM
    rw [← hcoord]
    simpa [Nat.add_assoc] using hpiece.doors r hr1 hr2
  · intro c hc1 hcM
    have hglobal : base + (c - 1) + 1 < chain.pieces.length := by omega
    have hseam := chain.seamWeight (base + (c - 1)) hglobal
    have hcoord := exactChain_fullSegment_start_eq hk hp chain
      base M c hM hsegment hfull hcM
    have hindex : base + (c - 1) + 1 = base + c := by omega
    have hbc : base + c < chain.pieces.length := by omega
    have hfin :
        (⟨base + (c - 1) + 1, hglobal⟩ : Fin chain.pieces.length) =
          ⟨base + c, hbc⟩ := Fin.ext hindex
    rw [hfin] at hseam
    have hcoord' :
        (chain.pieces[base + c]'hbc).start =
          (chain.pieces[base]).start + c * (k - 1) := by
      simpa only using hcoord
    rw [← hcoord']
    exact hseam

end PreimageChain

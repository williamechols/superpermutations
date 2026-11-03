import PreimageChain.ActualGapProfile

/-!
# 真实 gap 游程和边界到四项局部几何

除链首非终端满游程界外，本文已有的路径级定理已经足以自动生成
`ExactPieceGapGeometry`。本模块把这一装配写成一个严格接口，使最后一个新的局部
坐标引理与其后的纯组合求和完全隔离。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

private theorem natListAt_eq_getElem
    (fallback : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    natListAt fallback xs i = xs[i] := by
  simp [natListAt, List.getElem?_eq_getElem hi]

private theorem gapLength_at
    (gaps : List (List (ComponentIntervalPiece p)))
    (i : ℕ) (hi : i < gaps.length) :
    natListAt 0 (gapLengths gaps) i = gaps[i].length := by
  rw [natListAt_eq_getElem 0 (gapLengths gaps) i (by simpa [gapLengths] using hi)]
  simp [gapLengths]

private theorem partialDeficit_at
    (partials : List (ComponentIntervalPiece p))
    (i : ℕ) (hi : i < partials.length) :
    natListAt 1 (partialDeficits partials) i = partials[i].deficit := by
  rw [natListAt_eq_getElem 1 (partialDeficits partials) i
    (by simpa [partialDeficits] using hi)]
  simp [partialDeficits]

private theorem positiveIndicator_eq_one_iff (n : ℕ) :
    positiveIndicator n = 1 ↔ 0 < n := by
  simp [positiveIndicator]

/--
每条非空 gap 已被提升为真实 `WeightThreeFullRun`，并记录它与相邻部分片的
真实接缝坐标。`leadingGapBound` 是尚需由六方向碰撞证明的唯一新局部输入。
-/
structure ExactPieceGapRunWitness
    {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (partition : ExactPieceGapPartition chain.pieces gaps partials) where
  gapRun : ∀ i, (hi : i < gaps.length) → (hne : gaps[i] ≠ []) →
    WeightThreeFullRun p (gaps[i].head hne).start gaps[i].length
  leftJoin : ∀ i, (hiGap : i < gaps.length) →
      (hiPrev : i - 1 < partials.length) → 1 ≤ i →
      (hne : gaps[i] ≠ []) →
    partials[i - 1].stop = (gaps[i].head hne).start ∧
      Hunter.ProofsLedger.bw p (gaps[i].head hne).start = 3
  rightJoin : ∀ i, (hiPartial : i < partials.length) →
      (hiGap : i < gaps.length) → (hne : gaps[i] ≠ []) →
    (gaps[i].getLast hne).stop = partials[i].start ∧
      Hunter.ProofsLedger.bw p partials[i].start = 3
  rightCoordinate : ∀ i, (hiPartial : i < partials.length) →
      (hiGap : i < gaps.length) → (hne : gaps[i] ≠ []) →
    partials[i].start =
      (gaps[i].head hne).start + gaps[i].length * (k - 1)
  leadingGapBound : 0 < partials.length → (h0 : 0 < gaps.length) →
    gaps[0].length ≤ k - 3

namespace ExactPieceGapRunWitness

/-- 已有路径几何加链首界自动生成四项局部容量几何。 -/
def toGeometry
    (hk : 5 ≤ k) {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    {partition : ExactPieceGapPartition chain.pieces gaps partials}
    (hp : p.StronglyExitless)
    (witness : ExactPieceGapRunWitness partition) :
    ExactPieceGapGeometry gaps partials where
  allFullBound := by
    intro hzero
    have hgapLength : gaps.length = 1 := by
      have := partition.gaps_length
      simpa [hzero] using this
    have h0 : 0 < gaps.length := by omega
    rw [gapLength_at gaps 0 h0]
    by_cases hne : gaps[0] = []
    · simp [hne]
    · exact weightThreeFullRun_length_le (by omega : 3 ≤ k) hp.1
        (witness.gapRun 0 h0 hne)
  partialGapBound := by
    intro hpartials i hi
    have hgapsLength := partition.gaps_length
    have hiGap : i < gaps.length := by omega
    rw [gapLength_at gaps i hiGap]
    by_cases hne : gaps[i] = []
    · simp [hne]
    · have hrun := witness.gapRun i hiGap hne
      by_cases hi0 : i = 0
      · subst i
        exact witness.leadingGapBound hpartials hiGap
      · have hiPred : i - 1 < partials.length := by omega
        have hleft := witness.leftJoin i hiGap hiPred (by omega) hne
        have hpartialPos := partition.partials_positive
          partials[i - 1] (List.getElem_mem hiPred)
        have hrun' : WeightThreeFullRun p partials[i - 1].stop gaps[i].length := by
          rw [hleft.1]
          exact hrun
        have hseam : Hunter.ProofsLedger.bw p partials[i - 1].stop = 3 := by
          rw [hleft.1]
          exact hleft.2
        exact actualPiece_followingFullRun_length_le (by omega : 4 ≤ k) hp
          partials[i - 1].valid hpartialPos hseam
          (List.length_pos_iff.mpr hne) hrun'
  unitOneSided := by
    intro j hj hunit
    have hgapsLength := partition.gaps_length
    have hjGap : j < gaps.length := by omega
    have hjNextGap : j + 1 < gaps.length := by omega
    rw [partialDeficit_at partials j hj] at hunit
    rw [gapLength_at gaps j hjGap,
      gapLength_at gaps (j + 1) hjNextGap]
    have hleftIndicator : positiveIndicator gaps[j].length ≤ 1 := by
      unfold positiveIndicator
      split <;> omega
    have hrightIndicator : positiveIndicator gaps[j + 1].length ≤ 1 := by
      unfold positiveIndicator
      split <;> omega
    by_contra hnot
    have hleftOne : positiveIndicator gaps[j].length = 1 := by omega
    have hrightOne : positiveIndicator gaps[j + 1].length = 1 := by omega
    have hleftPos : 0 < gaps[j].length :=
      (positiveIndicator_eq_one_iff _).mp hleftOne
    have hrightPos : 0 < gaps[j + 1].length :=
      (positiveIndicator_eq_one_iff _).mp hrightOne
    have hleftNe : gaps[j] ≠ [] := List.ne_nil_of_length_pos hleftPos
    have hrightNe : gaps[j + 1] ≠ [] := List.ne_nil_of_length_pos hrightPos
    let leftPiece := gaps[j].getLast hleftNe
    let unitPiece := partials[j]
    have hleftMem : leftPiece ∈ gaps[j] := by
      dsimp [leftPiece]
      exact List.getLast_mem hleftNe
    have hleftFull : leftPiece.deficit = 0 :=
      partition.gaps_all_full gaps[j] (List.getElem_mem hjGap)
        leftPiece hleftMem
    have hrightRun := witness.gapRun (j + 1) hjNextGap hrightNe
    have hleftBoundary := witness.rightJoin j hj hjGap hleftNe
    have hrightBoundaryRaw :=
      witness.leftJoin (j + 1) hjNextGap hj (by omega) hrightNe
    have hidx : j + 1 - 1 = j := by omega
    have hrightBoundary :
        partials[j].stop = (gaps[j + 1].head hrightNe).start ∧
          Hunter.ProofsLedger.bw p (gaps[j + 1].head hrightNe).start = 3 := by
      simpa only [hidx] using hrightBoundaryRaw
    have houtgoing : Hunter.ProofsLedger.bw p unitPiece.stop = 3 := by
      dsimp [unitPiece]
      rw [hrightBoundary.1]
      exact hrightBoundary.2
    have hrightRun' : WeightThreeFullRun p unitPiece.stop gaps[j + 1].length := by
      dsimp [unitPiece]
      rw [hrightBoundary.1]
      exact hrightRun
    exact actualUnitPiece_not_between_full_runs (by omega : 4 ≤ k) hp
      leftPiece.valid unitPiece.valid hleftFull hunit hleftBoundary.1
      hleftBoundary.2 houtgoing hrightPos hrightRun'
  internalLongThreshold := by
    intro i hi1 hiPartial hlength
    have hgapsLength := partition.gaps_length
    have hiGap : i < gaps.length := by omega
    have hiPrev : i - 1 < partials.length := by omega
    rw [partialDeficit_at partials (i - 1) hiPrev,
      partialDeficit_at partials i hiPartial]
    rw [gapLength_at gaps i hiGap] at hlength
    have hgapPos : 0 < gaps[i].length := by omega
    have hgapNe : gaps[i] ≠ [] := List.ne_nil_of_length_pos hgapPos
    have hrun := witness.gapRun i hiGap hgapNe
    have hleftBoundary := witness.leftJoin i hiGap hiPrev hi1 hgapNe
    have hrightBoundary := witness.rightJoin i hiPartial hiGap hgapNe
    have hcoordinate := witness.rightCoordinate i hiPartial hiGap hgapNe
    have hleftPos := partition.partials_positive partials[i - 1]
      (List.getElem_mem hiPrev)
    have hrightPos := partition.partials_positive partials[i]
      (List.getElem_mem hiPartial)
    have hrun' : WeightThreeFullRun p partials[i - 1].stop (k - 3) := by
      rw [← hlength, hleftBoundary.1]
      exact hrun
    have hleftSeam : Hunter.ProofsLedger.bw p partials[i - 1].stop = 3 := by
      rw [hleftBoundary.1]
      exact hleftBoundary.2
    have hjoin : partials[i].start =
        partials[i - 1].stop + (k - 3) * (k - 1) := by
      rw [hcoordinate, ← hlength, hleftBoundary.1]
    exact actualPieces_internalLongRun_deficit_threshold hk hp
      partials[i - 1].valid partials[i].valid hleftPos hrightPos
      hleftSeam hrun' hjoin hrightBoundary.2

end ExactPieceGapRunWitness

end PreimageChain

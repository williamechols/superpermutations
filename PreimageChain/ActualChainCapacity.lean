import PreimageChain.GapRunWitnessConstruction
import PreimageChain.MaximalRunCollision
import PreimageChain.StandardEndpointBudget

/-!
# 实际精确权三链的无条件容量证书

规范 gap/partial 分解的唯一外部输入是链首非终端满游程界。本模块用
`nonterminalWeightThreeFullRun_length_le` 自动生成该界，并证明证书的端点字段恰为
真实首、末满片指标。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ} {p : HPath k}

/-- 实际 interval piece 的起始块仍严格位于组件路径范围内。 -/
theorem componentIntervalPiece_start_inRange
    (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) :
    k * piece.start < p.numVerts := by
  rw [component_numVerts_eq hk hp]
  have hstart : piece.start < componentClassCount p :=
    lt_of_lt_of_le piece.valid.nonempty piece.valid.stopLe
  exact Nat.mul_lt_mul_of_pos_left hstart hk

/--
规范分解中，若存在首个部分片，则第一条满 gap 是非终端游程，故长度至多 `k-3`。
-/
theorem leading_gap_length_le
    (hk : 5 ≤ k) {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (hp : p.StronglyExitless)
    (partition : ExactPieceGapPartition chain.pieces gaps partials)
    (hpartials : 0 < partials.length) :
    (gaps[0]'(by rw [partition.gaps_length]; omega)).length ≤ k - 3 := by
  have hgap0 : 0 < gaps.length := by
    rw [partition.gaps_length]
    omega
  by_cases hne : gaps[0] = []
  · simp [hne]
  · have hadjInterleave : AdjacentList PieceExactJoin
        (interleavePieceGaps gaps partials) := by
      rw [partition.interleave_eq]
      exact exactWeightThreeChain_adjacent chain
    have hgapAdj : AdjacentList PieceExactJoin gaps[0] :=
      gaps_adjacent_of_interleave gaps partials partition.gaps_length
        hadjInterleave gaps[0] (List.getElem_mem hgap0)
    have hfull : ∀ piece ∈ gaps[0], piece.deficit = 0 :=
      partition.gaps_all_full gaps[0] (List.getElem_mem hgap0)
    have hrun : WeightThreeFullRun p (gaps[0].head hne).start gaps[0].length :=
      fullPieceList_isRun (by omega : 4 ≤ k) hp gaps[0] hne hfull hgapAdj
    have hboundary : PieceExactJoin (gaps[0].getLast hne) partials[0] :=
      rightBoundary_of_interleave gaps partials partition.gaps_length
        hadjInterleave 0 hpartials hne
    have hend := fullPieceList_last_stop_eq (by omega : 4 ≤ k) hp gaps[0]
      hne hfull hgapAdj
    have hcoordinate : partials[0].start =
        (gaps[0].head hne).start + gaps[0].length * (k - 1) := by
      rw [← hboundary.1, hend]
    have htargetRange :
        k * ((gaps[0].head hne).start + gaps[0].length * (k - 1)) <
          p.numVerts := by
      rw [← hcoordinate]
      exact componentIntervalPiece_start_inRange (by omega : 1 ≤ k) hp partials[0]
    have hseam : Hunter.ProofsLedger.bw p
        ((gaps[0].head hne).start + gaps[0].length * (k - 1)) = 3 := by
      rw [← hcoordinate]
      exact hboundary.2
    exact nonterminalWeightThreeFullRun_length_le (by omega : 4 ≤ k) hp.1
      hrun (List.length_pos_iff.mpr hne) htargetRange hseam

/-- 全满列表的首片指标恰为其非空指标。 -/
theorem firstNatValue_full_pieces
    (pieces : List (ComponentIntervalPiece p))
    (hfull : ∀ piece ∈ pieces, piece.deficit = 0) :
    firstNatValue actualPieceFullBit pieces = positiveIndicator pieces.length := by
  cases pieces with
  | nil => simp [firstNatValue, positiveIndicator]
  | cons piece pieces =>
      have hpFull := hfull piece List.mem_cons_self
      simp [firstNatValue, actualPieceFullBit, positiveIndicator, hpFull]

/-- 全满列表的末片指标同样恰为其非空指标。 -/
theorem lastNatValue_full_pieces
    (pieces : List (ComponentIntervalPiece p))
    (hfull : ∀ piece ∈ pieces, piece.deficit = 0) :
    lastNatValue actualPieceFullBit pieces = positiveIndicator pieces.length := by
  unfold lastNatValue
  have hrev : ∀ piece ∈ pieces.reverse, piece.deficit = 0 := by
    intro piece hmem
    exact hfull piece (by simpa using hmem)
  rw [firstNatValue_full_pieces pieces.reverse hrev, List.length_reverse]

/-- 右侧列表非空时，拼接不改变末值。 -/
theorem lastNatValue_append_of_right_ne_nil
    (f : α → ℕ) (left right : List α) (hright : right ≠ []) :
    lastNatValue f (left ++ right) = lastNatValue f right := by
  unfold lastNatValue
  rw [List.reverse_append]
  cases hrev : right.reverse with
  | nil =>
      have : right = [] := by
        apply List.reverse_injective
        simpa [hrev]
      exact False.elim (hright this)
  | cons x xs => simp [firstNatValue, hrev]

/-- 规范交织列表的首满片指标由第一条 gap 是否非空决定。 -/
theorem interleave_firstFullBit
    (gaps : List (List (ComponentIntervalPiece p)))
    (partials : List (ComponentIntervalPiece p))
    (hlen : gaps.length = partials.length + 1)
    (hfull : ∀ gap ∈ gaps, ∀ piece ∈ gap, piece.deficit = 0)
    (hpartial : ∀ piece ∈ partials, 1 ≤ piece.deficit) :
    firstNatValue actualPieceFullBit (interleavePieceGaps gaps partials) =
      positiveIndicator (natListAt 0 (gapLengths gaps) 0) := by
  induction partials generalizing gaps with
  | nil =>
      cases gaps with
      | nil => simp at hlen
      | cons gap tail =>
          have htail : tail = [] := by
            simp at hlen
            exact hlen
          subst tail
          simp only [interleavePieceGaps, List.flatten_singleton]
          have hgap := hfull gap List.mem_cons_self
          simpa [gapLengths, natListAt] using firstNatValue_full_pieces gap hgap
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLen : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          have hfullGap : ∀ piece ∈ gap, piece.deficit = 0 :=
            hfull gap List.mem_cons_self
          have hfullTail : ∀ tailGap ∈ gaps, ∀ piece ∈ tailGap,
              piece.deficit = 0 := by
            intro tailGap hmem piece hpMem
            exact hfull tailGap (List.mem_cons_of_mem gap hmem) piece hpMem
          have hpartialHead : 1 ≤ part.deficit :=
            hpartial part List.mem_cons_self
          have hpartialTail : ∀ piece ∈ partials, 1 ≤ piece.deficit := by
            intro piece hmem
            exact hpartial piece (List.mem_cons_of_mem part hmem)
          cases gap with
          | nil =>
              have hne : part.deficit ≠ 0 := by omega
              simp [interleavePieceGaps, gapLengths, natListAt, firstNatValue,
                actualPieceFullBit, positiveIndicator, hne]
          | cons first rest =>
              have hfirstFull := hfullGap first List.mem_cons_self
              simp [interleavePieceGaps, gapLengths, natListAt, firstNatValue,
                actualPieceFullBit, positiveIndicator, hfirstFull]

/-- 规范交织列表的末满片指标由最后一条 gap 是否非空决定。 -/
theorem interleave_lastFullBit
    (gaps : List (List (ComponentIntervalPiece p)))
    (partials : List (ComponentIntervalPiece p))
    (hlen : gaps.length = partials.length + 1)
    (hfull : ∀ gap ∈ gaps, ∀ piece ∈ gap, piece.deficit = 0)
    (hpartial : ∀ piece ∈ partials, 1 ≤ piece.deficit) :
    lastNatValue actualPieceFullBit (interleavePieceGaps gaps partials) =
      positiveIndicator (natListAt 0 (gapLengths gaps) partials.length) := by
  induction partials generalizing gaps with
  | nil =>
      cases gaps with
      | nil => simp at hlen
      | cons gap tail =>
          have htail : tail = [] := by
            simp at hlen
            exact hlen
          subst tail
          simp only [interleavePieceGaps, List.flatten_singleton]
          have hgap := hfull gap List.mem_cons_self
          simpa [gapLengths, natListAt] using lastNatValue_full_pieces gap hgap
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLen : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          have hfullTail : ∀ tailGap ∈ gaps, ∀ piece ∈ tailGap,
              piece.deficit = 0 := by
            intro tailGap hmem piece hpMem
            exact hfull tailGap (List.mem_cons_of_mem gap hmem) piece hpMem
          have hpartialHead : 1 ≤ part.deficit :=
            hpartial part List.mem_cons_self
          have hpartialTail : ∀ piece ∈ partials, 1 ≤ piece.deficit := by
            intro piece hmem
            exact hpartial piece (List.mem_cons_of_mem part hmem)
          let tailInterleave := interleavePieceGaps gaps partials
          have ihTail := ih gaps htailLen hfullTail hpartialTail
          by_cases htailNe : tailInterleave = []
          · have hpartialTailNil : partials = [] := by
              by_contra hne
              obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
              cases gaps with
              | nil => simp at htailLen
              | cons next more =>
                  simp [tailInterleave, interleavePieceGaps] at htailNe
            have hgapsSingle : gaps = [[]] := by
              subst partials
              have hlen1 : gaps.length = 1 := by simpa using htailLen
              obtain ⟨lastGap, rfl⟩ := List.length_eq_one_iff.mp hlen1
              simp [tailInterleave, interleavePieceGaps] at htailNe
              subst lastGap
              rfl
            subst partials
            subst gaps
            have hpartialNe : part.deficit ≠ 0 := by omega
            simp [tailInterleave, interleavePieceGaps, lastNatValue,
              firstNatValue, actualPieceFullBit, positiveIndicator,
              gapLengths, natListAt, hpartialNe]
          · have happ :
                interleavePieceGaps (gap :: gaps) (part :: partials) =
                  (gap ++ [part]) ++ tailInterleave := by
              simp [interleavePieceGaps, tailInterleave, List.append_assoc]
            rw [happ, lastNatValue_append_of_right_ne_nil _ _ _ htailNe,
              ihTail]
            simp [gapLengths, natListAt]

/-- 给定规范分解时，真实首、末满片指标等于 gap-profile 的端点字段。 -/
theorem partition_endpointFullCount_eq
    (hk : 5 ≤ k) {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (hp : p.StronglyExitless)
    (partition : ExactPieceGapPartition chain.pieces gaps partials) :
    let witness : ExactPieceGapRunWitness partition :=
      partition.toRunWitness (by omega : 4 ≤ k) hp
        (leading_gap_length_le hk hp partition)
    let geometry : ExactPieceGapGeometry gaps partials := witness.toGeometry hk hp
    let profile : ExactWeightThreeChainLocalProfile chain :=
      partition.toLocalProfile geometry
    (profile.toRunCertificate hk).endpointFullCount =
      chainFirstFullBit chain + chainLastFullBit chain := by
  dsimp
  have hfirst := interleave_firstFullBit gaps partials partition.gaps_length
    partition.gaps_all_full partition.partials_positive
  have hlast := interleave_lastFullBit gaps partials partition.gaps_length
    partition.gaps_all_full partition.partials_positive
  rw [partition.interleave_eq] at hfirst hlast
  change positiveIndicator (natListAt 0 (gapLengths gaps) 0) +
      positiveIndicator (natListAt 0 (gapLengths gaps) partials.length) =
    chainFirstFullBit chain + chainLastFullBit chain
  rw [← hfirst, ← hlast]
  rfl

/-- 链容量证书及其真实端点等式。 -/
structure ActualChainCapacityPackage
    (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) where
  certificate : ExactWeightThreeChainRunCertificate chain
  endpoint_eq : certificate.endpointFullCount =
    chainFirstFullBit chain + chainLastFullBit chain

/-- 任意实际精确权三片链都无条件产生容量证书与端点等式。 -/
noncomputable def actualChainCapacityPackage
    (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ActualChainCapacityPackage hk hp chain := by
  classical
  let hexists := ExactPieceGapPartition.exists_for chain.pieces
  let gaps := Classical.choose hexists
  let hpartials := Classical.choose_spec hexists
  let partials := Classical.choose hpartials
  let partition : ExactPieceGapPartition chain.pieces gaps partials :=
    Classical.choose_spec hpartials
  let witness : ExactPieceGapRunWitness partition :=
    partition.toRunWitness (by omega : 4 ≤ k) hp
      (leading_gap_length_le hk hp partition)
  let geometry : ExactPieceGapGeometry gaps partials := witness.toGeometry hk hp
  let profile : ExactWeightThreeChainLocalProfile chain :=
    partition.toLocalProfile geometry
  exact
    { certificate := profile.toRunCertificate hk
      endpoint_eq := partition_endpointFullCount_eq hk hp partition }

/-- 任意实际精确权三片链的无条件容量界。 -/
theorem actualExactWeightThreeChain_capacity
    (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    2 * exactChainPieceCount chain ≤
      (k - 2) * (exactChainTotalDeficit chain +
        (actualChainCapacityPackage hk hp chain).certificate.endpointFullCount) :=
  exactWeightThreeChain_capacity_of_runCertificate hk chain
    (actualChainCapacityPackage hk hp chain).certificate

end PreimageChain

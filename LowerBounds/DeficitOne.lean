import PreimageChain.ComponentEndpointRigidity

/-!
# The deficit-one lemma

Three consecutive pieces of an exitless path, joined by two seams of weight exactly 3: if the
first is full (`k - 1` blocks) and the second has `k - 2` blocks, then the third has at most
`k - 3` blocks.

Write the entry of the first block of the full piece as `a₁ A b c` with `|A| = k - 3`.

* The seam into the piece of `k - 2` blocks is an `α` seam
  (`weightThree_complete_to_unitDeficit_isAlpha`), so that piece starts at `A a₁ b c` and its
  last block has entry `a₁ b A c`, with exit `c a₁ b A`.
* The six weight-3 successors of `c a₁ b A` are `A` followed by a permutation of `c, a₁, b`.
  Five of them lie in a rotation class that the path has already visited:
  `A c a₁ b` (the last block of the second piece), `A c b a₁` (the last block of the full
  piece), `A a₁ b c` (the first block of the second piece), `A b c a₁` (the first block of the
  full piece), `A b a₁ c` (the second block of the full piece).
* So the third piece starts at `A a₁ c b`.  Its block number `k - 3` would have entry
  `a₁ c A b`, a rotation of `A b a₁ c`, the second block of the full piece.

`deficitOne_path` is this statement in block coordinates, `actualPiece_after_full_unit_deficit_ge_two`
is the same for Liu's `ActualIntervalPieceSpan`, and `partition_unit_after_full_next_large` is
the fact (G5) about the canonical gap/partial decomposition of an exact weight-three chain.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### Words -/

/-- Swapping the two halves of a word does not change its rotation class. -/
theorem rotClass_append_comm (P Q : List ℕ) :
    rotClass (P ++ Q) = rotClass (Q ++ P) := by
  calc
    rotClass (P ++ Q) = rotClass ((P ++ Q).rotate P.length) :=
      (Hunter.ProofsClosure3.rotClass_rotate (P ++ Q) P.length).symm
    _ = rotClass (Q ++ P) := by rw [List.rotate_append_length_eq]

/-- Rotating by the length of the left half swaps the halves. -/
theorem rotate_append_of_length (P Q : List ℕ) {n : ℕ} (h : n = P.length) :
    (P ++ Q).rotate n = Q ++ P := by
  subst h
  exact List.rotate_append_length_eq P Q

/-- Two different blocks of an exitless path are never rotations of each other. -/
theorem block_clash {p : HPath k} (hk : 1 ≤ k) (hp : p.Exitless) {s t : ℕ}
    (hs : k * s < p.numVerts) (ht : k * t < p.numVerts) (hst : s ≠ t) {P Q : List ℕ}
    (h1 : Hunter.ProofsChartEq.blockWord p s = P ++ Q)
    (h2 : Hunter.ProofsChartEq.blockWord p t = Q ++ P) : False := by
  apply Hunter.ProofsChartEq.blockWord_distinct hk hp hs ht hst
  rw [h1, h2]
  exact rotClass_append_comm P Q

/-! ### The lemma in block coordinates -/

/--
**Deficit-one lemma.**  A full piece at block `leftStart`, a seam of weight 3, a piece of
`k - 2` blocks, a seam of weight 3, and then `k - 2` further blocks joined by doors cannot occur
in an exitless path.
-/
theorem deficitOne_path
    (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {leftStart : ℕ}
    (hleft : FullIntervalPiece p leftStart)
    (hincoming : Hunter.ProofsLedger.bw p (leftStart + (k - 1)) = 3)
    (hunitDoors : ∀ i, 1 ≤ i → i ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor p (leftStart + (k - 1) + i))
    (houtgoing : Hunter.ProofsLedger.bw p (leftStart + (k - 1) + (k - 2)) = 3)
    (hnextRange : k * (leftStart + (k - 1) + (k - 2) + (k - 3)) < p.numVerts)
    (hnextDoors : ∀ r, 1 ≤ r → r ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor p (leftStart + (k - 1) + (k - 2) + r)) :
    False := by
  obtain ⟨unitStart, hunitStart⟩ : ∃ u, u = leftStart + (k - 1) := ⟨_, rfl⟩
  obtain ⟨nextStart, hnextStart⟩ : ∃ t, t = unitStart + (k - 2) := ⟨_, rfl⟩
  rw [← hunitStart] at hincoming hunitDoors houtgoing hnextRange hnextDoors
  rw [← hnextStart] at houtgoing hnextRange hnextDoors
  have hk1 : 1 ≤ k := by omega
  have hrange : ∀ {t : ℕ}, t ≤ nextStart + (k - 3) → k * t < p.numVerts := by
    intro t ht
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k ht) hnextRange
  have hnextStartRange : k * nextStart < p.numVerts := hrange (by omega)
  -- the seam into the piece of `k - 2` blocks is an `α` seam
  have hunit : UnitDeficitDoorSegment p unitStart :=
    ⟨by rw [← hnextStart]; exact hnextStartRange, hunitDoors⟩
  have hcomplete0 := fullIntervalPiece_complete (by omega : 3 ≤ k) hp hleft
  have hcomplete : Hunter.ProofsLedger.IsComplete p (unitStart - 1) := by
    rw [show unitStart - 1 = leftStart + (k - 2) by omega]
    exact hcomplete0
  have halpha : Hunter.ProofsLedger.IsAlpha p unitStart :=
    weightThree_complete_to_unitDeficit_isAlpha hk hp (by omega) hunit hincoming hcomplete
  -- the first block of the full piece is `a₁ A b c`
  have hrootLen : (Hunter.ProofsChartEq.blockWord p leftStart).length = k :=
    (Hunter.ProofsChartEq.blockWord_isPermWord p leftStart).length
  obtain ⟨A', b, c, hA'raw, hroot⟩ :=
    exists_split_last_two (Hunter.ProofsChartEq.blockWord p leftStart)
      (by rw [hrootLen]; omega)
  have hA' : A'.length = k - 2 := by rw [hA'raw, hrootLen]
  obtain ⟨a₁, A, rfl⟩ : ∃ a₁ A, A' = a₁ :: A := by
    cases A' with
    | nil =>
        simp only [List.length_nil] at hA'
        omega
    | cons a₁ A => exact ⟨a₁, A, rfl⟩
  have hA : A.length = k - 3 := by
    simp only [List.length_cons] at hA'
    omega
  -- blocks of the full piece
  have hD : ∀ l, l ≤ k - 2 → Hunter.ProofsChartEq.blockWord p (leftStart + l) =
      ((a₁ :: A) ++ [b]).rotate l ++ [c] := fun l hl =>
    fullPiece_block_word (by omega : 3 ≤ k) hp hA' hl hleft.inRange hleft.doors hroot
  have hD1 : Hunter.ProofsChartEq.blockWord p (leftStart + 1) = A ++ [b, a₁, c] := by
    rw [hD 1 (by omega)]
    simp [List.rotate_cons_succ]
  have hDlast : Hunter.ProofsChartEq.blockWord p (leftStart + (k - 2)) =
      [b] ++ (a₁ :: A) ++ [c] := by
    rw [hD (k - 2) le_rfl,
      rotate_append_of_length (a₁ :: A) [b] (by rw [List.length_cons, hA]; omega)]
  -- the piece of `k - 2` blocks starts at `A a₁ b c`
  have hnext := fullPiece_alpha_next_start (by omega : 3 ≤ k) hp hA'
    (start := leftStart) (q := b) (t := c)
    (by rw [← hunitStart]; exact hrange (by omega)) hleft.doors hroot
    (by rw [← hunitStart]; exact halpha)
  have hV0 : Hunter.ProofsChartEq.blockWord p unitStart = (A ++ [a₁, b]) ++ [c] := by
    rw [hunitStart, hnext]
    simp [List.rotate_cons_succ]
  -- and its last block is `a₁ b A c`
  have hVlast : Hunter.ProofsChartEq.blockWord p (unitStart + (k - 3)) =
      [a₁, b] ++ A ++ [c] := by
    have h := doorSegment_block_word (by omega : 2 ≤ k) hp (start := unitStart)
      (r := k - 3) (l := k - 3) (base := A ++ [a₁, b]) (marker := c) le_rfl
      (hrange (by omega)) hunitDoors hV0
    rw [h, rotate_append_of_length A [a₁, b] hA.symm]
  -- the vertex before the third piece is `c a₁ b A`
  have hsource := blockBoundarySource_eq_bexit hk1 hp (t := nextStart) (by omega)
    hnextStartRange
  rw [show nextStart - 1 = unitStart + (k - 3) by omega, hVlast] at hsource
  have hbexit : Hunter.ProofsRigidity2.bexit k ([a₁, b] ++ A ++ [c]) = c :: a₁ :: b :: A := by
    unfold Hunter.ProofsRigidity2.bexit
    rw [rotate_append_of_length ([a₁, b] ++ A) [c]
      (by simp only [List.length_append, List.length_cons, List.length_nil, hA]; omega)]
    rfl
  rw [hbexit] at hsource
  obtain ⟨o, hnextWord⟩ := weightThreeTarget_normalizes_from_head hk
    (V := A) (m := c) (a := a₁) (c := b) hA hsource houtgoing
  cases o with
  | mab =>
      -- `A c a₁ b`: the class of the last block of the second piece
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      exact block_clash hk1 hp (s := unitStart + (k - 3)) (t := nextStart)
        (P := [a₁, b]) (Q := A ++ [c]) (hrange (by omega)) hnextStartRange (by omega)
        (by rw [hVlast]; simp) (by rw [hnextWord])
  | mba =>
      -- `A c b a₁`: the class of the last block of the full piece
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      exact block_clash hk1 hp (s := leftStart + (k - 2)) (t := nextStart)
        (P := [b, a₁]) (Q := A ++ [c]) (hrange (by omega)) hnextStartRange (by omega)
        (by rw [hDlast]; simp) (by rw [hnextWord])
  | abm =>
      -- `A a₁ b c`: the first block of the second piece
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      exact block_clash hk1 hp (s := unitStart) (t := nextStart)
        (P := []) (Q := A ++ [a₁, b, c]) (hrange (by omega)) hnextStartRange (by omega)
        (by rw [hV0]; simp) (by rw [hnextWord]; simp)
  | amb =>
      -- `A a₁ c b`: block `k - 3` of the third piece is `a₁ c A b`, a rotation of `A b a₁ c`
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      have hstart : Hunter.ProofsChartEq.blockWord p nextStart = (A ++ [a₁, c]) ++ [b] := by
        rw [hnextWord]
        simp
      have h := doorSegment_block_word (by omega : 2 ≤ k) hp (start := nextStart)
        (r := k - 3) (l := k - 3) (base := A ++ [a₁, c]) (marker := b) le_rfl
        hnextRange hnextDoors hstart
      rw [rotate_append_of_length A [a₁, c] hA.symm] at h
      exact block_clash hk1 hp (s := nextStart + (k - 3)) (t := leftStart + 1)
        (P := [a₁, c]) (Q := A ++ [b]) hnextRange (hrange (by omega)) (by omega)
        (by rw [h]; simp) (by rw [hD1]; simp)
  | bma =>
      -- `A b c a₁`: the class of the first block of the full piece
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      exact block_clash hk1 hp (s := leftStart) (t := nextStart)
        (P := [a₁]) (Q := A ++ [b, c]) (hrange (by omega)) hnextStartRange (by omega)
        (by rw [hroot]; simp) (by rw [hnextWord]; simp)
  | bam =>
      -- `A b a₁ c`: the second block of the full piece
      simp only [orientedSuccessorStartWord, List.rotate_zero] at hnextWord
      exact block_clash hk1 hp (s := leftStart + 1) (t := nextStart)
        (P := []) (Q := A ++ [b, a₁, c]) (hrange (by omega)) hnextStartRange (by omega)
        (by rw [hD1]; simp) (by rw [hnextWord]; simp)

/-! ### The lemma for actual pieces -/

/--
Deficit-one lemma for Liu's actual pieces: after a full piece and a piece of deficit 1, joined
by seams of weight 3, the next piece has deficit at least 2.
-/
theorem actualPiece_after_full_unit_deficit_ge_two
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {leftStart leftStop unitStart unitStop nextStart nextStop : ℕ}
    (hleft : ActualIntervalPieceSpan p leftStart leftStop)
    (hunit : ActualIntervalPieceSpan p unitStart unitStop)
    (hnext : ActualIntervalPieceSpan p nextStart nextStop)
    (hleftFull : actualPieceDeficit k leftStart leftStop = 0)
    (hunitDeficit : actualPieceDeficit k unitStart unitStop = 1)
    (hjoinLeft : leftStop = unitStart) (hjoinRight : unitStop = nextStart)
    (hincoming : Hunter.ProofsLedger.bw p unitStart = 3)
    (houtgoing : Hunter.ProofsLedger.bw p nextStart = 3) :
    2 ≤ actualPieceDeficit k nextStart nextStop := by
  by_contra hsmall
  have hleftPiece := fullIntervalPiece_of_actual_deficit_zero hk hp hleft hleftFull
  have hleftSize := actualIntervalPieceSpan_size_add_deficit hk hp hleft
  have hunitSize := actualIntervalPieceSpan_size_add_deficit hk hp hunit
  have hnextSize := actualIntervalPieceSpan_size_add_deficit hk hp hnext
  rw [hleftFull] at hleftSize
  rw [hunitDeficit] at hunitSize
  simp only [actualPieceSize] at hleftSize hunitSize hnextSize
  have h1 := hleft.nonempty
  have h2 := hunit.nonempty
  have h3 := hnext.nonempty
  have hunitStart : unitStart = leftStart + (k - 1) := by omega
  have hnextStart : nextStart = leftStart + (k - 1) + (k - 2) := by omega
  have hnextLen : k - 2 ≤ nextStop - nextStart := by omega
  have hlast := actualIntervalPieceSpan_last_inRange (by omega : 1 ≤ k) hp hnext
  apply deficitOne_path hk hp.1 hleftPiece
  · rw [← hunitStart]
    exact hincoming
  · intro i hi1 hi2
    rw [← hunitStart]
    exact hunit.doors i hi1 (by omega)
  · rw [← hnextStart]
    exact houtgoing
  · rw [← hnextStart]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k (by omega)) hlast
  · intro r hr1 hr2
    rw [← hnextStart]
    exact hnext.doors r hr1 (by omega)

/-! ### The canonical decomposition of a chain -/

variable {p : HPath k}

private theorem natListAt_getElem
    (fallback : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    natListAt fallback xs i = xs[i] := by
  simp [natListAt, List.getElem?_eq_getElem hi]

/-- The length of gap `i`. -/
theorem gapLengths_at
    (gaps : List (List (ComponentIntervalPiece p)))
    (i : ℕ) (hi : i < gaps.length) :
    natListAt 0 (gapLengths gaps) i = gaps[i].length := by
  rw [natListAt_getElem 0 (gapLengths gaps) i (by simpa [gapLengths] using hi)]
  simp [gapLengths]

/-- The deficit of partial piece `i`. -/
theorem partialDeficits_at
    (partials : List (ComponentIntervalPiece p))
    (i : ℕ) (hi : i < partials.length) :
    natListAt 1 (partialDeficits partials) i = partials[i].deficit := by
  rw [natListAt_getElem 1 (partialDeficits partials) i
    (by simpa [partialDeficits] using hi)]
  simp [partialDeficits]

/-- Two partial pieces with an empty gap between them are adjacent in the chain. -/
theorem consecutivePartials_of_interleave
    {α : Type} {R : α → α → Prop}
    (gaps : List (List α)) (partials : List α)
    (hlen : gaps.length = partials.length + 1)
    (hadj : AdjacentList R (interleavePieceGaps gaps partials)) :
    ∀ i, (hi : i + 1 < partials.length) → (hnil : gaps[i + 1] = []) →
      R partials[i] partials[i + 1] := by
  induction partials generalizing gaps with
  | nil => intro i hi; simp at hi
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLength : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          intro i hi hnil
          cases i with
          | zero =>
              cases gaps with
              | nil => simp at htailLength
              | cons next more =>
                  cases partials with
                  | nil => simp at hi
                  | cons part2 rest =>
                      have hnext : next = [] := by simpa using hnil
                      subst hnext
                      have hdrop : AdjacentList R
                          (part :: part2 :: interleavePieceGaps more rest) := by
                        have hdropped := AdjacentList.drop hadj gap.length
                        simpa [interleavePieceGaps] using hdropped
                      simpa using hdrop.1
          | succ i =>
              have htailAdj : AdjacentList R
                  (interleavePieceGaps gaps partials) := by
                have hdropped := hadj.drop (gap.length + 1)
                simpa [interleavePieceGaps] using hdropped
              have hi' : i + 1 < partials.length := by simpa using hi
              have hnil' : gaps[i + 1] = [] := by simpa using hnil
              simpa only [List.getElem_cons_succ] using
                ih gaps htailLength htailAdj i hi' hnil'

/--
**(G5).**  In the canonical gap/partial decomposition of an exact weight-three chain: if gap `j`
is not empty, partial piece `j` has deficit 1 and there is a partial piece `j + 1`, then partial
piece `j + 1` has deficit at least 2.
-/
theorem partition_unit_after_full_next_large {k : ℕ} (hk : 5 ≤ k) {p : HPath k}
    (hp : p.StronglyExitless) {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (partition : ExactPieceGapPartition chain.pieces gaps partials) :
    ∀ j, j + 1 < partials.length →
      0 < natListAt 0 (gapLengths gaps) j →
      natListAt 1 (partialDeficits partials) j = 1 →
      2 ≤ natListAt 1 (partialDeficits partials) (j + 1) := by
  intro j hj1 hgap hunit
  have hgapsLength := partition.gaps_length
  have hj : j < partials.length := by omega
  have hjGap : j < gaps.length := by omega
  have hj1Gap : j + 1 < gaps.length := by omega
  rw [gapLengths_at gaps j hjGap] at hgap
  rw [partialDeficits_at partials j hj] at hunit
  rw [partialDeficits_at partials (j + 1) hj1]
  have hleftNe : gaps[j] ≠ [] := List.ne_nil_of_length_pos hgap
  have hadj : AdjacentList PieceExactJoin (interleavePieceGaps gaps partials) := by
    rw [partition.interleave_eq]
    exact exactWeightThreeChain_adjacent chain
  have hleftB : PieceExactJoin (gaps[j].getLast hleftNe) partials[j] :=
    rightBoundary_of_interleave gaps partials hgapsLength hadj j hj hleftNe
  have hleftFull : (gaps[j].getLast hleftNe).deficit = 0 :=
    partition.gaps_all_full gaps[j] (List.getElem_mem hjGap) _ (List.getLast_mem hleftNe)
  by_cases hmid : gaps[j + 1] = []
  · -- the next piece is partial piece `j + 1`: the deficit-one lemma
    have hmidB : PieceExactJoin partials[j] partials[j + 1] :=
      consecutivePartials_of_interleave gaps partials hgapsLength hadj j hj1 hmid
    exact actualPiece_after_full_unit_deficit_ge_two (by omega : 4 ≤ k) hp
      (gaps[j].getLast hleftNe).valid partials[j].valid partials[j + 1].valid
      hleftFull hunit hleftB.1 hmidB.1 hleftB.2 hmidB.2
  · -- the next piece is full: excluded by Liu's unit one-sidedness
    exfalso
    have hrightB : PieceExactJoin partials[j] (gaps[j + 1].head hmid) :=
      afterPartialBoundary_of_interleave gaps partials hgapsLength hadj j hj hmid
    have hgapAdj : AdjacentList PieceExactJoin gaps[j + 1] :=
      gaps_adjacent_of_interleave gaps partials hgapsLength hadj gaps[j + 1]
        (List.getElem_mem hj1Gap)
    have hrun : WeightThreeFullRun p (gaps[j + 1].head hmid).start gaps[j + 1].length :=
      fullPieceList_isRun (by omega : 4 ≤ k) hp gaps[j + 1] hmid
        (partition.gaps_all_full gaps[j + 1] (List.getElem_mem hj1Gap)) hgapAdj
    have hrun' : WeightThreeFullRun p partials[j].stop gaps[j + 1].length := by
      rw [hrightB.1]
      exact hrun
    have hout : Hunter.ProofsLedger.bw p partials[j].stop = 3 := by
      rw [hrightB.1]
      exact hrightB.2
    exact actualUnitPiece_not_between_full_runs (by omega : 4 ≤ k) hp
      (gaps[j].getLast hleftNe).valid partials[j].valid hleftFull hunit hleftB.1
      hleftB.2 hout (List.length_pos_iff.mpr hmid) hrun'

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.deficitOne_path
#print axioms SuperpermLowerBounds.actualPiece_after_full_unit_deficit_ge_two
#print axioms SuperpermLowerBounds.partition_unit_after_full_next_large

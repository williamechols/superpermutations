import PreimageChain.FullRunExtraction

/-!
# 非终端最大满游程的坐标碰撞

本模块证明：一个后面仍有精确权三后继的满片游程不能达到一般纯游程上界
`k-2`，因此其长度至多为 `k-3`。证明把末端权三目标归一化为六种方向，
并在每种方向中显式找到一个已经被源满游程访问的旋转类。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- 长度至少三的词可按最后三个符号分解。 -/
theorem exists_split_last_three
    (word : List ℕ) (hthree : 3 ≤ word.length) :
    ∃ R a b m, R.length = word.length - 3 ∧ word = R ++ [a, b, m] := by
  let m := word.getLastD 0
  let base := word.dropLast
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil] at hthree
    simp at hthree
  have hword : word = base ++ [m] := by
    dsimp [base, m]
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD word hwordNe
  have hbaseLen : base.length = word.length - 1 := by
    dsimp [base]
    rw [List.length_dropLast]
  have hbaseNe : base ≠ [] := by
    intro hnil
    rw [hnil] at hbaseLen
    simp at hbaseLen
    omega
  let b := base.getLastD 0
  let pre := base.dropLast
  have hbase : base = pre ++ [b] := by
    dsimp [pre, b]
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD base hbaseNe
  have hpreLen : pre.length = word.length - 2 := by
    dsimp [pre]
    rw [List.length_dropLast, hbaseLen]
    omega
  have hpreNe : pre ≠ [] := by
    intro hnil
    rw [hnil] at hpreLen
    simp at hpreLen
    omega
  let a := pre.getLastD 0
  let R := pre.dropLast
  have hpre : pre = R ++ [a] := by
    dsimp [R, a]
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD pre hpreNe
  have hR : R.length = word.length - 3 := by
    dsimp [R]
    rw [List.length_dropLast, hpreLen]
    omega
  refine ⟨R, a, b, m, hR, ?_⟩
  rw [hword, hbase, hpre]
  simp [List.append_assoc]

/--
长度 `|R|+1=k-2` 的满游程采用 `.bam` 方向时，任意精确权三后继的首个
旋转类都已经出现在该游程中。证明直接复用已核验的六行门户碰撞表。
-/
private theorem rotClass_append_swap (P Q : List ℕ) :
    rotClass (P ++ Q) = rotClass (Q ++ P) := by
  calc
    rotClass (P ++ Q) = rotClass ((P ++ Q).rotate P.length) :=
      (Hunter.ProofsClosure3.rotClass_rotate (P ++ Q) P.length).symm
    _ = rotClass (Q ++ P) := by
      rw [Hunter.ProofsFill.rotate_append_left]

private theorem target_to_partial_full
    (R : List ℕ) (x y z : ℕ) :
    rotClass (R ++ [x, y, z]) =
      rotClass (partialIncidenceWord R x y z (R.length + 2)) := by
  calc
    rotClass (R ++ [x, y, z]) = rotClass ([x, y, z] ++ R) :=
      rotClass_append_swap R [x, y, z]
    _ = rotClass (partialIncidenceWord R x y z (R.length + 2)) := by
      apply congrArg rotClass
      unfold partialIncidenceWord
      rw [show R.length + 2 = (y :: z :: R).length by simp]
      rw [List.rotate_length]
      rfl

theorem maximalFullRun_successor_collision_coordinates
    (R : List ℕ) (m a b : ℕ) (o : PortalOrientation) :
    ∃ j, j < R.length + 1 ∧ ∃ l, l < R.length + 2 ∧
      rotClass (orientedSuccessorStartWord R m b a o 0) =
        rotClass (orientedSuccessorIncidenceWord R m b a .bam j l) := by
  cases o with
  | mab =>
      refine ⟨R.length, by omega, R.length + 1, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .mab 0) =
            rotClass (partialIncidenceWord R m b a (R.length + 2)) := by
        simpa [orientedSuccessorStartWord] using
          target_to_partial_full R m b a
      have hcollision := portalCollision_bam R m b a (R.length + 1)
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)
  | mba =>
      refine ⟨0, by omega, R.length, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .mba 0) =
            rotClass (partialIncidenceWord R m a b (R.length + 2)) := by
        simpa [orientedSuccessorStartWord] using
          target_to_partial_full R m a b
      have hcollision := portalCollision_abm R m a b (R.length + 1) (by omega)
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)
  | abm =>
      refine ⟨R.length, by omega, 1, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .abm 0) =
            rotClass (partialIncidenceWord R m b a 2) := by
        calc
          rotClass (orientedSuccessorStartWord R m b a .abm 0) =
              rotClass (m :: (R ++ [b, a])) := by
            simpa [orientedSuccessorStartWord, List.append_assoc] using
              rotClass_append_swap (R ++ [b, a]) [m]
          _ = rotClass (partialIncidenceWord R m b a 2) := by
            simpa only [partialIncidenceWord] using
              congrArg (fun W => rotClass (m :: W))
                (rotate_abR_two R b a).symm
      have hcollision := portalCollision_bam R m b a 1
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)
  | amb =>
      refine ⟨R.length, by omega, 0, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .amb 0) =
            rotClass (partialIncidenceWord R m b a 1) := by
        calc
          rotClass (orientedSuccessorStartWord R m b a .amb 0) =
              rotClass ([m, a] ++ (R ++ [b])) := by
            simpa [orientedSuccessorStartWord, List.append_assoc] using
              rotClass_append_swap (R ++ [b]) [m, a]
          _ = rotClass (partialIncidenceWord R m b a 1) := by
            simpa [partialIncidenceWord, List.append_assoc] using
              congrArg (fun W => rotClass (m :: W))
                (rotate_abR_one R b a).symm
      have hcollision := portalCollision_bam R m b a 0
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)
  | bma =>
      refine ⟨0, by omega, R.length + 1, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .bma 0) =
            rotClass (partialIncidenceWord R a m b 0) := by
        calc
          rotClass (orientedSuccessorStartWord R m b a .bma 0) =
              rotClass ([a, m, b] ++ R) := by
            simpa [orientedSuccessorStartWord, List.append_assoc] using
              rotClass_append_swap R [a, m, b]
          _ = rotClass (partialIncidenceWord R a m b 0) := by
            simp [partialIncidenceWord]
      have hcollision := portalCollision_mba R a m b
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)
  | bam =>
      refine ⟨0, by omega, 0, by omega, ?_⟩
      have htarget :
          rotClass (orientedSuccessorStartWord R m b a .bam 0) =
            rotClass (partialIncidenceWord R a b m 0) := by
        calc
          rotClass (orientedSuccessorStartWord R m b a .bam 0) =
              rotClass ([a, b, m] ++ R) := by
            simpa [orientedSuccessorStartWord, List.append_assoc] using
              rotClass_append_swap R [a, b, m]
          _ = rotClass (partialIncidenceWord R a b m 0) := by
            simp [partialIncidenceWord]
      have hcollision := portalCollision_mab R a b m
      exact htarget.trans (by
        simpa [orientedSuccessorIncidenceWord] using hcollision)


/--
只要满游程后还有一个精确权三后继块，游程长度就不能达到一般上界 `k-2`，
因而至多为 `k-3`。
-/
theorem nonterminalWeightThreeFullRun_length_le
    (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start M : ℕ} (hrun : WeightThreeFullRun p start M)
    (hM : 1 ≤ M)
    (htargetRange : k * (start + M * (k - 1)) < p.numVerts)
    (hseam : Hunter.ProofsLedger.bw p (start + M * (k - 1)) = 3) :
    M ≤ k - 3 := by
  have hle := weightThreeFullRun_length_le (by omega : 3 ≤ k) hp hrun
  by_contra hgoal
  have hMeq : M = k - 2 := by omega
  let root := Hunter.ProofsChartEq.blockWord p start
  have hrootLen : root.length = k := by
    exact (Hunter.ProofsChartEq.blockWord_isPermWord p start).length
  obtain ⟨R, a, b, m, hRraw, hroot⟩ :=
    exists_split_last_three root (by rw [hrootLen]; omega)
  have hR : R.length = k - 3 := by rw [hRraw, hrootLen]
  have hzero : Hunter.ProofsChartEq.blockWord p start =
      orientedSuccessorStartWord R m b a .bam 0 := by
    change root = _
    simpa [orientedSuccessorStartWord, List.append_assoc] using hroot
  have hstarts := weightThreeFullRun_start_words hk hp hR hrun hzero
  have hclasses := weightThreeFullRun_block_classes hk hp hR hrun hzero
  let target := start + M * (k - 1)
  have htargetPos : 1 ≤ target := by
    dsimp [target]
    have : 1 ≤ M * (k - 1) := Nat.mul_pos hM (by omega)
    omega
  have hlastIndex : M - 1 < M := by omega
  have hlastStartWord := hstarts (M - 1) hlastIndex
  have hperiod : R.length + 2 = k - 1 := by rw [hR]; omega
  have hlastStartIndex :
      start + (M - 1) * (R.length + 2) =
        target - (k - 1) := by
    have hMsplit : M = (M - 1) + 1 := by omega
    rw [hperiod]
    have htargetEq :
        target = (start + (M - 1) * (k - 1)) + (k - 1) := by
      dsimp [target]
      calc
        start + M * (k - 1) =
            start + ((M - 1) + 1) * (k - 1) := by
          exact congrArg (fun n => start + n * (k - 1)) hMsplit
        _ = start + ((M - 1) * (k - 1) + 1 * (k - 1)) := by
          rw [Nat.add_mul]
        _ = (start + (M - 1) * (k - 1)) + (k - 1) := by
          simp [Nat.add_assoc]
    rw [htargetEq, Nat.add_sub_cancel]
  have hlastStartWord' :
      Hunter.ProofsChartEq.blockWord p (target - (k - 1)) =
        (R ++ [a]).rotate (M - 1) ++ [b, m] := by
    rw [← hlastStartIndex]
    simpa [orientedSuccessorStartWord] using hlastStartWord
  have hlastPieceStart : target - (k - 1) + (k - 2) = target - 1 := by
    dsimp [target]
    have hpos : k - 1 ≤ M * (k - 1) := by
      simpa using Nat.mul_le_mul_right (k - 1) hM
    omega
  have hlastRange : k * (target - 1) < p.numVerts := by
    have : target - 1 < target := by omega
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left this (by omega : 0 < k))
      (Nat.le_of_lt htargetRange)
  have hlastDoors : ∀ r, 1 ≤ r → r ≤ k - 2 →
      Hunter.ProofsLedger.IsDoor p (target - (k - 1) + r) := by
    intro r hr1 hr2
    have hstartEq : target - (k - 1) = start + (M - 1) * (k - 1) := by
      calc
        target - (k - 1) = start + (M - 1) * (R.length + 2) :=
          hlastStartIndex.symm
        _ = start + (M - 1) * (k - 1) := by rw [hperiod]
    rw [hstartEq]
    exact hrun.doors (M - 1) r hlastIndex hr1 hr2
  have hAlen : ((R ++ [a]).rotate (M - 1)).length = k - 2 := by
    rw [List.length_rotate, List.length_append, hR]
    simp
    omega
  have hlastPieceRange :
      k * (target - (k - 1) + (k - 2)) < p.numVerts := by
    rw [hlastPieceStart]
    exact hlastRange
  have hlastWord := fullPiece_block_word (by omega : 3 ≤ k) hp hAlen
    (l := k - 2) (by omega) hlastPieceRange hlastDoors hlastStartWord'
  rw [hlastPieceStart] at hlastWord
  have hMminus : M - 1 = R.length := by rw [hMeq, hR]; omega
  have hprevWord : Hunter.ProofsChartEq.blockWord p (target - 1) =
      (b :: a :: R) ++ [m] := by
    rw [hMminus] at hlastWord
    rw [List.rotate_append_length_eq] at hlastWord
    have hk2len : k - 2 = ([a] ++ R).length := by
      simp [hR]
      omega
    have hrotate :
        (([a] ++ R) ++ [b]).rotate (k - 2) = b :: a :: R := by
      rw [hk2len, Hunter.ProofsFill.rotate_append_left]
      rfl
    rw [hrotate] at hlastWord
    simpa [List.append_assoc] using hlastWord
  have hsource := blockBoundarySource_eq_bexit (by omega : 1 ≤ k) hp
    htargetPos htargetRange
  have hsourceWord : (p.vert (k * target - 1) : List ℕ) = m :: b :: a :: R := by
    rw [hprevWord] at hsource
    have hbaseLen : (b :: a :: R).length = k - 1 := by simp [hR]; omega
    unfold Hunter.ProofsRigidity2.bexit at hsource
    rw [show k - 1 = (b :: a :: R).length by exact hbaseLen.symm,
      List.rotate_append_length_eq] at hsource
    simpa using hsource
  obtain ⟨o, htargetWord⟩ := weightThreeTarget_normalizes_from_head hk
    hR hsourceWord hseam
  obtain ⟨j, hj, l, hl, hcollision⟩ :=
    maximalFullRun_successor_collision_coordinates R m a b o
  have hjM : j < M := by
    have hMlen : M = R.length + 1 := by
      rw [hMeq, hR]
      omega
    rw [hMlen]
    exact hj
  have hclass := hclasses j hjM l hl
  have hblockIndex :
      start + j * (R.length + 2) + l < target := by
    have hlPeriod : l < k - 1 := by
      rw [← hperiod]
      exact hl
    have hstep : j * (k - 1) + l < (j + 1) * (k - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hjSucc : j + 1 ≤ M := Nat.succ_le_iff.mpr hjM
    have hmul := Nat.mul_le_mul_right (k - 1) hjSucc
    dsimp [target]
    rw [hperiod]
    omega
  have hblockRange :
      k * (start + j * (R.length + 2) + l) < p.numVerts := by
    have hmul := Nat.mul_lt_mul_of_pos_left hblockIndex (by omega : 0 < k)
    exact lt_trans hmul htargetRange
  have hdistinct := Hunter.ProofsChartEq.blockWord_distinct (by omega : 1 ≤ k) hp
    hblockRange htargetRange (by omega :
      start + j * (R.length + 2) + l ≠ target)
  apply hdistinct
  rw [hclass, htargetWord]
  exact hcollision.symm

end PreimageChain

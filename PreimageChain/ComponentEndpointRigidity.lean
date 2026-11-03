import PreimageChain.ActualComponentCapacity
import PreimageChain.MaximalRunCollision

/-!
# 最小入权二分量的端点刚性

若 strongly-exitless 分量的首片为满片，则双旋转前驱和 proper 权二前驱都已在
分量内，因此其最小外部入权不可能为二。末片满指标为一则确实推出
`componentLastPieceFull`。这两点把一般组件容量专门化为本原块稳定性所需的端点数据。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `door` 在长度至少二且等长的列表上是单射。 -/
theorem door_injective_of_equal_length
    {u v : List ℕ} (hu : 2 ≤ u.length) (hv : 2 ≤ v.length)
    (hlen : u.length = v.length) (hdoor : door u = door v) :
    u = v := by
  cases u with
  | nil => simp at hu
  | cons a us =>
      cases us with
      | nil => simp at hu
      | cons b tailU =>
          cases v with
          | nil => simp at hv
          | cons c vs =>
              cases vs with
              | nil => simp at hv
              | cons d tailV =>
                  change tailU ++ [b, a] = tailV ++ [d, c] at hdoor
                  have htailLen : tailU.length = tailV.length := by
                    simp only [List.length_cons] at hlen
                    omega
                  obtain ⟨htail, hlast⟩ := List.append_inj hdoor htailLen
                  subst tailV
                  have hlast' : b = d ∧ a = c := by
                    simpa using hlast
                  obtain ⟨rfl, rfl⟩ := hlast'
                  rfl

/-- 对 `k≥2`，proper 权二后继 `tau` 是单射。 -/
theorem tau_injective (hk : 2 ≤ k) : Function.Injective (@tau k) := by
  intro u v huv
  apply Subtype.ext
  have huDoor := tau_val_of_door (door_isPermWord hk u.2)
  have hvDoor := tau_val_of_door (door_isPermWord hk v.2)
  apply door_injective_of_equal_length
  · rw [u.2.length]
    exact hk
  · rw [v.2.length]
    exact hk
  · rw [u.2.length, v.2.length]
  · rw [← huDoor, ← hvDoor]
    exact congrArg Subtype.val huv

/-- 长度至少二的列表可按最后两个符号分解。 -/
theorem exists_split_last_two
    (word : List ℕ) (htwo : 2 ≤ word.length) :
    ∃ A b c, A.length = word.length - 2 ∧ word = A ++ [b, c] := by
  let c := word.getLastD 0
  let base := word.dropLast
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil] at htwo
    simp at htwo
  have hword : word = base ++ [c] := by
    dsimp [base, c]
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
  let A := base.dropLast
  have hbase : base = A ++ [b] := by
    dsimp [A, b]
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD base hbaseNe
  have hA : A.length = word.length - 2 := by
    dsimp [A]
    rw [List.length_dropLast, hbaseLen]
    omega
  refine ⟨A, b, c, hA, ?_⟩
  rw [hword, hbase]
  simp [List.append_assoc]

/-- 首片为满片时，proper 权二前驱已在组件路径内。 -/
theorem proper_predecessor_mem_of_first_full
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hfull : FullIntervalPiece p 0)
    {v : Vtx k} (htau : tau v = p.first) :
    v ∈ p.verts := by
  have hfirstLen : p.first.1.length = k := p.first.2.length
  obtain ⟨A, b, c, hAraw, hfirst⟩ :=
    exists_split_last_two p.first.1 (by rw [hfirstLen]; omega)
  have hA : A.length = k - 2 := by
    rw [hAraw, hfirstLen]
  have hstart : Hunter.ProofsChartEq.blockWord p 0 = A ++ [b, c] := by
    change (p.vert 0 : List ℕ) = A ++ [b, c]
    rw [p.vert_zero]
    exact hfirst
  have hlastWord := fullPiece_block_word (by omega : 3 ≤ k) hp.1 hA
    (l := k - 2) (by omega) hfull.inRange hfull.doors hstart
  have hnum := component_numVerts_eq (by omega : 1 ≤ k) hp
  have ht : k - 2 < componentClassCount p := by
    have hinRange := hfull.inRange
    rw [hnum] at hinRange
    have hinRange' : k * (k - 2) < k * componentClassCount p := by
      simpa only [Nat.zero_add] using hinRange
    exact Nat.lt_of_mul_lt_mul_left hinRange'
  let sourceIndex := k * (k - 2) + (k - 1)
  have hsourceRange : sourceIndex < p.numVerts := by
    rw [hnum]
    have hsucc : k - 1 ≤ componentClassCount p := by omega
    have hmul : k * (k - 1) ≤ k * componentClassCount p :=
      Nat.mul_le_mul_left k hsucc
    have hsourceSucc : sourceIndex + 1 = k * (k - 1) := by
      dsimp [sourceIndex]
      rw [Nat.add_assoc, show (k - 1) + 1 = k by omega]
      calc
        k * (k - 2) + k = k * (k - 2) + k * 1 := by rw [Nat.mul_one]
        _ = k * ((k - 2) + 1) := (Nat.mul_add k (k - 2) 1).symm
        _ = k * (k - 1) := by
          congr 1
          omega
    have hsourceLe : sourceIndex + 1 ≤ k * componentClassCount p := by
      rw [hsourceSucc]
      exact hmul
    exact Nat.lt_of_succ_le hsourceLe
  let source : Vtx k := p.vert sourceIndex
  have hcycle :
      p.vert (k * (k - 2) + (k - 1)) =
        sigma^[k - 1] (p.vert (k * (k - 2))) :=
    Hunter.ProofsExitless.block_is_full_cycle (by omega : 1 ≤ k) hp.1
      ⟨k - 2, rfl⟩ (by omega) hsourceRange
  have hsourceVal : source.1 = Hunter.ProofsRigidity2.bexit k
      ((A ++ [b]).rotate (k - 2) ++ [c]) := by
    dsimp [source, sourceIndex]
    rw [hcycle, Hunter.ProofsExitless.sigma_iter_val]
    change ((Hunter.ProofsChartEq.blockWord p (k - 2) : List ℕ).rotate
      (k - 1)) = _
    have hlastWord' : Hunter.ProofsChartEq.blockWord p (k - 2) =
        (A ++ [b]).rotate (k - 2) ++ [c] := by
      simpa only [Nat.zero_add] using hlastWord
    rw [hlastWord']
    rfl
  have htauSource : tau source = p.first := by
    apply Subtype.ext
    rw [tau_val_of_door (door_isPermWord (by omega) source.2), hsourceVal]
    change Hunter.ProofsRigidity2.tau2 k
        ((A ++ [b]).rotate (k - 2) ++ [c]) = p.first.1
    have hprefix : (A ++ [b]).length = k - 1 := by simp [hA]; omega
    rw [Hunter.ProofsRigidity2.tau2_step (by omega : 2 ≤ k) hprefix c (k - 2),
      show k - 2 + 1 = k - 1 by omega]
    have hperiod : (A ++ [b]).rotate (k - 1) = A ++ [b] := by
      rw [← hprefix, List.rotate_length]
    rw [hperiod, hfirst]
    simp [List.append_assoc]
  have hvSource : v = source := tau_injective (by omega : 2 ≤ k)
    (htau.trans htauSource.symm)
  rw [hvSource]
  exact Hunter.ProofsExitless.vert_mem p hsourceRange

/-- 组件实际片列表始终非空。 -/
theorem componentIntervalPieces_ne_nil
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    componentIntervalPieces p hk hp ≠ [] := by
  intro hnil
  have hlen := componentIntervalPieces_length p hk hp
  rw [hnil] at hlen
  simp [componentPieceCount] at hlen

/-- 最小入权二的非满分量首片不可能为满片。 -/
theorem componentFirstFullBit_eq_zero_of_minto_two
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hnonspanning : p.vertsFinset ≠ Finset.univ)
    (hmu : p.minto = 2) :
    componentFirstFullBit p (by omega) hp = 0 := by
  by_contra hne
  have hbit : componentFirstFullBit p (by omega) hp = 1 := by
    have hle := componentFirstFullBit_le_one p (by omega) hp
    omega
  obtain ⟨first, rest, hpieces⟩ :=
    List.exists_cons_of_ne_nil (componentIntervalPieces_ne_nil (by omega) hp)
  have hdeficit : first.deficit = 0 := by
    unfold componentFirstFullBit firstNatValue at hbit
    rw [hpieces] at hbit
    change (if first.deficit = 0 then 1 else 0) = 1 at hbit
    by_cases hzero : first.deficit = 0
    · exact hzero
    · simp [hzero] at hbit
  have hstart : first.start = 0 := by
    have hstarts := componentIntervalPieces_starts p (by omega) hp
    rw [hpieces] at hstarts
    have hhead := congrArg List.head? hstarts
    simpa [componentPieceStarts] using hhead
  have hfull := fullIntervalPiece_of_actual_deficit_zero (by omega : 4 ≤ k)
    hp first.valid hdeficit
  rw [hstart] at hfull
  let S : Set ℕ :=
    {d | ∃ v : Vtx k, v ∉ p.verts ∧ ew k v p.first = d}
  have hSne : S.Nonempty := by
    have hout : ∃ v : Vtx k, v ∉ p.vertsFinset := by
      by_contra hall
      push Not at hall
      exact hnonspanning (Finset.eq_univ_of_forall hall)
    obtain ⟨u, hu⟩ := hout
    refine ⟨ew k u p.first, u, ?_, rfl⟩
    exact fun humem => hu (HPath.mem_vertsFinset.mpr humem)
  have hmin : p.minto ∈ S := by
    unfold HPath.minto
    exact Nat.sInf_mem hSne
  rw [hmu] at hmin
  obtain ⟨v, hvout, hweight⟩ := hmin
  rcases weight_two_successors (by omega : 2 ≤ k) hweight with hdouble | hproper
  · have hrot : rotClass (sigma2 v).1 = rotClass v.1 := by
      simpa [sigma2, Function.iterate_succ_apply'] using
        Hunter.ProofsExitless.rotClass_sigma_iter 2 v
    have hvcycle : v ∈ cyc p.first := by
      apply Hunter.ProofsExitless.mem_cyc.mpr
      rw [hdouble]
      exact hrot.symm
    have huoc : p.IsUnionOfCycles := Hunter.Proved.clm_1cyclesubset hp
    exact hvout (HPath.mem_vertsFinset.mp
      (huoc p.first p.first_mem hvcycle))
  · exact hvout (proper_predecessor_mem_of_first_full
      (by omega : 4 ≤ k) hp hfull hproper.symm)

/-- 末片满指标为一时，最后实际片确实完成完整门游程。 -/
theorem componentLastFullBit_one_implies_lastPieceFull
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hbit : componentLastFullBit p (by omega) hp = 1) :
    componentLastPieceFull p := by
  have hreverseNe :
      (componentIntervalPieces p (by omega : 1 ≤ k) hp).reverse ≠ [] := by
    simp [componentIntervalPieces_ne_nil (by omega : 1 ≤ k) hp]
  obtain ⟨last, rest, hreverse⟩ :=
    List.exists_cons_of_ne_nil hreverseNe
  have hdeficit : last.deficit = 0 := by
    unfold componentLastFullBit lastNatValue firstNatValue at hbit
    rw [hreverse] at hbit
    change (if last.deficit = 0 then 1 else 0) = 1 at hbit
    by_cases hzero : last.deficit = 0
    · exact hzero
    · simp [hzero] at hbit
  have hstops := componentIntervalPieces_stops p (by omega) hp
  have hrevStops := congrArg List.reverse hstops
  have hlastStop : last.stop = componentClassCount p := by
    rw [← List.map_reverse, hreverse] at hrevStops
    have hhead := congrArg List.head? hrevStops
    simpa [componentPieceStops] using hhead
  have hfull := fullIntervalPiece_of_actual_deficit_zero (by omega : 4 ≤ k)
    hp last.valid hdeficit
  have hcomplete := fullIntervalPiece_complete (by omega : 3 ≤ k) hp.1 hfull
  have hsize := ComponentIntervalPiece.size_add_deficit (by omega : 4 ≤ k)
    hp last
  rw [hdeficit, Nat.add_zero] at hsize
  have hindex : last.start + (k - 2) = componentClassCount p - 1 := by
    simp only [ComponentIntervalPiece.size, actualPieceSize] at hsize
    rw [hlastStop] at hsize
    have hlt := last.valid.nonempty
    omega
  unfold componentLastPieceFull
  rwa [← hindex]

/-- 实际组件的零一终端门户指标。 -/
noncomputable def actualPortalBit
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  if hk : 2 ≤ k then
    if compMinto (F P) C.1 = 2 ∧
        componentLastFullBit (actualComponentPath hP C) (by omega)
          (actualComponentPath_stronglyExitless hP hk C) = 1
      then 1 else 0
  else 0

@[simp] theorem actualPortalBit_le_one
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualPortalBit hP C ≤ 1 := by
  unfold actualPortalBit
  by_cases hk : 2 ≤ k
  · rw [dif_pos hk]
    split <;> omega
  · rw [dif_neg hk]
    omega

/-- 门户指标为一即可恢复真实终端门户谓词。 -/
theorem actualPortalBit_one_implies_terminalPortal
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hbit : actualPortalBit hP C = 1) :
    ActualTerminalPortal hP C := by
  unfold actualPortalBit at hbit
  rw [dif_pos (by omega : 2 ≤ k)] at hbit
  split at hbit
  · rename_i hportal
    refine ⟨hportal.1, ?_⟩
    unfold actualComponentLastPieceFull
    exact componentLastFullBit_one_implies_lastPieceFull hk
      (actualComponentPath_stronglyExitless hP (by omega) C) hportal.2
  · omega

end PreimageChain

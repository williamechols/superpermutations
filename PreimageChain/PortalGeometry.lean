import Hunter.ProofsFillPath
import Hunter.ProofsLedger2
import Hunter.ProofsLast
import PreimageChain.ComponentGeometry

/-!
# 门户局部几何：满片与纯满片游程

一个满 interval piece 由 `k-1` 个连续旋转类组成，因此其内部恰有 `k-2`
个权二门边界。本模块先在真实 `HPath` 上形式化这一局部对象，再证明：

* 满片末端必处于 `IsComplete` 状态；
* 两个满片之间若接缝权为三，则该接缝只能是 `IsAlpha`；
* 因而，由权三接缝串联的纯满片游程长度至多为 `k-2`。

最后一条正是正文门户局部几何结论 (i) 的路径级版本。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

set_option maxHeartbeats 800000

/-- 从块 `start` 开始的满 interval piece：它的 `k-2` 个内部块边界全是门。 -/
structure FullIntervalPiece (p : HPath k) (start : ℕ) : Prop where
  inRange : k * (start + (k - 2)) < p.numVerts
  doors : ∀ r, 1 ≤ r → r ≤ k - 2 →
    Hunter.ProofsLedger.IsDoor p (start + r)

/-- 一段连续门边界会把 `doorDepth` 精确增加该段的长度。 -/
theorem doorDepth_add_eq_of_door_segment {p : HPath k} (start r : ℕ)
    (hdoor : ∀ i, 1 ≤ i → i ≤ r →
      Hunter.ProofsLedger.IsDoor p (start + i)) :
    Hunter.ProofsLedger.doorDepth p (start + r) =
      Hunter.ProofsLedger.doorDepth p start + r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hprefix : ∀ i, 1 ≤ i → i ≤ r →
          Hunter.ProofsLedger.IsDoor p (start + i) := by
        intro i hi hir
        exact hdoor i hi (by omega)
      have hlast : Hunter.ProofsLedger.IsDoor p ((start + r) + 1) := by
        simpa [Nat.add_assoc] using hdoor (r + 1) (by omega) (by omega)
      rw [show start + (r + 1) = (start + r) + 1 by omega,
        Hunter.ProofsLedger.doorDepth_door hlast, ih hprefix]
      simp only [Nat.add_assoc]

/-- 门段不改变 `metaDepth`。 -/
theorem metaDepth_add_eq_of_door_segment {p : HPath k} (start r : ℕ)
    (hdoor : ∀ i, 1 ≤ i → i ≤ r →
      Hunter.ProofsLedger.IsDoor p (start + i)) :
    Hunter.ProofsLedger.metaDepth p (start + r) =
      Hunter.ProofsLedger.metaDepth p start := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hprefix : ∀ i, 1 ≤ i → i ≤ r →
          Hunter.ProofsLedger.IsDoor p (start + i) := by
        intro i hi hir
        exact hdoor i hi (by omega)
      have hlast : Hunter.ProofsLedger.IsDoor p ((start + r) + 1) := by
        simpa [Nat.add_assoc] using hdoor (r + 1) (by omega) (by omega)
      rw [show start + (r + 1) = (start + r) + 1 by omega,
        Hunter.ProofsLedger.metaDepth_door hlast, ih hprefix]

/-- 满片的最后一个旋转块确实是完整块。 -/
theorem fullIntervalPiece_complete
    (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {start : ℕ}
    (hfull : FullIntervalPiece p start) :
    Hunter.ProofsLedger.IsComplete p (start + (k - 2)) := by
  have hdepth := doorDepth_add_eq_of_door_segment start (k - 2) hfull.doors
  have hcap := Hunter.ProofsLedger2.doorDepth_le_km2 hk hp
    (start + (k - 2)) hfull.inRange
  rw [Hunter.ProofsLedger.IsComplete, hdepth]
  omega

/--
若一个权三接缝离开完整片并进入另一个完整片，则五分类中：门和 heavy 与权三
矛盾，`σ²` 与源片完整性矛盾，marker-move 与 fill lemma 及目标片完整性矛盾；
故唯一可能是 `α`。
-/
theorem weightThree_between_complete_pieces_isAlpha
    (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t)
    (hN : k * (t + (k - 2)) < p.numVerts)
    (hweight : Hunter.ProofsLedger.bw p t = 3)
    (hsource : Hunter.ProofsLedger.IsComplete p (t - 1))
    (htarget : Hunter.ProofsLedger.IsComplete p (t + (k - 2))) :
    Hunter.ProofsLedger.IsAlpha p t := by
  have htEnd : t ≤ t + (k - 2) := by omega
  have hboundary : k * t < p.numVerts :=
    lt_of_le_of_lt (Nat.mul_le_mul_left k htEnd) hN
  rcases Hunter.ProofsLedger.boundary_classify_ledger hk hp ht hboundary with
    hdoor | halpha | hsigma | hmove | hheavy
  · rw [Hunter.ProofsLedger.IsDoor, hweight] at hdoor
    omega
  · exact halpha
  · exact False.elim
      ((Hunter.ProofsLedger.sigmaSq_incomplete_only hk hp hboundary hsigma) hsource)
  · exact False.elim
      (Hunter.Proved.fill_path hk hp ht hN hmove hsource htarget)
  · rw [Hunter.ProofsLedger.IsHeavy, hweight] at hheavy
    omega

/--
`m` 个满片组成的候选纯游程：每片内部均为门，且相邻满片之间的接缝恰为权三。
`inRange` 允许游程恰好结束于路径末端。
-/
structure WeightThreeFullRun (p : HPath k) (start m : ℕ) : Prop where
  inRange : k * (start + m * (k - 1)) ≤ p.numVerts
  doors : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 →
    Hunter.ProofsLedger.IsDoor p (start + j * (k - 1) + r)
  seams : ∀ c, 1 ≤ c → c < m →
    Hunter.ProofsLedger.bw p (start + c * (k - 1)) = 3

/-- 游程中编号 `j` 的片本身是一个满片。 -/
theorem weightThreeFullRun_piece
    (hk : 3 ≤ k) {p : HPath k} {start m j : ℕ}
    (hrun : WeightThreeFullRun p start m) (hjm : j < m) :
    FullIntervalPiece p (start + j * (k - 1)) := by
  refine ⟨?_, ?_⟩
  · have hjSucc : j + 1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_right (k - 1) hjSucc
    rw [Nat.add_mul] at hmul
    have hEnd : start + j * (k - 1) + (k - 2) <
        start + m * (k - 1) := by omega
    have hkmul := Nat.mul_lt_mul_of_pos_left hEnd (by omega : 0 < k)
    exact lt_of_lt_of_le hkmul hrun.inRange
  · intro r hr1 hr2
    simpa [Nat.add_assoc] using hrun.doors j r hjm hr1 hr2

/-- 权三满片游程中的每条内部接缝都是 `α` 接缝。 -/
theorem weightThreeFullRun_seam_isAlpha
    (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start m c : ℕ} (hrun : WeightThreeFullRun p start m)
    (hc1 : 1 ≤ c) (hcm : c < m) :
    Hunter.ProofsLedger.IsAlpha p (start + c * (k - 1)) := by
  let seam := start + c * (k - 1)
  let sourceStart := start + (c - 1) * (k - 1)
  have hcPred : c - 1 < m := by omega
  have hseamEq : seam = sourceStart + (k - 1) := by
    dsimp [sourceStart, seam]
    calc
      start + c * (k - 1) = start + ((c - 1) + 1) * (k - 1) := by
        rw [Nat.sub_add_cancel hc1]
      _ = start + (c - 1) * (k - 1) + (k - 1) := by
        rw [Nat.add_mul, one_mul, Nat.add_assoc]
  have hsourceEnd : sourceStart + (k - 2) = seam - 1 := by
    rw [hseamEq]
    omega
  have htargetEnd : seam + (k - 2) < start + m * (k - 1) := by
    dsimp [seam]
    have hcSucc : c + 1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_right (k - 1) hcSucc
    rw [Nat.add_mul] at hmul
    omega
  have htargetRange : k * (seam + (k - 2)) < p.numVerts := by
    have hmul := Nat.mul_lt_mul_of_pos_left htargetEnd (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hrun.inRange
  have hsourceRange : k * (sourceStart + (k - 2)) < p.numVerts := by
    have hEndLe : sourceStart + (k - 2) ≤ seam + (k - 2) := by
      dsimp [sourceStart, seam]
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k hEndLe) htargetRange
  have hsourceFull : FullIntervalPiece p sourceStart := by
    refine ⟨hsourceRange, ?_⟩
    intro r hr1 hr2
    simpa [sourceStart, Nat.add_assoc] using
      hrun.doors (c - 1) r hcPred hr1 hr2
  have htargetFull : FullIntervalPiece p seam := by
    refine ⟨htargetRange, ?_⟩
    intro r hr1 hr2
    simpa [seam, Nat.add_assoc] using hrun.doors c r hcm hr1 hr2
  have hsourceComplete := fullIntervalPiece_complete hk hp hsourceFull
  have htargetComplete := fullIntervalPiece_complete hk hp htargetFull
  apply weightThree_between_complete_pieces_isAlpha hk hp
  · omega
  · exact htargetRange
  · exact hrun.seams c hc1 hcm
  · rwa [hsourceEnd] at hsourceComplete
  · exact htargetComplete

/-- 正文门户局部几何 (i)：纯满片游程的片数至多为 `k-2`。 -/
theorem weightThreeFullRun_length_le
    (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start m : ℕ} (hrun : WeightThreeFullRun p start m) :
    m ≤ k - 2 := by
  apply Hunter.ProofsLedger.metaDepth_le_of_run hk hp start m hrun.inRange hrun.doors
  intro c hc1 hcm
  exact weightThreeFullRun_seam_isAlpha hk hp hrun hc1 hcm

/-! ## 单位缺口片的已闭合入口几何 -/

/--
从 `start` 开始的单位缺口门段：该片有 `k-2` 个旋转类，故内部有 `k-3` 个门。
这里额外要求下一块仍在路径内；这是 `defective_deep_false` 的路径窗口接口。
-/
structure UnitDeficitDoorSegment (p : HPath k) (start : ℕ) : Prop where
  inRange : k * (start + (k - 2)) < p.numVerts
  doors : ∀ i, 1 ≤ i → i ≤ k - 3 →
    Hunter.ProofsLedger.IsDoor p (start + i)

/--
完整片以权三进入单位缺口门段时，接缝只能是 `α`。其中 marker-move 分支由
`ProofsLast.defective_deep_false` 的旋转类重入碰撞排除。
-/
theorem weightThree_complete_to_unitDeficit_isAlpha
    (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hunit : UnitDeficitDoorSegment p t)
    (hweight : Hunter.ProofsLedger.bw p t = 3)
    (hsource : Hunter.ProofsLedger.IsComplete p (t - 1)) :
    Hunter.ProofsLedger.IsAlpha p t := by
  have htEnd : t ≤ t + (k - 2) := by omega
  have hboundary : k * t < p.numVerts :=
    lt_of_le_of_lt (Nat.mul_le_mul_left k htEnd) hunit.inRange
  rcases Hunter.ProofsLedger.boundary_classify_ledger (by omega) hp ht hboundary with
    hdoor | halpha | hsigma | hmove | hheavy
  · rw [Hunter.ProofsLedger.IsDoor, hweight] at hdoor
    omega
  · exact halpha
  · exact False.elim
      ((Hunter.ProofsLedger.sigmaSq_incomplete_only (by omega) hp hboundary hsigma) hsource)
  · exact False.elim
      (Hunter.ProofsLast.defective_deep_false hk hp ht hunit.inRange hmove hsource hunit.doors)
  · rw [Hunter.ProofsLedger.IsHeavy, hweight] at hheavy
    omega

/-- 满片游程第 `c` 片起点处的元深度至少为 `c`。 -/
theorem weightThreeFullRun_metaDepth_start_ge
    (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start m c : ℕ} (hrun : WeightThreeFullRun p start m) (hcm : c < m) :
    c ≤ Hunter.ProofsLedger.metaDepth p (start + c * (k - 1)) := by
  induction c with
  | zero => omega
  | succ c ih =>
      have hcm' : c < m := by omega
      have hprev := ih hcm'
      have hpiece := weightThreeFullRun_piece (by omega : 3 ≤ k) hrun hcm'
      have hcarry := metaDepth_add_eq_of_door_segment
        (start + c * (k - 1)) (k - 2) hpiece.doors
      have hcomplete := fullIntervalPiece_complete (by omega) hp hpiece
      have halpha := weightThreeFullRun_seam_isAlpha (by omega) hp hrun
        (c := c + 1) (by omega) hcm
      have hsourceEnd : start + c * (k - 1) + (k - 2) =
          start + (c + 1) * (k - 1) - 1 := by
        rw [Nat.add_mul]
        omega
      have hnextPos : 1 ≤ start + (c + 1) * (k - 1) := by
        have : 1 ≤ (c + 1) * (k - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      have hpredSucc : start + (c + 1) * (k - 1) - 1 + 1 =
          start + (c + 1) * (k - 1) := Nat.sub_add_cancel hnextPos
      have hcomplete' : Hunter.ProofsLedger.IsComplete p
          (start + (c + 1) * (k - 1) - 1) := by
        rwa [hsourceEnd] at hcomplete
      have halpha' : Hunter.ProofsLedger.IsAlpha p
          (start + (c + 1) * (k - 1) - 1 + 1) := by
        rwa [hpredSucc]
      have hstep := Hunter.ProofsLedger.metaDepth_alpha_complete halpha' hcomplete'
      rw [hsourceEnd] at hcarry
      rw [hpredSucc] at hstep
      omega

/--
若一个正满片游程之后紧接一个有后续块的单位缺口片，则该满游程至多含 `k-3`
片。这是正文端点界 (iii) 在单位缺口入口方向上的真实路径版本。
-/
theorem fullRun_before_unitDeficit_length_le
    (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start m : ℕ} (hrun : WeightThreeFullRun p start m) (hm : 1 ≤ m)
    (hunit : UnitDeficitDoorSegment p (start + m * (k - 1)))
    (hseam : Hunter.ProofsLedger.bw p (start + m * (k - 1)) = 3) :
    m ≤ k - 3 := by
  let seam := start + m * (k - 1)
  have hmPred : m - 1 < m := by omega
  have hlastPiece := weightThreeFullRun_piece (by omega : 3 ≤ k) hrun hmPred
  have hlastStartDepth := weightThreeFullRun_metaDepth_start_ge hk hp hrun hmPred
  have hcarryFull := metaDepth_add_eq_of_door_segment
    (start + (m - 1) * (k - 1)) (k - 2) hlastPiece.doors
  have hsourceComplete := fullIntervalPiece_complete (by omega) hp hlastPiece
  have hsourceEnd : start + (m - 1) * (k - 1) + (k - 2) = seam - 1 := by
    have hmEq : (m - 1) + 1 = m := Nat.sub_add_cancel hm
    dsimp [seam]
    calc
      start + (m - 1) * (k - 1) + (k - 2) =
          start + ((m - 1) * (k - 1) + (k - 2)) := by omega
      _ = start + (((m - 1) + 1) * (k - 1) - 1) := by
        rw [Nat.add_mul]
        omega
      _ = start + (m * (k - 1) - 1) := by rw [hmEq]
      _ = start + m * (k - 1) - 1 := by
        have : 1 ≤ m * (k - 1) := Nat.mul_pos hm (by omega)
        omega
  have hsource : Hunter.ProofsLedger.IsComplete p (seam - 1) := by
    rwa [hsourceEnd] at hsourceComplete
  have hseamPos : 1 ≤ seam := by
    dsimp [seam]
    have : 1 ≤ m * (k - 1) := Nat.mul_pos hm (by omega)
    omega
  have halpha := weightThree_complete_to_unitDeficit_isAlpha hk hp hseamPos hunit hseam hsource
  have hpredSucc : seam - 1 + 1 = seam := Nat.sub_add_cancel hseamPos
  have halpha' : Hunter.ProofsLedger.IsAlpha p (seam - 1 + 1) := by
    rwa [hpredSucc]
  have hstep := Hunter.ProofsLedger.metaDepth_alpha_complete halpha' hsource
  have hunitCarry := metaDepth_add_eq_of_door_segment seam (k - 3) hunit.doors
  have hunitEndRange : k * (seam + (k - 3)) < p.numVerts := by
    have hle : seam + (k - 3) ≤ seam + (k - 2) := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k hle) hunit.inRange
  have hcap := Hunter.ProofsClose.metaDepth_le_km3 hk hp (seam + (k - 3)) hunitEndRange
  have hsourceEndDepth :
      m - 1 ≤ Hunter.ProofsLedger.metaDepth p (seam - 1) := by
    rw [← hsourceEnd, hcarryFull]
    exact hlastStartDepth
  rw [hpredSucc] at hstep
  omega

end PreimageChain

import PreimageChain.PortalCoordinates

/-!
# 实际组件的门户片链

本模块把 `componentSeamList` 的相邻断点最终需要携带的路径信息封装为实际 interval
piece：起止块号、非空性、组件范围和内部全门证书。该接口把组件分片层与
`PortalGeometry`/`PortalCoordinates` 的局部定理连接起来。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- 组件块区间 `[start, stop)` 所定义的一个实际 interval piece。 -/
structure ActualIntervalPieceSpan
    (p : HPath k) (start stop : ℕ) : Prop where
  nonempty : start < stop
  stopLe : stop ≤ componentClassCount p
  doors : ∀ r, 1 ≤ r → r < stop - start →
    Hunter.ProofsLedger.IsDoor p (start + r)

/-- 实际 interval piece 的旋转块数。 -/
def actualPieceSize (start stop : ℕ) : ℕ := stop - start

/-- 实际 interval piece 相对于满片长度 `k-1` 的缺口。 -/
def actualPieceDeficit (k start stop : ℕ) : ℕ :=
  k - 1 - actualPieceSize start stop

/-- 组件有序断点生成的原始片区间。 -/
noncomputable def componentPieceIntervals (p : HPath k) : List (ℕ × ℕ) :=
  List.zip (componentPieceStarts p) (componentPieceStops p)

@[simp] theorem componentPieceIntervals_length (p : HPath k) :
    (componentPieceIntervals p).length = componentPieceCount p := by
  rw [componentPieceIntervals, List.length_zip,
    componentPieceStarts_length, componentPieceStops_length, Nat.min_self]

/-- 自然数列表的非严格单调性与无重复性合成严格单调性。 -/
private theorem pairwise_lt_of_pairwise_le_nodup
    (xs : List ℕ) (hle : xs.Pairwise (· ≤ ·)) (hnd : xs.Nodup) :
    xs.Pairwise (· < ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hle' := List.pairwise_cons.mp hle
      have hnd' := List.nodup_cons.mp hnd
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        have hxy := hle'.1 y hy
        have hne : x ≠ y := by
          intro heq
          subst y
          exact hnd'.1 hy
        omega
      · exact ih hle'.2 hnd'.2

/--
严格递增断点列生成的每个相邻区间都是实际片。`hall` 表示起点之后的所有接缝
仍在当前断点尾列中，是递归时排除区间内部接缝的关键不变量。
-/
private theorem intervalSpans_of_sorted_breaks
    {p : HPath k} {breaks : Finset ℕ} (terminal start : ℕ) (xs : List ℕ)
    (hterminalLe : terminal ≤ componentClassCount p)
    (hstartTerminal : start < terminal)
    (hsorted : xs.Pairwise (· < ·))
    (hstartBefore : ∀ x ∈ xs, start < x)
    (hupper : ∀ x ∈ xs, x < terminal)
    (hall : ∀ j, j ∈ breaks → start < j → j ∈ xs)
    (hmem : ∀ j ∈ xs, j ∈ breaks)
    (hdoor : ∀ j, 1 ≤ j → j < terminal → j ∉ breaks →
      Hunter.ProofsLedger.IsDoor p j) :
    ∀ interval ∈ List.zip (start :: xs) (xs ++ [terminal]),
      ActualIntervalPieceSpan p interval.1 interval.2 := by
  induction xs generalizing start with
  | nil =>
      intro interval hinterval
      simp at hinterval
      subst interval
      refine ⟨hstartTerminal, ?_, ?_⟩
      · exact hterminalLe
      · intro r hr1 hr2
        apply hdoor (start + r)
        · omega
        · simp only at hr2
          omega
        · intro hbreak
          have := hall (start + r) hbreak (by omega)
          simp at this
  | cons x xs ih =>
      intro interval hinterval
      simp only [List.cons_append, List.zip_cons_cons, List.mem_cons] at hinterval
      rcases hinterval with rfl | hinterval
      · refine ⟨hstartBefore x List.mem_cons_self, ?_, ?_⟩
        · exact (Nat.le_of_lt (hupper x List.mem_cons_self)).trans hterminalLe
        · intro r hr1 hr2
          apply hdoor (start + r)
          · omega
          · have hx := hupper x List.mem_cons_self
            omega
          · intro hbreak
            have hbetween : start < start + r := by omega
            have hin := hall (start + r) hbreak hbetween
            rcases List.mem_cons.mp hin with heq | hinTail
            · omega
            · have hpc := List.pairwise_cons.mp hsorted
              have hxlt := hpc.1 (start + r) hinTail
              omega
      · have hpc := List.pairwise_cons.mp hsorted
        apply ih x (hupper x List.mem_cons_self) hpc.2
        · intro y hy
          exact hpc.1 y hy
        · intro y hy
          exact hupper y (List.mem_cons_of_mem x hy)
        · intro j hjBreak hxj
          have hsj : start < j := lt_trans
            (hstartBefore x List.mem_cons_self) hxj
          have hin := hall j hjBreak hsj
          rcases List.mem_cons.mp hin with heq | hinTail
          · omega
          · exact hinTail
        · intro j hj
          exact hmem j (List.mem_cons_of_mem x hj)
        · exact hinterval

/-- 有序 `componentSeamList` 的每对相邻断点确实生成一个实际 interval piece。 -/
theorem componentPieceInterval_valid
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {interval : ℕ × ℕ} (hinterval : interval ∈ componentPieceIntervals p) :
    ActualIntervalPieceSpan p interval.1 interval.2 := by
  have htPos := componentClassCount_pos hk hp
  have hsorted : (componentSeamList p).Pairwise (· < ·) := by
    exact pairwise_lt_of_pairwise_le_nodup (componentSeamList p)
      (componentSeamList_pairwise p) (componentSeamList_nodup p)
  have hbounds : ∀ j ∈ componentSeams p,
      1 ≤ j ∧ j < componentClassCount p := by
    intro j hj
    have hboundary := (Finset.mem_filter.mp hj).1
    rw [componentBoundaries, Finset.mem_Icc] at hboundary
    omega
  have hvalid := intervalSpans_of_sorted_breaks
    (p := p) (breaks := componentSeams p)
    (componentClassCount p) 0 (componentSeamList p) (le_refl _) htPos hsorted
    (by
      intro j hj
      exact (hbounds j (mem_componentSeamList.mp hj)).1)
    (by
      intro j hj
      exact (hbounds j (mem_componentSeamList.mp hj)).2)
    (by
      intro j hj _
      exact mem_componentSeamList.mpr hj)
    (by
      intro j hj
      exact mem_componentSeamList.mp hj)
    (by
      intro j hj1 hjlt hjnot
      apply (componentBoundary_door_iff_not_seam (p := p) ?_).2 hjnot
      rw [componentBoundaries, Finset.mem_Icc]
      omega)
  apply hvalid interval
  simpa [componentPieceIntervals, componentPieceStarts, componentPieceStops] using hinterval

/-- 实际片最后一个块始终位于组件路径内。 -/
theorem actualIntervalPieceSpan_last_inRange
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop : ℕ} (hpiece : ActualIntervalPieceSpan p start stop) :
    k * (stop - 1) < p.numVerts := by
  rw [component_numVerts_eq hk hp]
  have hnonempty := hpiece.nonempty
  have hstopLe := hpiece.stopLe
  have hstopPos : 1 ≤ stop := by omega
  have hlast : stop - 1 < componentClassCount p := by omega
  exact Nat.mul_lt_mul_of_pos_left hlast hk

/-- 片内连续门段把片末 `doorDepth` 至少提高 `size-1`。 -/
theorem actualIntervalPieceSpan_depth_ge
    {p : HPath k} {start stop : ℕ}
    (hpiece : ActualIntervalPieceSpan p start stop) :
    actualPieceSize start stop - 1 ≤
      Hunter.ProofsLedger.doorDepth p (stop - 1) := by
  have hstop : start + (actualPieceSize start stop - 1) = stop - 1 := by
    simp only [actualPieceSize]
    have := hpiece.nonempty
    omega
  have hdoors : ∀ i, 1 ≤ i → i ≤ actualPieceSize start stop - 1 →
      Hunter.ProofsLedger.IsDoor p (start + i) := by
    intro i hi1 hi2
    apply hpiece.doors i hi1
    simp only [actualPieceSize] at hi2 ⊢
    omega
  have hdepth := doorDepth_add_eq_of_door_segment
    start (actualPieceSize start stop - 1) hdoors
  rw [hstop] at hdepth
  omega

/-- 每个实际 interval piece 至多含 `k-1` 个旋转块。 -/
theorem actualIntervalPieceSpan_size_le
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop : ℕ} (hpiece : ActualIntervalPieceSpan p start stop) :
    actualPieceSize start stop ≤ k - 1 := by
  have hlastRange := actualIntervalPieceSpan_last_inRange (by omega) hp hpiece
  have hcap := Hunter.ProofsLedger2.doorDepth_le_km2 (by omega : 3 ≤ k)
    hp.1 (stop - 1) hlastRange
  have hdepth := actualIntervalPieceSpan_depth_ge hpiece
  have hpos : 1 ≤ actualPieceSize start stop := by
    simp only [actualPieceSize]
    have := hpiece.nonempty
    omega
  have hsizeSucc : actualPieceSize start stop =
      (actualPieceSize start stop - 1) + 1 := by omega
  have hkSucc : k - 1 = (k - 2) + 1 := by omega
  rw [hsizeSucc, hkSucc]
  exact Nat.add_le_add_right (le_trans hdepth hcap) 1

/-- 逐片大小与缺口的自然数等式没有截断。 -/
theorem actualIntervalPieceSpan_size_add_deficit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop : ℕ} (hpiece : ActualIntervalPieceSpan p start stop) :
    actualPieceSize start stop + actualPieceDeficit k start stop = k - 1 := by
  have hle := actualIntervalPieceSpan_size_le hk hp hpiece
  unfold actualPieceDeficit
  omega

/-- 缺口为零的实际片自动成为门户局部几何中的满片。 -/
theorem fullIntervalPiece_of_actual_deficit_zero
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop : ℕ} (hpiece : ActualIntervalPieceSpan p start stop)
    (hdeficit : actualPieceDeficit k start stop = 0) :
    FullIntervalPiece p start := by
  have hle := actualIntervalPieceSpan_size_le hk hp hpiece
  have hsize : actualPieceSize start stop = k - 1 := by
    unfold actualPieceDeficit at hdeficit
    omega
  have hstop : stop = start + (k - 1) := by
    simp only [actualPieceSize] at hsize
    omega
  refine ⟨?_, ?_⟩
  · have hlastRange := actualIntervalPieceSpan_last_inRange (by omega) hp hpiece
    rw [hstop] at hlastRange
    have hindex : start + (k - 1) - 1 = start + (k - 2) := by omega
    rwa [hindex] at hlastRange
  · intro r hr1 hr2
    apply hpiece.doors r hr1
    rw [hstop]
    omega

/--
实际部分片及其右侧权三满游程自动形成 `PartialThenFullRun`，从而可直接调用端点
坐标定理。
-/
theorem partialThenFullRun_of_actual_piece
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop M : ℕ} (hpiece : ActualIntervalPieceSpan p start stop)
    (hdeficitPos : 1 ≤ actualPieceDeficit k start stop)
    (hseam : Hunter.ProofsLedger.bw p stop = 3)
    (hM : 1 ≤ M)
    (hrun : WeightThreeFullRun p stop M) :
    PartialThenFullRun p start (actualPieceDeficit k start stop) M := by
  let delta := actualPieceDeficit k start stop
  have hcap := actualIntervalPieceSpan_size_add_deficit hk hp hpiece
  have hsizePos : 1 ≤ actualPieceSize start stop := by
    simp only [actualPieceSize]
    have := hpiece.nonempty
    omega
  have hdeltaMax : delta ≤ k - 2 := by
    dsimp [delta]
    omega
  have hstop : start + (k - 1 - delta) = stop := by
    have hstopRaw : start + actualPieceSize start stop = stop := by
      simp only [actualPieceSize]
      have := hpiece.nonempty
      omega
    dsimp [delta]
    omega
  refine
    { deltaPos := hdeficitPos
      deltaMax := hdeltaMax
      runPos := hM
      partialDoors := ?_
      seamWeight := ?_
      fullRun := ?_ }
  · intro r hr1 hr2
    apply hpiece.doors r hr1
    have hdeltaEq : actualPieceSize start stop + delta = k - 1 := hcap
    omega
  · rwa [hstop]
  · rwa [hstop]

/-- 实际部分片之后的正满游程自动满足路径级端点界 `M≤k-3`。 -/
theorem actualPiece_followingFullRun_length_le
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start stop M : ℕ} (hpiece : ActualIntervalPieceSpan p start stop)
    (hdeficitPos : 1 ≤ actualPieceDeficit k start stop)
    (hseam : Hunter.ProofsLedger.bw p stop = 3)
    (hM : 1 ≤ M) (hrun : WeightThreeFullRun p stop M) :
    M ≤ k - 3 := by
  apply partialThenFullRun_length_le hk hp.1
  exact partialThenFullRun_of_actual_piece hk hp hpiece hdeficitPos hseam hM hrun

/--
实际片接口下的单位缺口单侧性：满片、单位缺口片、正满游程不能依次出现。
-/
theorem actualUnitPiece_not_between_full_runs
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {leftStart leftStop unitStart unitStop M : ℕ}
    (hleft : ActualIntervalPieceSpan p leftStart leftStop)
    (hunit : ActualIntervalPieceSpan p unitStart unitStop)
    (hleftFull : actualPieceDeficit k leftStart leftStop = 0)
    (hunitDeficit : actualPieceDeficit k unitStart unitStop = 1)
    (hjoin : leftStop = unitStart)
    (hincoming : Hunter.ProofsLedger.bw p unitStart = 3)
    (houtgoing : Hunter.ProofsLedger.bw p unitStop = 3)
    (hM : 1 ≤ M) (hrun : WeightThreeFullRun p unitStop M) : False := by
  have hleftPiece := fullIntervalPiece_of_actual_deficit_zero hk hp hleft hleftFull
  have hleftSize := actualIntervalPieceSpan_size_add_deficit hk hp hleft
  have hleftStop : unitStart = leftStart + (k - 1) := by
    rw [hleftFull, Nat.add_zero] at hleftSize
    simp only [actualPieceSize] at hleftSize
    rw [hjoin] at hleftSize
    omega
  have hcfg := partialThenFullRun_of_actual_piece hk hp hunit
    (by rw [hunitDeficit]) houtgoing hM hrun
  rw [hunitDeficit] at hcfg
  rw [hleftStop] at hincoming hcfg
  exact unitDeficit_not_between_full_runs hk hp.1 hleftPiece
    hincoming hcfg

/--
实际左右部分片夹住 `k-3` 个满片时，两侧缺口之和满足内部阈值 `k-1`。
-/
theorem actualPieces_internalLongRun_deficit_threshold
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {leftStart leftStop rightStart rightStop : ℕ}
    (hleft : ActualIntervalPieceSpan p leftStart leftStop)
    (hright : ActualIntervalPieceSpan p rightStart rightStop)
    (hleftDeficitPos : 1 ≤ actualPieceDeficit k leftStart leftStop)
    (hrightDeficitPos : 1 ≤ actualPieceDeficit k rightStart rightStop)
    (hleftSeam : Hunter.ProofsLedger.bw p leftStop = 3)
    (hrun : WeightThreeFullRun p leftStop (k - 3))
    (hjoin : rightStart = leftStop + (k - 3) * (k - 1))
    (hrightSeam : Hunter.ProofsLedger.bw p rightStart = 3) :
    k - 1 ≤ actualPieceDeficit k leftStart leftStop +
      actualPieceDeficit k rightStart rightStop := by
  let leftDeficit := actualPieceDeficit k leftStart leftStop
  let rightDeficit := actualPieceDeficit k rightStart rightStop
  have hleftCfg : PartialThenFullRun p leftStart leftDeficit (k - 3) := by
    exact partialThenFullRun_of_actual_piece (by omega : 4 ≤ k) hp hleft
      hleftDeficitPos hleftSeam (by omega) hrun
  have hleftCap := actualIntervalPieceSpan_size_add_deficit
    (by omega : 4 ≤ k) hp hleft
  have hleftStopEq : leftStart + (k - 1 - leftDeficit) = leftStop := by
    have hraw : leftStart + actualPieceSize leftStart leftStop = leftStop := by
      simp only [actualPieceSize]
      have := hleft.nonempty
      omega
    dsimp [leftDeficit]
    omega
  have hrightCap := actualIntervalPieceSpan_size_add_deficit
    (by omega : 4 ≤ k) hp hright
  have hrightDeficitMax : rightDeficit ≤ k - 2 := by
    have hsizePos : 1 ≤ actualPieceSize rightStart rightStop := by
      simp only [actualPieceSize]
      have := hright.nonempty
      omega
    dsimp [rightDeficit]
    omega
  have hrightLast : rightStart + (k - 2 - rightDeficit) = rightStop - 1 := by
    have hraw : rightStart + actualPieceSize rightStart rightStop = rightStop := by
      simp only [actualPieceSize]
      have := hright.nonempty
      omega
    dsimp [rightDeficit]
    omega
  have hconfig : InternalLongFullRun p leftStart leftDeficit rightDeficit := by
    refine
      { left := hleftCfg
        rightDeficitPos := hrightDeficitPos
        rightDeficitMax := hrightDeficitMax
        rightSeamWeight := ?_
        rightDoors := ?_
        rightRange := ?_ }
    · have hindex : internalLongRightStart k leftStart leftDeficit = rightStart := by
        unfold internalLongRightStart
        rw [hleftStopEq, hjoin]
      rwa [hindex]
    · intro r hr1 hr2
      have hindex : internalLongRightStart k leftStart leftDeficit = rightStart := by
        unfold internalLongRightStart
        rw [hleftStopEq, hjoin]
      rw [hindex]
      apply hright.doors r hr1
      have hcap : actualPieceSize rightStart rightStop + rightDeficit = k - 1 :=
        hrightCap
      omega
    · have hindex : internalLongRightStart k leftStart leftDeficit = rightStart := by
        unfold internalLongRightStart
        rw [hleftStopEq, hjoin]
      rw [hindex, hrightLast]
      exact actualIntervalPieceSpan_last_inRange (by omega) hp hright
  exact internalLongFullRun_deficit_threshold hk hp.1 hconfig

/-- 带起止坐标的实际 interval piece，供有序链列表使用。 -/
structure ComponentIntervalPiece (p : HPath k) where
  start : ℕ
  stop : ℕ
  valid : ActualIntervalPieceSpan p start stop

namespace ComponentIntervalPiece

/-- 带证书实际片的长度。 -/
def size {p : HPath k} (piece : ComponentIntervalPiece p) : ℕ :=
  actualPieceSize piece.start piece.stop

/-- 带证书实际片的缺口。 -/
def deficit {p : HPath k} (piece : ComponentIntervalPiece p) : ℕ :=
  actualPieceDeficit k piece.start piece.stop

theorem size_add_deficit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) :
    piece.size + piece.deficit = k - 1 := by
  exact actualIntervalPieceSpan_size_add_deficit hk hp piece.valid

end ComponentIntervalPiece

/-- 把列表配对后的逐项映射改写为 `zipWith`。 -/
private theorem map_zip_eq_zipWith
    {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    (List.zip xs ys).map (fun pair => f pair.1 pair.2) =
      List.zipWith f xs ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [ih]

/-- 组件的全部相邻 seam 区间，连同自动生成的实际片证书。 -/
noncomputable def componentIntervalPieces
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    List (ComponentIntervalPiece p) :=
  (componentPieceIntervals p).attach.map fun interval =>
    { start := interval.val.1
      stop := interval.val.2
      valid := componentPieceInterval_valid hk hp interval.property }

@[simp] theorem componentIntervalPieces_length
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).length = componentPieceCount p := by
  simp [componentIntervalPieces, componentPieceIntervals_length]

/-- 带证书片列表忘掉证书后，精确还原原始相邻区间列表。 -/
theorem componentIntervalPieces_coordinates
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).map (fun piece =>
      (piece.start, piece.stop)) = componentPieceIntervals p := by
  simp only [componentIntervalPieces, List.map_map]
  change (componentPieceIntervals p).attach.unattach = componentPieceIntervals p
  exact List.unattach_attach

/-- 实际片证书列表的起点坐标就是组件的有序起点列表。 -/
theorem componentIntervalPieces_starts
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.start =
      componentPieceStarts p := by
  calc
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.start =
        ((componentIntervalPieces p hk hp).map fun piece =>
          (piece.start, piece.stop)).map Prod.fst := by
            simp [List.map_map]
    _ = (componentPieceIntervals p).map Prod.fst := by
      rw [componentIntervalPieces_coordinates]
    _ = componentPieceStarts p := by
      unfold componentPieceIntervals
      apply List.map_fst_zip
      simp

/-- 实际片证书列表的终点坐标就是组件的有序终点列表。 -/
theorem componentIntervalPieces_stops
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.stop =
      componentPieceStops p := by
  calc
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.stop =
        ((componentIntervalPieces p hk hp).map fun piece =>
          (piece.start, piece.stop)).map Prod.snd := by
            simp [List.map_map]
    _ = (componentPieceIntervals p).map Prod.snd := by
      rw [componentIntervalPieces_coordinates]
    _ = componentPieceStops p := by
      unfold componentPieceIntervals
      apply List.map_snd_zip
      simp

/-- 实际片证书列表的逐片大小就是组件组合层的 `componentPieceSizes`。 -/
theorem componentIntervalPieces_sizes
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.size =
      componentPieceSizes p := by
  calc
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.size =
        ((componentIntervalPieces p hk hp).map fun piece =>
          (piece.start, piece.stop)).map fun interval =>
            actualPieceSize interval.1 interval.2 := by
              simp [List.map_map, ComponentIntervalPiece.size]
    _ = (componentPieceIntervals p).map fun interval =>
          actualPieceSize interval.1 interval.2 := by
            rw [componentIntervalPieces_coordinates]
    _ = componentPieceSizes p := by
      unfold componentPieceIntervals componentPieceSizes actualPieceSize
      exact map_zip_eq_zipWith (fun start stop => stop - start)
        (componentPieceStarts p) (componentPieceStops p)

/-- 实际片证书列表的逐片缺口就是组件组合层的 `componentPieceDeficits`。 -/
theorem componentIntervalPieces_deficits
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.deficit =
      componentPieceDeficits p := by
  calc
    (componentIntervalPieces p hk hp).map ComponentIntervalPiece.deficit =
        ((componentIntervalPieces p hk hp).map
          ComponentIntervalPiece.size).map fun size => k - 1 - size := by
            simp [List.map_map, ComponentIntervalPiece.size,
              ComponentIntervalPiece.deficit, actualPieceDeficit]
    _ = (componentPieceSizes p).map fun size => k - 1 - size := by
      rw [componentIntervalPieces_sizes]
    _ = componentPieceDeficits p := by rfl

/-- 组件实际片列表中相邻两片严格首尾相接。 -/
theorem componentIntervalPieces_consecutive
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (i : ℕ) (hi : i + 1 < (componentIntervalPieces p hk hp).length) :
    (componentIntervalPieces p hk hp)[i].stop =
      (componentIntervalPieces p hk hp)[i + 1].start := by
  have hiSeam : i < (componentSeamList p).length := by
    have hiCard : i < (componentSeams p).card := by
      have hi' := hi
      rw [componentIntervalPieces_length, componentPieceCount] at hi'
      omega
    simpa using hiCard
  have hiPiece : i < (componentIntervalPieces p hk hp).length := by omega
  have hsome : some (componentIntervalPieces p hk hp)[i].stop =
      some (componentIntervalPieces p hk hp)[i + 1].start := by
    calc
      some (componentIntervalPieces p hk hp)[i].stop =
          ((componentIntervalPieces p hk hp).map
            ComponentIntervalPiece.stop)[i]? := by
              simp only [List.getElem?_map,
                List.getElem?_eq_getElem hiPiece, Option.map_some]
      _ = (componentPieceStops p)[i]? := by
        rw [componentIntervalPieces_stops]
      _ = (componentPieceStarts p)[i + 1]? := by
        simp only [componentPieceStops, componentPieceStarts,
          List.getElem?_append_left hiSeam, List.getElem?_cons_succ]
      _ = ((componentIntervalPieces p hk hp).map
            ComponentIntervalPiece.start)[i + 1]? := by
        rw [componentIntervalPieces_starts]
      _ = some (componentIntervalPieces p hk hp)[i + 1].start := by
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem hi, Option.map_some]
  exact Option.some.inj hsome

/-- 相邻实际片之间的公共端点确实属于组件接缝集。 -/
theorem componentIntervalPieces_joiningSeam
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (i : ℕ) (hi : i + 1 < (componentIntervalPieces p hk hp).length) :
    (componentIntervalPieces p hk hp)[i + 1].start ∈ componentSeams p := by
  have hiSeam : i < (componentSeamList p).length := by
    have hiCard : i < (componentSeams p).card := by
      have hi' := hi
      rw [componentIntervalPieces_length, componentPieceCount] at hi'
      omega
    simpa using hiCard
  have hsome : some (componentIntervalPieces p hk hp)[i + 1].start =
      some (componentSeamList p)[i] := by
    calc
      some (componentIntervalPieces p hk hp)[i + 1].start =
          ((componentIntervalPieces p hk hp).map
            ComponentIntervalPiece.start)[i + 1]? := by
              simp only [List.getElem?_map,
                List.getElem?_eq_getElem hi, Option.map_some]
      _ = (componentPieceStarts p)[i + 1]? := by
        rw [componentIntervalPieces_starts]
      _ = some (componentSeamList p)[i] := by
        simp only [componentPieceStarts, List.getElem?_cons_succ,
          List.getElem?_eq_getElem hiSeam]
  have hcoordinate := Option.some.inj hsome
  rw [hcoordinate]
  apply mem_componentSeamList.mp
  exact List.getElem_mem hiSeam

/-- 未被正剩余切割的相邻片公共 seam 权重精确为三。 -/
theorem componentIntervalPieces_joiningSeam_weight_eq_three
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (i : ℕ) (hi : i + 1 < (componentIntervalPieces p hk hp).length)
    (hnotPositive :
      (componentIntervalPieces p hk hp)[i + 1].start ∉
        componentPositiveSeams p) :
    Hunter.ProofsLedger.bw p
      (componentIntervalPieces p hk hp)[i + 1].start = 3 := by
  let seam := (componentIntervalPieces p hk hp)[i + 1].start
  have hseam : seam ∈ componentSeams p :=
    componentIntervalPieces_joiningSeam p hk hp i hi
  have hge := componentSeam_weight_ge_three hk hp hseam
  dsimp [seam] at hge
  by_contra hne
  apply hnotPositive
  refine Finset.mem_filter.mpr ⟨hseam, ?_⟩
  omega

/-- 一列实际片按端点首尾相接，且相邻接缝均为精确权三。 -/
structure ExactWeightThreePieceChain (p : HPath k) where
  pieces : List (ComponentIntervalPiece p)
  nonempty : pieces ≠ []
  consecutive : ∀ i, (hi : i + 1 < pieces.length) →
    (pieces.get ⟨i, by omega⟩).stop =
      (pieces.get ⟨i + 1, by omega⟩).start
  seamWeight : ∀ i, (hi : i + 1 < pieces.length) →
    Hunter.ProofsLedger.bw p (pieces.get ⟨i + 1, by omega⟩).start = 3

/-- 列表中每对相邻元素都满足关系 `R`。 -/
private def ListAdjacent {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => R x y ∧ ListAdjacent R (y :: xs)

/-- `ListAdjacent` 可在任意合法相邻下标处取出关系证书。 -/
private theorem listAdjacent_get
    {α : Type} {R : α → α → Prop} {xs : List α}
    (hadj : ListAdjacent R xs) (i : ℕ) (hi : i + 1 < xs.length) :
    R xs[i] xs[i + 1] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases xs with
      | nil => simp at hi
      | cons y ys =>
          change R x y ∧ ListAdjacent R (y :: ys) at hadj
          cases i with
          | zero => simpa using hadj.1
          | succ i =>
              have hi' : i + 1 < (y :: ys).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              simpa only [List.getElem_cons_succ] using ih hadj.2 i hi'

/-- 逐下标相邻关系证书可合成为 `ListAdjacent`。 -/
private theorem listAdjacent_of_get
    {α : Type} {R : α → α → Prop} {xs : List α}
    (hget : ∀ i, (hi : i + 1 < xs.length) → R xs[i] xs[i + 1]) :
    ListAdjacent R xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      cases xs with
      | nil => trivial
      | cons y ys =>
          change R x y ∧ ListAdjacent R (y :: ys)
          constructor
          · simpa using hget 0 (by simp)
          · apply ih
            intro i hi
            have hall := hget (i + 1) (by
              simp only [List.length_cons] at hi ⊢
              omega)
            simpa only [List.getElem_cons_succ, Nat.add_assoc] using hall

/-- 相邻关系失败的次数。 -/
private def adjacentFailureCount
    {α : Type} (R : α → α → Prop) [DecidableRel R] : List α → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => (if R x y then 0 else 1) +
      adjacentFailureCount R (y :: xs)

/-- 逐点等价的相邻关系具有相同失败计数，与所选判定实例无关。 -/
private theorem adjacentFailureCount_congr
    {α : Type} {R S : α → α → Prop}
    [DecidableRel R] [DecidableRel S]
    (hiff : ∀ left right, R left right ↔ S left right)
    (xs : List α) :
    adjacentFailureCount R xs = adjacentFailureCount S xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp only [adjacentFailureCount, ih]
          by_cases hR : R x y
          · have hS : S x y := (hiff x y).mp hR
            simp [hR, hS]
          · have hS : ¬ S x y := by
              intro hSy
              exact hR ((hiff x y).mpr hSy)
            simp [hR, hS]

/-- 单点性质失败的次数。 -/
private def propertyFailureCount
    {α : Type} (Q : α → Prop) [DecidablePred Q] : List α → ℕ
  | [] => 0
  | x :: xs => (if Q x then 0 else 1) + propertyFailureCount Q xs

/-- 若第一项相邻条件处处成立，则合取关系的失败次数只计算右元素性质失败。 -/
private theorem adjacentFailureCount_and_of_adjacent
    {α : Type} {C : α → α → Prop} {Q : α → Prop}
    [DecidableRel C] [DecidablePred Q] {xs : List α}
    (hconnected : ListAdjacent C xs) :
    adjacentFailureCount (fun left right => C left right ∧ Q right) xs =
      propertyFailureCount Q xs.tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          change C x y ∧ ListAdjacent C (y :: ys) at hconnected
          simp only [adjacentFailureCount, List.tail_cons,
            propertyFailureCount, ih hconnected.2]
          by_cases hQ : Q y <;> simp [hconnected.1, hQ]

/-- 单点失败计数与映射交换。 -/
private theorem propertyFailureCount_map
    {α β : Type} (Q : β → Prop) [DecidablePred Q]
    (f : α → β) (xs : List α) :
    propertyFailureCount Q (xs.map f) =
      propertyFailureCount (fun x => Q (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, propertyFailureCount, ih]

/-- 单点失败计数等于筛出失败元素后的列表长度。 -/
private theorem propertyFailureCount_eq_filter_length
    {α : Type} (Q : α → Prop) [DecidablePred Q] (xs : List α) :
    propertyFailureCount Q xs =
      (xs.filter fun x => decide (¬ Q x)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [propertyFailureCount, List.filter_cons]
      by_cases hQ : Q x <;> simp [hQ, ih, Nat.add_comm]

/--
`ListChainPartition R source groups` 表示把源列表只在 `R` 失败的相邻位置切开。
构造子同时记录每组首元素，因此后续不需要从扁平化等式反推非空性。
-/
private inductive ListChainPartition {α : Type} (R : α → α → Prop) :
    List α → List (List α) → Prop
  | nil : ListChainPartition R [] []
  | single (x : α) : ListChainPartition R [x] [[x]]
  | join {x y : α} {ys tail : List α} {groups : List (List α)}
      (hxy : R x y)
      (rest : ListChainPartition R (y :: ys) ((y :: tail) :: groups)) :
      ListChainPartition R (x :: y :: ys) ((x :: y :: tail) :: groups)
  | cut {x y : α} {ys tail : List α} {groups : List (List α)}
      (hxy : ¬ R x y)
      (rest : ListChainPartition R (y :: ys) ((y :: tail) :: groups)) :
      ListChainPartition R (x :: y :: ys) ([x] :: (y :: tail) :: groups)

/-- 任意非空列表都存在按 `R` 的链分区，且第一组仍以原首元素开头。 -/
private theorem exists_listChainPartition_nonempty
    {α : Type} (R : α → α → Prop) [DecidableRel R]
    (x : α) (xs : List α) :
    ∃ tail groups,
      ListChainPartition R (x :: xs) ((x :: tail) :: groups) := by
  induction xs generalizing x with
  | nil => exact ⟨[], [], ListChainPartition.single x⟩
  | cons y ys ih =>
      obtain ⟨tail, groups, hrest⟩ := ih y
      by_cases hxy : R x y
      · exact ⟨y :: tail, groups, ListChainPartition.join hxy hrest⟩
      · exact ⟨[], (y :: tail) :: groups,
          ListChainPartition.cut hxy hrest⟩

/-- 任意列表（含空列表）都存在按 `R` 的链分区。 -/
private theorem exists_listChainPartition
    {α : Type} (R : α → α → Prop) [DecidableRel R]
    (xs : List α) : ∃ groups, ListChainPartition R xs groups := by
  cases xs with
  | nil => exact ⟨[], ListChainPartition.nil⟩
  | cons x xs =>
      obtain ⟨tail, groups, hpartition⟩ :=
        exists_listChainPartition_nonempty R x xs
      exact ⟨(x :: tail) :: groups, hpartition⟩

/-- 链分区中的每一组均非空。 -/
private theorem ListChainPartition.groups_nonempty
    {α : Type} {R : α → α → Prop} {source : List α}
    {groups : List (List α)}
    (hpartition : ListChainPartition R source groups) :
    ∀ group ∈ groups, group ≠ [] := by
  induction hpartition with
  | nil => simp
  | single x => simp
  | join hxy rest ih =>
      intro group hgroup
      rcases List.mem_cons.mp hgroup with rfl | hgroup
      · simp
      · exact ih group (List.mem_cons_of_mem _ hgroup)
  | cut hxy rest ih =>
      intro group hgroup
      rcases List.mem_cons.mp hgroup with rfl | hgroup
      · simp
      · exact ih group hgroup

/-- 链分区中的每一组内部均处处满足 `R`。 -/
private theorem ListChainPartition.groups_adjacent
    {α : Type} {R : α → α → Prop} {source : List α}
    {groups : List (List α)}
    (hpartition : ListChainPartition R source groups) :
    ∀ group ∈ groups, ListAdjacent R group := by
  induction hpartition with
  | nil => simp
  | single x => simp [ListAdjacent]
  | @join x y ys tail groups hxy rest ih =>
      intro group hgroup
      rcases List.mem_cons.mp hgroup with rfl | hgroup
      · change R x y ∧ ListAdjacent R (y :: tail)
        exact ⟨hxy, ih (y :: tail) List.mem_cons_self⟩
      · exact ih group (List.mem_cons_of_mem _ hgroup)
  | @cut x y ys tail groups hxy rest ih =>
      intro group hgroup
      rcases List.mem_cons.mp hgroup with rfl | hgroup
      · simp [ListAdjacent]
      · exact ih group hgroup

/-- 链分区所有组按序扁平化后精确还原源列表。 -/
private theorem ListChainPartition.flatten_eq
    {α : Type} {R : α → α → Prop} {source : List α}
    {groups : List (List α)}
    (hpartition : ListChainPartition R source groups) :
    groups.flatten = source := by
  induction hpartition with
  | nil => rfl
  | single x => simp
  | @join x y ys tail groups hxy rest ih =>
      simp only [List.flatten_cons, List.cons_append] at ih ⊢
      exact congrArg (x :: ·) ih
  | @cut x y ys tail groups hxy rest ih =>
      simp only [List.flatten_cons, List.cons_append, List.nil_append] at ih ⊢
      exact congrArg (x :: ·) ih

/-- 链分区的组数恰为相邻关系失败次数加一（空源列表时两边均为零）。 -/
private theorem ListChainPartition.groups_length_eq_failureCount
    {α : Type} {R : α → α → Prop} [DecidableRel R]
    {source : List α} {groups : List (List α)}
    (hpartition : ListChainPartition R source groups) :
    groups.length = adjacentFailureCount R source +
      (if source = [] then 0 else 1) := by
  induction hpartition with
  | nil => rfl
  | single x => simp [adjacentFailureCount]
  | join hxy rest ih =>
      simpa [adjacentFailureCount, hxy] using ih
  | cut hxy rest ih =>
      simp [adjacentFailureCount, hxy] at ih ⊢
      omega

/-- 两个带证书实际片之间形成一条精确权三链内接缝。 -/
def ExactPieceJoin {p : HPath k}
    (left right : ComponentIntervalPiece p) : Prop :=
  left.stop = right.start ∧
    Hunter.ProofsLedger.bw p right.start = 3

attribute [local instance] Classical.propDecidable

/-- 组件片列表去掉首片后的起点列表正是全部有序 seam。 -/
theorem componentIntervalPieces_tail_starts
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    (componentIntervalPieces p hk hp).tail.map ComponentIntervalPiece.start =
      componentSeamList p := by
  have hstarts := congrArg List.tail
    (componentIntervalPieces_starts p hk hp)
  simpa [componentPieceStarts] using hstarts

/-- 有序 seam 列表中非权三元素的数目恰为正剩余 seam 数。 -/
private theorem componentSeamList_failureCount_eq_positive_card
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    propertyFailureCount
        (fun j => Hunter.ProofsLedger.bw p j = 3)
        (componentSeamList p) =
      (componentPositiveSeams p).card := by
  classical
  let filtered := (componentSeamList p).filter fun j =>
    decide (Hunter.ProofsLedger.bw p j ≠ 3)
  have hnodup : filtered.Nodup := by
    exact (componentSeamList_nodup p).filter _
  have hfinset : filtered.toFinset = componentPositiveSeams p := by
    ext j
    simp only [filtered, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, componentPositiveSeams, Finset.mem_filter]
    constructor
    · rintro ⟨hjList, hjNotThree⟩
      have hjSeam := mem_componentSeamList.mp hjList
      refine ⟨hjSeam, ?_⟩
      have hge := componentSeam_weight_ge_three hk hp hjSeam
      omega
    · rintro ⟨hjSeam, hjPositive⟩
      refine ⟨mem_componentSeamList.mpr hjSeam, ?_⟩
      have hge := componentSeam_weight_ge_three hk hp hjSeam
      omega
  rw [propertyFailureCount_eq_filter_length]
  change filtered.length = (componentPositiveSeams p).card
  rw [← List.toFinset_card_of_nodup hnodup, hfinset]

/-- 实际组件片列表中非精确权三相邻位置的数目恰为正剩余 seam 数。 -/
private theorem componentIntervalPieces_failureCount_eq_positive_card
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    adjacentFailureCount ExactPieceJoin
        (componentIntervalPieces p hk hp) =
      (componentPositiveSeams p).card := by
  classical
  let source := componentIntervalPieces p hk hp
  have hconnected : ListAdjacent
      (fun left right : ComponentIntervalPiece p =>
        left.stop = right.start) source := by
    apply listAdjacent_of_get
    intro i hi
    exact componentIntervalPieces_consecutive p hk hp i hi
  calc
    adjacentFailureCount ExactPieceJoin source =
        adjacentFailureCount
          (fun left right : ComponentIntervalPiece p =>
            left.stop = right.start ∧
              Hunter.ProofsLedger.bw p right.start = 3) source := by
      apply adjacentFailureCount_congr
      intro left right
      rfl
    _ =
        propertyFailureCount
          (fun right : ComponentIntervalPiece p =>
            Hunter.ProofsLedger.bw p right.start = 3) source.tail := by
      exact adjacentFailureCount_and_of_adjacent
        (C := fun left right : ComponentIntervalPiece p =>
          left.stop = right.start)
        (Q := fun right : ComponentIntervalPiece p =>
          Hunter.ProofsLedger.bw p right.start = 3)
        hconnected
    _ = propertyFailureCount
          (fun j => Hunter.ProofsLedger.bw p j = 3)
          (source.tail.map ComponentIntervalPiece.start) := by
      symm
      exact propertyFailureCount_map
        (fun j => Hunter.ProofsLedger.bw p j = 3)
        ComponentIntervalPiece.start source.tail
    _ = propertyFailureCount
          (fun j => Hunter.ProofsLedger.bw p j = 3)
          (componentSeamList p) := by
      rw [show source.tail.map ComponentIntervalPiece.start =
          componentSeamList p by
        exact componentIntervalPieces_tail_starts p hk hp]
    _ = (componentPositiveSeams p).card :=
      componentSeamList_failureCount_eq_positive_card p hk hp

/-- 非空且逐邻接满足 `ExactPieceJoin` 的片列表提升为精确权三链。 -/
private noncomputable def exactWeightThreePieceChainOfList
    {p : HPath k} (pieces : List (ComponentIntervalPiece p))
    (hnonempty : pieces ≠ [])
    (hadjacent : ListAdjacent ExactPieceJoin pieces) :
    ExactWeightThreePieceChain p where
  pieces := pieces
  nonempty := hnonempty
  consecutive := by
    intro i hi
    exact (listAdjacent_get hadjacent i hi).1
  seamWeight := by
    intro i hi
    exact (listAdjacent_get hadjacent i hi).2

/--
任意实际组件片列表都可在非精确权三 seam 处切成非空精确权三链；所有链的片列表
扁平化后精确还原原组件片列表，不遗漏也不重复任何片。
-/
theorem exists_componentExactWeightThreeChainPartition
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    ∃ chains : List (ExactWeightThreePieceChain p),
      (chains.map ExactWeightThreePieceChain.pieces).flatten =
        componentIntervalPieces p hk hp ∧
      chains.length = (componentPositiveSeams p).card + 1 := by
  classical
  let source := componentIntervalPieces p hk hp
  obtain ⟨groups, hpartition⟩ :=
    exists_listChainPartition ExactPieceJoin source
  have hnonempty := hpartition.groups_nonempty
  have hadjacent := hpartition.groups_adjacent
  let chains : List (ExactWeightThreePieceChain p) :=
    groups.attach.map fun group =>
      exactWeightThreePieceChainOfList group.val
        (hnonempty group.val group.property)
        (hadjacent group.val group.property)
  refine ⟨chains, ?_, ?_⟩
  · simp only [chains, List.map_map]
    change (groups.attach.map (fun group => group.val)).flatten =
      componentIntervalPieces p hk hp
    rw [show groups.attach.map (fun group => group.val) = groups.attach.unattach by rfl,
      List.unattach_attach]
    simpa [source] using hpartition.flatten_eq
  · have hsourceNonempty : source ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [source]
      rw [componentIntervalPieces_length]
      unfold componentPieceCount
      omega
    simp only [chains, List.length_map, List.length_attach]
    rw [hpartition.groups_length_eq_failureCount, if_neg hsourceNonempty]
    change adjacentFailureCount ExactPieceJoin source + 1 = _
    rw [show adjacentFailureCount ExactPieceJoin source =
        (componentPositiveSeams p).card by
      exact componentIntervalPieces_failureCount_eq_positive_card p hk hp]

/-- 精确权三链分区的链数至多为 seam 剩余 `x` 加一。 -/
theorem exists_componentExactWeightThreeChainPartition_card_le_residual
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    ∃ chains : List (ExactWeightThreePieceChain p),
      (chains.map ExactWeightThreePieceChain.pieces).flatten =
        componentIntervalPieces p hk hp ∧
      chains.length ≤ componentSeamResidual p + 1 := by
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p hk hp
  refine ⟨chains, hflatten, ?_⟩
  have hcuts := componentPositiveSeams_card_le_residual (p := p)
  omega

/-- 没有正剩余 seam 时，整个组件实际片列表本身就是一条精确权三链。 -/
noncomputable def componentExactWeightThreeChain_of_no_positive
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (hnoPositive : componentPositiveSeams p = ∅) :
    ExactWeightThreePieceChain p where
  pieces := componentIntervalPieces p hk hp
  nonempty := by
    apply List.ne_nil_of_length_pos
    rw [componentIntervalPieces_length]
    unfold componentPieceCount
    omega
  consecutive := by
    intro i hi
    exact componentIntervalPieces_consecutive p hk hp i hi
  seamWeight := by
    intro i hi
    apply componentIntervalPieces_joiningSeam_weight_eq_three p hk hp i hi
    rw [hnoPositive]
    simp

/-- 组件 seam 剩余为零时不存在正剩余切割点。 -/
theorem componentPositiveSeams_eq_empty_of_residual_zero
    {p : HPath k} (hresidual : componentSeamResidual p = 0) :
    componentPositiveSeams p = ∅ := by
  apply Finset.card_eq_zero.mp
  have hle := componentPositiveSeams_card_le_residual (p := p)
  omega

/-- `x=0` 的实际组件直接生成唯一未切分的精确权三链证书。 -/
noncomputable def componentExactWeightThreeChain_of_residual_zero
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (hresidual : componentSeamResidual p = 0) :
    ExactWeightThreePieceChain p :=
  componentExactWeightThreeChain_of_no_positive p hk hp
    (componentPositiveSeams_eq_empty_of_residual_zero hresidual)

/-- 一列实际片的总长度。 -/
def pieceListTotalSize {p : HPath k}
    (pieces : List (ComponentIntervalPiece p)) : ℕ :=
  (pieces.map ComponentIntervalPiece.size).sum

/-- 一列实际片的总缺口。 -/
def pieceListTotalDeficit {p : HPath k}
    (pieces : List (ComponentIntervalPiece p)) : ℕ :=
  (pieces.map ComponentIntervalPiece.deficit).sum

/-- 任意实际片列表的总长度与总缺口精确分割满容量。 -/
theorem pieceListTotalSize_add_deficit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (pieces : List (ComponentIntervalPiece p)) :
    pieceListTotalSize pieces + pieceListTotalDeficit pieces =
      (k - 1) * pieces.length := by
  induction pieces with
  | nil => simp [pieceListTotalSize, pieceListTotalDeficit]
  | cons piece pieces ih =>
      have hpiece := ComponentIntervalPiece.size_add_deficit hk hp piece
      simp only [pieceListTotalSize, pieceListTotalDeficit, List.map_cons,
        List.sum_cons, List.length_cons]
      change piece.size + (pieces.map ComponentIntervalPiece.size).sum +
        (piece.deficit + (pieces.map ComponentIntervalPiece.deficit).sum) = _
      have ih' :
          (pieces.map ComponentIntervalPiece.size).sum +
              (pieces.map ComponentIntervalPiece.deficit).sum =
            (k - 1) * pieces.length := ih
      rw [Nat.mul_succ]
      omega

/-- 组件实际片列表的总大小精确等于组件旋转块数。 -/
theorem componentIntervalPieces_totalSize
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    pieceListTotalSize (componentIntervalPieces p hk hp) =
      componentClassCount p := by
  rw [pieceListTotalSize, componentIntervalPieces_sizes,
    componentPieceSizes_sum]

/-- 组件实际片列表的总缺口精确等于正文的组件缺口 `Δ`。 -/
theorem componentIntervalPieces_totalDeficit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    pieceListTotalDeficit (componentIntervalPieces p (by omega) hp) =
      componentPieceDeficit p := by
  have htotal := pieceListTotalSize_add_deficit hk hp
    (componentIntervalPieces p (by omega) hp)
  rw [componentIntervalPieces_totalSize,
    componentIntervalPieces_length] at htotal
  have hcomponent := componentClassCount_add_deficit hk hp
  omega

/-- 精确权三链分区的逐链片数之和等于组件片数 `r`。 -/
theorem exactWeightThreeChainPartition_pieceCount_sum
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p))
    (hflatten : (chains.map ExactWeightThreePieceChain.pieces).flatten =
      componentIntervalPieces p hk hp) :
    (chains.map fun chain => chain.pieces.length).sum =
      componentPieceCount p := by
  have hlength := congrArg List.length hflatten
  simpa [Function.comp_def] using hlength

/-- 精确权三链分区的逐链总大小之和等于组件旋转块数 `t`。 -/
theorem exactWeightThreeChainPartition_totalSize_sum
    (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p))
    (hflatten : (chains.map ExactWeightThreePieceChain.pieces).flatten =
      componentIntervalPieces p hk hp) :
    (chains.map fun chain => pieceListTotalSize chain.pieces).sum =
      componentClassCount p := by
  calc
    (chains.map fun chain => pieceListTotalSize chain.pieces).sum =
        pieceListTotalSize
          (chains.map ExactWeightThreePieceChain.pieces).flatten := by
      clear hflatten
      induction chains with
      | nil => simp [pieceListTotalSize]
      | cons chain chains ih =>
          simp [pieceListTotalSize, Function.comp_def]
    _ = pieceListTotalSize (componentIntervalPieces p hk hp) := by
      rw [hflatten]
    _ = componentClassCount p :=
      componentIntervalPieces_totalSize p hk hp

/-- 精确权三链分区的逐链总缺口之和等于组件缺口 `Δ`。 -/
theorem exactWeightThreeChainPartition_totalDeficit_sum
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p))
    (hflatten : (chains.map ExactWeightThreePieceChain.pieces).flatten =
      componentIntervalPieces p (by omega) hp) :
    (chains.map fun chain => pieceListTotalDeficit chain.pieces).sum =
      componentPieceDeficit p := by
  calc
    (chains.map fun chain => pieceListTotalDeficit chain.pieces).sum =
        pieceListTotalDeficit
          (chains.map ExactWeightThreePieceChain.pieces).flatten := by
      clear hflatten
      induction chains with
      | nil => simp [pieceListTotalDeficit]
      | cons chain chains ih =>
          simp [pieceListTotalDeficit, Function.comp_def]
    _ = pieceListTotalDeficit
          (componentIntervalPieces p (by omega) hp) := by
      rw [hflatten]
    _ = componentPieceDeficit p :=
      componentIntervalPieces_totalDeficit hk hp

end PreimageChain

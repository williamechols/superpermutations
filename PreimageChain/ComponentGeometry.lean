import Hunter.ProofsLedger
import Hunter.ProofsLink2
import PreimageChain.TerminalPortal

/-!
# 实际组件的区间片参数

对 strongly-exitless 组件路径，长度是 `k` 的倍数，每个长度 `k` 的块是一条完整
旋转类。权二块边界连接同一 interval piece；其余边界是接缝。本模块定义实际
`t,r,Δ,x`，并把 Hunter 的逐边 excess 恒等式重索引到接缝。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- strongly-exitless 路径访问的完整旋转类数。 -/
def componentClassCount (p : HPath k) : ℕ := p.numVerts / k

/-- 全部相邻旋转块边界，编号为 `1,…,t-1`。 -/
def componentBoundaries (p : HPath k) : Finset ℕ :=
  Finset.Icc 1 (componentClassCount p - 1)

/-- 非权二块边界，即 interval pieces 之间的接缝。 -/
noncomputable def componentSeams (p : HPath k) : Finset ℕ :=
  (componentBoundaries p).filter fun j => Hunter.ProofsLedger.bw p j ≠ 2

/-- interval piece 数；非空组件至少有一片。 -/
noncomputable def componentPieceCount (p : HPath k) : ℕ :=
  (componentSeams p).card + 1

/-- 按真实块号递增排列的接缝列表。 -/
noncomputable def componentSeamList (p : HPath k) : List ℕ :=
  (componentSeams p).sort (· ≤ ·)

/-- 每个 interval piece 的起始块号；首片从块 `0` 开始。 -/
noncomputable def componentPieceStarts (p : HPath k) : List ℕ :=
  0 :: componentSeamList p

/-- 每个 interval piece 的右开终点块号；末片止于组件块数。 -/
noncomputable def componentPieceStops (p : HPath k) : List ℕ :=
  componentSeamList p ++ [componentClassCount p]

/-- 按路径顺序排列的实际片长度。 -/
noncomputable def componentPieceSizes (p : HPath k) : List ℕ :=
  List.zipWith (fun start stop => stop - start)
    (componentPieceStarts p) (componentPieceStops p)

/-- 按路径顺序排列的逐片缺口 `δ=(k-1)-size`。 -/
noncomputable def componentPieceDeficits (p : HPath k) : List ℕ :=
  (componentPieceSizes p).map fun size => k - 1 - size

@[simp] theorem componentSeamList_length (p : HPath k) :
    (componentSeamList p).length = (componentSeams p).card := by
  simp [componentSeamList, Finset.length_sort]

@[simp] theorem componentPieceStarts_length (p : HPath k) :
    (componentPieceStarts p).length = componentPieceCount p := by
  simp [componentPieceStarts, componentPieceCount]

@[simp] theorem componentPieceStops_length (p : HPath k) :
    (componentPieceStops p).length = componentPieceCount p := by
  simp [componentPieceStops, componentPieceCount]

@[simp] theorem componentPieceSizes_length (p : HPath k) :
    (componentPieceSizes p).length = componentPieceCount p := by
  rw [componentPieceSizes, List.length_zipWith,
    componentPieceStarts_length, componentPieceStops_length, Nat.min_self]

@[simp] theorem componentPieceDeficits_length (p : HPath k) :
    (componentPieceDeficits p).length = componentPieceCount p := by
  simp [componentPieceDeficits]

theorem componentSeamList_pairwise (p : HPath k) :
    (componentSeamList p).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort _ _

theorem componentSeamList_nodup (p : HPath k) :
    (componentSeamList p).Nodup := by
  exact Finset.sort_nodup _ _

@[simp] theorem mem_componentSeamList {p : HPath k} {j : ℕ} :
    j ∈ componentSeamList p ↔ j ∈ componentSeams p := by
  exact Finset.mem_sort _

/-- 单调自然数断点的相邻差之和等于总区间长度。 -/
theorem sum_adjacent_differences
    (a z : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hupper : ∀ x ∈ a :: xs, x ≤ z) :
    (List.zipWith (fun start stop => stop - start)
      (a :: xs) (xs ++ [z])).sum = z - a := by
  induction xs generalizing a with
  | nil =>
      have haz := hupper a List.mem_cons_self
      simp
  | cons x xs ih =>
      have hpc := List.pairwise_cons.mp hsorted
      have hax : a ≤ x := hpc.1 x List.mem_cons_self
      have hupperTail : ∀ y ∈ x :: xs, y ≤ z := by
        intro y hy
        exact hupper y (List.mem_cons_of_mem a hy)
      have hih := ih x hpc.2 hupperTail
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [hih]
      have hxz := hupperTail x List.mem_cons_self
      omega

/-- 有序实际片长度逐项求和恰为组件的旋转块总数。 -/
theorem componentPieceSizes_sum (p : HPath k) :
    (componentPieceSizes p).sum = componentClassCount p := by
  have hsorted : (0 :: componentSeamList p).Pairwise (· ≤ ·) := by
    rw [List.pairwise_cons]
    exact ⟨fun _ _ => Nat.zero_le _, componentSeamList_pairwise p⟩
  have hupper : ∀ x ∈ 0 :: componentSeamList p,
      x ≤ componentClassCount p := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hseam : x ∈ componentSeams p := mem_componentSeamList.mp hx
      have hboundary := (Finset.mem_filter.mp hseam).1
      rw [componentBoundaries, Finset.mem_Icc] at hboundary
      omega
  simpa [componentPieceSizes, componentPieceStarts, componentPieceStops] using
    sum_adjacent_differences 0 (componentClassCount p)
      (componentSeamList p) hsorted hupper

/-- 总片缺口 `Δ=(k-1)r-t`。 -/
noncomputable def componentPieceDeficit (p : HPath k) : ℕ :=
  (k - 1) * componentPieceCount p - componentClassCount p

/-- 接缝超过基准权三的总剩余 `x=Σ(w-3)`。 -/
noncomputable def componentSeamResidual (p : HPath k) : ℕ :=
  ∑ j ∈ componentSeams p, (Hunter.ProofsLedger.bw p j - 3)

/-- 正接缝剩余（即权至少四）的切割点。 -/
noncomputable def componentPositiveSeams (p : HPath k) : Finset ℕ :=
  (componentSeams p).filter fun j =>
    0 < Hunter.ProofsLedger.bw p j - 3

/-- 留在精确权三片链内部的接缝。 -/
noncomputable def componentExactThreeSeams (p : HPath k) : Finset ℕ :=
  (componentSeams p).filter fun j => Hunter.ProofsLedger.bw p j = 3

/-- 末片为满片：最后一个旋转块处的门游程深度达到 `k-2`。 -/
def componentLastPieceFull (p : HPath k) : Prop :=
  Hunter.ProofsLedger.IsComplete p (componentClassCount p - 1)

/-- 完整门游程头的 `Ψ` 坐标就是该门游程的第二个旋转块起点。 -/
theorem psi_of_complete_run_head
    (hk : 3 ≤ k) {base : List ℕ} (hbase : base.length = k - 1)
    {m : ℕ} {h : Vtx k}
    (hhead : h.1 = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 2) ++ [m])) :
    (psi h).1 = base.rotate 1 ++ [m] := by
  have htau₁ := Hunter.ProofsRigidity2.tau2_step
    (by omega : 2 ≤ k) hbase m (k - 2)
  have hperiod : base.rotate (k - 1) = base := by
    rw [← hbase, List.rotate_length]
  have hfirstDoor :
      door (Hunter.ProofsRigidity2.bexit k (base.rotate (k - 2) ++ [m])) =
        base ++ [m] := by
    change Hunter.ProofsRigidity2.tau2 k
      (base.rotate (k - 2) ++ [m]) = base ++ [m]
    rw [htau₁, show k - 2 + 1 = k - 1 by omega, hperiod]
  have htau₂ := Hunter.ProofsRigidity2.tau2_step
    (by omega : 2 ≤ k) hbase m 0
  change (tau (sigmaInv (tau h))).1 = _
  rw [Hunter.tau_val_of_door
    (Hunter.door_isPermWord (by omega) (sigmaInv (tau h)).2)]
  change door ((tau h).1.rotate (k - 1)) = _
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) h.2)]
  rw [hhead, hfirstDoor]
  change Hunter.ProofsRigidity2.tau2 k (base ++ [m]) = _
  simpa using htau₂

theorem component_numVerts_eq
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    p.numVerts = k * componentClassCount p := by
  unfold componentClassCount
  exact (Nat.mul_div_cancel' (Hunter.Proved.dvd_numVerts_of_stronglyExitless
    hk hp)).symm

theorem componentClassCount_pos
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    0 < componentClassCount p := by
  have hN := component_numVerts_eq hk hp
  have hpN := p.numVerts_pos
  have hmul : 0 < k * componentClassCount p := by rwa [← hN]
  by_contra hzero
  have hcount : componentClassCount p = 0 := by omega
  rw [hcount, Nat.mul_zero] at hmul
  omega

theorem componentBoundary_weight_ge_two
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {j : ℕ} (hj : j ∈ componentBoundaries p) :
    2 ≤ Hunter.ProofsLedger.bw p j := by
  rw [componentBoundaries, Finset.mem_Icc] at hj
  have hN := component_numVerts_eq hk hp
  have hjlt : j < componentClassCount p := by omega
  have hindex : k * j - 1 + 1 = k * j := by
    have : 1 ≤ k * j := Nat.mul_pos hk hj.1
    omega
  unfold Hunter.ProofsLedger.bw
  have hi : k * j - 1 + 1 < p.numVerts := by
    rw [hindex, hN]
    exact Nat.mul_lt_mul_of_pos_left hjlt hk
  have hd : k ∣ k * j - 1 + 1 := by
    rw [hindex]
    exact ⟨j, rfl⟩
  simpa [hindex] using
    (Hunter.ProofsWindow.boundary_ge_two hk hp.1 hi hd)

/-- 在组件边界内，“不是接缝”等价于权二门。 -/
theorem componentBoundary_door_iff_not_seam
    {p : HPath k} {j : ℕ} (hj : j ∈ componentBoundaries p) :
    Hunter.ProofsLedger.IsDoor p j ↔ j ∉ componentSeams p := by
  simp [componentSeams, hj, Hunter.ProofsLedger.IsDoor]

/-- 每个实际接缝的边权至少为三。 -/
theorem componentSeam_weight_ge_three
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {j : ℕ} (hj : j ∈ componentSeams p) :
    3 ≤ Hunter.ProofsLedger.bw p j := by
  have hmem := Finset.mem_filter.mp hj
  have hge := componentBoundary_weight_ge_two hk hp hmem.1
  omega

/-- 接缝剩余为零恰好是精确权三接缝。 -/
theorem componentSeam_residual_eq_zero_iff
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {j : ℕ} (hj : j ∈ componentSeams p) :
    Hunter.ProofsLedger.bw p j - 3 = 0 ↔
      Hunter.ProofsLedger.bw p j = 3 := by
  have hge := componentSeam_weight_ge_three hk hp hj
  omega

/-- 正剩余接缝恰好是边权至少四的切割点。 -/
theorem componentSeam_residual_pos_iff
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {j : ℕ} (hj : j ∈ componentSeams p) :
    0 < Hunter.ProofsLedger.bw p j - 3 ↔
      4 ≤ Hunter.ProofsLedger.bw p j := by
  have hge := componentSeam_weight_ge_three hk hp hj
  omega

/-- 每个正剩余切割点至少消耗一个单位，故切割数不超过组件接缝剩余 `x`。 -/
theorem componentPositiveSeams_card_le_residual
    {p : HPath k} :
    (componentPositiveSeams p).card ≤ componentSeamResidual p := by
  calc
    (componentPositiveSeams p).card =
        ∑ j ∈ componentPositiveSeams p, 1 := by simp
    _ ≤ ∑ j ∈ componentPositiveSeams p,
        (Hunter.ProofsLedger.bw p j - 3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hpos := (Finset.mem_filter.mp hj).2
      omega
    _ ≤ ∑ j ∈ componentSeams p,
        (Hunter.ProofsLedger.bw p j - 3) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro j _ _
      omega
    _ = componentSeamResidual p := by rfl

/-- 可整除的真实边位置恰由块边界编号 `j ↦ kj-1` 给出。 -/
theorem component_boundary_index_set
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    (Finset.range (p.numVerts - 1)).filter (fun i => k ∣ i + 1) =
      (componentBoundaries p).image (fun j => k * j - 1) := by
  have hN := component_numVerts_eq hk hp
  ext i
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hi, ⟨j, hj⟩⟩
    have hiPos : 1 ≤ i + 1 := by omega
    have hjPos : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      rw [this] at hj
      omega
    have hjlt : j < componentClassCount p := by
      have hiklt : i + 1 < p.numVerts := by omega
      have hmul : k * j < k * componentClassCount p := by
        rw [← hj, ← hN]
        exact hiklt
      exact Nat.lt_of_mul_lt_mul_left hmul
    refine ⟨j, ?_, ?_⟩
    · rw [componentBoundaries, Finset.mem_Icc]
      omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [componentBoundaries, Finset.mem_Icc] at hj
    have hjlt : j < componentClassCount p := by omega
    have hkj : 1 ≤ k * j := Nat.mul_pos hk hj.1
    have hmul : k * j < k * componentClassCount p :=
      Nat.mul_lt_mul_of_pos_left hjlt hk
    constructor
    · rw [hN]
      omega
    · rw [show k * j - 1 + 1 = k * j by omega]
      exact ⟨j, rfl⟩

/-- 组件路径的全部 excess 精确等于所有块边界的 `bw-2` 求和。 -/
theorem component_excess_eq_boundary_sum
    (hk : 3 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    Hunter.ProofsRecursion.excess p =
      ∑ j ∈ componentBoundaries p, (Hunter.ProofsLedger.bw p j - 2) := by
  rw [Hunter.ProofsMeta3.excess_eq_sum_edgeWeight (by omega) p]
  let f := fun i : ℕ => ew k (p.vert i) (p.vert (i + 1)) - 2
  calc
    (∑ i ∈ Finset.range (p.numVerts - 1), f i) =
        ∑ i ∈ Finset.range (p.numVerts - 1),
          if k ∣ i + 1 then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hd : k ∣ i + 1
      · simp [hd]
      · have hi' : i + 1 < p.numVerts := by omega
        have hw := (Hunter.Proved.prp_periodicedges (by omega) hp.1 hi').mpr hd
        simp [hd, f, hw]
    _ = ∑ i ∈ (Finset.range (p.numVerts - 1)).filter (fun i => k ∣ i + 1), f i := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ (componentBoundaries p).image (fun j => k * j - 1), f i := by
      rw [component_boundary_index_set (by omega) hp]
    _ = ∑ j ∈ componentBoundaries p, f (k * j - 1) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      change a ∈ componentBoundaries p at ha
      change b ∈ componentBoundaries p at hb
      rw [componentBoundaries, Finset.mem_Icc] at ha hb
      have hka : 1 ≤ k * a := Nat.mul_pos (by omega) ha.1
      have hkb : 1 ≤ k * b := Nat.mul_pos (by omega) hb.1
      have hmul : k * a = k * b := by
        calc
          k * a = (k * a - 1) + 1 := (Nat.sub_add_cancel hka).symm
          _ = (k * b - 1) + 1 := congrArg (fun n => n + 1) hab
          _ = k * b := Nat.sub_add_cancel hkb
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    _ = ∑ j ∈ componentBoundaries p, (Hunter.ProofsLedger.bw p j - 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [componentBoundaries, Finset.mem_Icc] at hj
      have hkj : 1 ≤ k * j := Nat.mul_pos (by omega) hj.1
      simp only [f, Hunter.ProofsLedger.bw]
      rw [show k * j - 1 + 1 = k * j by omega]

/-- excess 等于接缝数加接缝权三剩余。 -/
theorem component_excess_eq_piece_residual
    (hk : 3 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    Hunter.ProofsRecursion.excess p =
      componentPieceCount p - 1 + componentSeamResidual p := by
  rw [component_excess_eq_boundary_sum hk hp]
  have hfilter :
      (∑ j ∈ componentBoundaries p, (Hunter.ProofsLedger.bw p j - 2)) =
        ∑ j ∈ componentSeams p, (Hunter.ProofsLedger.bw p j - 2) := by
    unfold componentSeams
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases htwo : Hunter.ProofsLedger.bw p j = 2
    · simp [htwo]
    · simp [htwo]
  rw [hfilter]
  unfold componentPieceCount componentSeamResidual
  calc
    (∑ j ∈ componentSeams p, (Hunter.ProofsLedger.bw p j - 2)) =
        ∑ j ∈ componentSeams p,
          (1 + (Hunter.ProofsLedger.bw p j - 3)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjBoundary := (Finset.mem_filter.mp hj).1
      have hne := (Finset.mem_filter.mp hj).2
      have hge := componentBoundary_weight_ge_two (by omega) hp hjBoundary
      have hthree : 3 ≤ Hunter.ProofsLedger.bw p j := by omega
      omega
    _ = (componentSeams p).card +
        ∑ j ∈ componentSeams p, (Hunter.ProofsLedger.bw p j - 3) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (componentSeams p).card + 1 - 1 +
        ∑ j ∈ componentSeams p, (Hunter.ProofsLedger.bw p j - 3) := by omega

/-- 每个门游程至多含 `k-1` 个旋转类，故 `t ≤ (k-1)r`。 -/
theorem componentClassCount_le_piece_capacity
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    componentClassCount p ≤ (k - 1) * componentPieceCount p := by
  have hruns := Hunter.ProofsLink2.blocks_le_runs hk hp.1 p.numVerts_pos
  have hceil : p.numVerts ⌈/⌉ k = componentClassCount p := by
    rw [component_numVerts_eq (by omega) hp,
      Hunter.Proved.ceilDiv_of_dvd (by omega) ⟨componentClassCount p, rfl⟩,
      Nat.mul_div_cancel_left _ (by omega)]
  have hcount :
      Hunter.ProofsLink2.posBoundaryCount p (componentClassCount p) =
        (componentSeams p).card := by
    unfold Hunter.ProofsLink2.posBoundaryCount componentSeams componentBoundaries
    apply congrArg Finset.card
    ext j
    -- Lean 4.35 port: rewrite the filter membership before unfolding `IsDoor`.
    simp only [Finset.mem_filter]
    simp [Hunter.ProofsLedger.IsDoor]
  rw [hceil, hcount] at hruns
  simpa [componentPieceCount, Nat.mul_comm] using hruns

/-- `Δ=(k-1)r-t` 是精确差值，而非截断记号。 -/
theorem componentClassCount_add_deficit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    componentClassCount p + componentPieceDeficit p =
      (k - 1) * componentPieceCount p := by
  have hle := componentClassCount_le_piece_capacity hk hp
  unfold componentPieceDeficit
  omega

/-- 正文等式 `t=(k-1)r-Δ` 的整数版本。 -/
theorem componentClassCount_int_eq
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    (componentClassCount p : ℤ) =
      ((k : ℤ) - 1) * (componentPieceCount p : ℤ) -
        (componentPieceDeficit p : ℤ) := by
  have h := componentClassCount_add_deficit hk hp
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
  simp only [Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ k)] at hcast
  norm_num at hcast
  calc
    (componentClassCount p : ℤ) =
        ((componentClassCount p : ℤ) + (componentPieceDeficit p : ℤ)) -
          (componentPieceDeficit p : ℤ) := by ring
    _ = ((k : ℤ) - 1) * (componentPieceCount p : ℤ) -
          (componentPieceDeficit p : ℤ) := by rw [hcast]

/-- 末片满时，`Ψ(head)` 确实已在组件路径首点之后出现。 -/
theorem componentLastPieceFull_visit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hfull : componentLastPieceFull p) :
    psi p.last ∈ p.verts.tail := by
  let t := componentClassCount p
  have hN : p.numVerts = k * t := component_numVerts_eq (by omega) hp
  have ht : 0 < t := componentClassCount_pos (by omega) hp
  have hcomplete : Hunter.ProofsLedger.doorDepth p (t - 1) = k - 2 := by
    exact hfull
  have hdepth := Hunter.ProofsLedger.doorDepth_le p (t - 1)
  have htlarge : k - 1 ≤ t := by rw [hcomplete] at hdepth; omega
  let g0 := (t - 1) - (k - 2)
  have hg0 : g0 + (k - 2) = t - 1 := by
    dsimp [g0]
    omega
  have hdoor : ∀ r, 1 ≤ r → r ≤ k - 2 →
      ew k (p.vert (k * (g0 + r) - 1)) (p.vert (k * (g0 + r))) = 2 := by
    intro r hr1 hr2
    have hj : (k - 2) - r < Hunter.ProofsLedger.doorDepth p (t - 1) := by
      rw [hcomplete]
      omega
    have hd := Hunter.ProofsLedger.isDoor_of_lt_doorDepth p
      (t - 1) ((k - 2) - r) hj
    have hidx : (t - 1) - ((k - 2) - r) = g0 + r := by
      dsimp [g0]
      omega
    rw [hidx, Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] at hd
    exact hd
  have hNrun : k * (g0 + (k - 2)) < p.numVerts := by
    rw [hg0, hN]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hrun := Hunter.ProofsFillPath.blockrun_eq
    (by omega : 2 ≤ k) hp.1 g0 (k - 2) hNrun hdoor
  let m := (p.vert (k * g0) : List ℕ).getLastD 0
  let base := (p.vert (k * g0) : List ℕ).erase m
  have hbase : base.length = k - 1 := by
    dsimp [base, m]
    rw [Hunter.ProofsConfinement.erase_getLastD (p.vert (k * g0)).2.nodup,
      List.length_dropLast, (p.vert (k * g0)).2.length]
  have hlastBlock := hrun (k - 2) (le_refl _)
  rw [hg0] at hlastBlock
  change (p.vert (k * (t - 1)) : List ℕ) =
    base.rotate (k - 2) ++ [m] at hlastBlock
  have hlastIndex : p.numVerts - 1 = k * (t - 1) + (k - 1) := by
    have htEq : t = (t - 1) + 1 := by omega
    have hmul : k * t = k * (t - 1) + k := by
      calc
        k * t = k * ((t - 1) + 1) := congrArg (fun n => k * n) htEq
        _ = k * (t - 1) + k := Nat.mul_succ _ _
    rw [hN, hmul]
    omega
  have hBlt : k * (t - 1) + (k - 1) < p.numVerts := by
    rw [← hlastIndex]
    omega
  have hcycle :
      p.vert (k * (t - 1) + (k - 1)) =
        sigma^[k - 1] (p.vert (k * (t - 1))) :=
    Hunter.ProofsExitless.block_is_full_cycle (by omega) hp.1
      ⟨t - 1, rfl⟩ (by omega) hBlt
  have hhead : (p.last : List ℕ) = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 2) ++ [m]) := by
    rw [Hunter.Proved.last_eq_vert, hlastIndex, hcycle,
      Hunter.ProofsExitless.sigma_iter_val, hlastBlock]
    rfl
  have hpsiVal := psi_of_complete_run_head (by omega : 3 ≤ k) hbase hhead
  have hrunOne := hrun 1 (by omega)
  change (p.vert (k * (g0 + 1)) : List ℕ) = base.rotate 1 ++ [m] at hrunOne
  have hpsi : psi p.last = p.vert (k * (g0 + 1)) := by
    apply Subtype.ext
    exact hpsiVal.trans hrunOne.symm
  have hg1lt : g0 + 1 < t := by
    dsimp [g0]
    omega
  have hidxpos : 1 ≤ k * (g0 + 1) := Nat.mul_pos (by omega) (by omega)
  have hidxlt : k * (g0 + 1) < p.numVerts := by
    rw [hN]
    exact Nat.mul_lt_mul_of_pos_left hg1lt (by omega)
  rw [hpsi]
  simpa only [List.drop_one] using
    (Hunter.ProofsUnwind2.vert_mem_drop1 hidxpos hidxlt)

/-- 正文组件权重公式 `wt=(k+1)t+r+x-3` 的真实路径版本。 -/
theorem actual_component_weight_formula
    (hk : 3 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    p.wtP = (k + 1) * componentClassCount p +
      componentPieceCount p + componentSeamResidual p - 3 := by
  have hN := component_numVerts_eq (by omega) hp
  have ht := componentClassCount_pos (by omega) hp
  have hpieces : 1 ≤ componentPieceCount p := by
    unfold componentPieceCount
    omega
  have hexcess := component_excess_eq_piece_residual hk hp
  rw [Hunter.ProofsRecursion.wtP_decompose hk hp.1, hN] at ⊢
  have hceil : (k * componentClassCount p) ⌈/⌉ k = componentClassCount p := by
    rw [Hunter.Proved.ceilDiv_of_dvd (by omega) ⟨componentClassCount p, rfl⟩,
      Nat.mul_div_cancel_left _ (by omega)]
  have hmul :
      (k + 1) * componentClassCount p =
        k * componentClassCount p + componentClassCount p := by
    simp [Nat.add_mul]
  have hkt : 1 ≤ k * componentClassCount p :=
    Nat.mul_pos (by omega) ht
  have hnat :
      ∀ a t r x : ℕ, 1 ≤ a → 1 ≤ t → 1 ≤ r →
        (a - 1) + (t - 1) + (r - 1 + x) = a + t + r + x - 3 := by
    intro a t r x ha ht' hr
    omega
  rw [hceil, hexcess]
  calc
    (k * componentClassCount p - 1) + (componentClassCount p - 1) +
        (componentPieceCount p - 1 + componentSeamResidual p) =
      k * componentClassCount p + componentClassCount p +
        componentPieceCount p + componentSeamResidual p - 3 :=
      hnat _ _ _ _ hkt ht hpieces
    _ = (k + 1) * componentClassCount p + componentPieceCount p +
        componentSeamResidual p - 3 := by rw [hmul]

/-- 由实际组件路径直接得到的正文整数几何数据。 -/
noncomputable def componentGeometry (p : HPath k) : Geometry where
  t := componentClassCount p
  r := componentPieceCount p
  Delta := componentPieceDeficit p
  x := componentSeamResidual p
  mu := p.minto
  pValue := 1 + (p.minto : ℤ) + (p.wtP : ℤ)
  defect := D k * (1 + (p.minto : ℤ) + (p.wtP : ℤ)) -
    A k * componentClassCount p
  m := componentPieceDeficit p +
    (k - 1) * (componentSeamResidual p + (p.minto : ℤ) - 2)

/-- 真实 strongly-exitless 路径构造的几何数据满足正文公式 (16)。 -/
theorem componentGeometry_weightEquations
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    (componentGeometry p).WeightEquations k := by
  constructor
  · exact componentClassCount_int_eq hk hp
  · have hw := actual_component_weight_formula (by omega) hp
    have ht := componentClassCount_pos (by omega) hp
    have hbase :
        3 ≤ (k + 1) * componentClassCount p +
          componentPieceCount p + componentSeamResidual p := by
      have hkpos : 1 ≤ k + 1 := by omega
      have hprod : k + 1 ≤ (k + 1) * componentClassCount p :=
        Nat.le_mul_of_pos_right _ ht
      have hr : 1 ≤ componentPieceCount p := by
        unfold componentPieceCount
        omega
      omega
    change 1 + (p.minto : ℤ) + (p.wtP : ℤ) =
      ((k : ℤ) + 1) * (componentClassCount p : ℤ) +
        (componentPieceCount p : ℤ) + (componentSeamResidual p : ℤ) +
          (p.minto : ℤ) - 2
    rw [hw, Nat.cast_sub hbase]
    push_cast
    ring

/-- `defect,m` 字段按正文定义构造，故缺陷方程成立。 -/
theorem componentGeometry_defectEquations (p : HPath k) :
    (componentGeometry p).DefectEquations k := by
  constructor <;> rfl

/-- 非满 strongly-exitless 路径不可能从外部以权一进入，故 `minto ≥ 2`。 -/
theorem stronglyExitless_minto_ge_two
    (hk : 2 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hnonspanning : p.vertsFinset ≠ Finset.univ) :
    2 ≤ p.minto := by
  have hout : ∃ v : Vtx k, v ∉ p.vertsFinset := by
    by_contra h
    push Not at h
    exact hnonspanning (Finset.eq_univ_of_forall h)
  obtain ⟨u, hu⟩ := hout
  let S : Set ℕ :=
    {d | ∃ v : Vtx k, v ∉ p.verts ∧ ew k v p.first = d}
  have hSne : S.Nonempty := by
    refine ⟨ew k u p.first, u, ?_, rfl⟩
    exact fun humem => hu (HPath.mem_vertsFinset.mpr humem)
  have hmin : p.minto ∈ S := by
    unfold HPath.minto
    exact Nat.sInf_mem hSne
  obtain ⟨v, hvout, hvmin⟩ := hmin
  have hge : 1 ≤ ew k v p.first :=
    Hunter.ProofsExitless.ew_ge_one (by omega) v p.first
  have hne : ew k v p.first ≠ 1 := by
    intro hone
    have hfirst : p.first = sigma v :=
      (Hunter.ProofsExitless.ew_eq_one_iff (by omega)).mp hone
    have huoc : p.IsUnionOfCycles := Hunter.Proved.clm_1cyclesubset hp
    have hvin : v ∈ cyc p.first := by
      rw [hfirst]
      apply Hunter.ProofsExitless.mem_cyc.mpr
      exact (Hunter.ProofsExitless.mem_cyc.mp
        (by simpa using Hunter.ProofsExitless.sigma_iter_mem_cyc 1 v)).symm
    have hvfin : v ∈ p.vertsFinset := huoc p.first p.first_mem hvin
    exact hvout (HPath.mem_vertsFinset.mp hvfin)
  rw [← hvmin]
  omega

/-- 实际 `F(P)` 分量的有序路径满足正文组件权重公式。 -/
theorem actual_component_weight_formula_component
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 3 ≤ k)
    (C : ActualComponent P) :
    (actualComponentPath hP C).wtP =
      (k + 1) * componentClassCount (actualComponentPath hP C) +
        componentPieceCount (actualComponentPath hP C) +
          componentSeamResidual (actualComponentPath hP C) - 3 :=
  actual_component_weight_formula hk
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- 实际 `F(P)` 分量的正文整数几何记录。 -/
noncomputable def actualComponentGeometry
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Geometry :=
  componentGeometry (actualComponentPath hP C)

/-- 实际分量的末区间片为满片。 -/
def actualComponentLastPieceFull
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Prop :=
  componentLastPieceFull (actualComponentPath hP C)

/-- 论文的真实终端门户谓词：`μ=2` 且末区间片为满片。 -/
def ActualTerminalPortal
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Prop :=
  compMinto (F P) C.1 = 2 ∧ actualComponentLastPieceFull hP C

/-- “末片为满片”自动生成此前抽象记录的 `Ψ` 访问证书。 -/
theorem actualComponentLastPieceFull_certificate
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) (hfull : actualComponentLastPieceFull hP C) :
    TerminalFullVisitCertificate hP C := by
  unfold TerminalFullVisitCertificate
  rw [← actualComponentPath_last hP C]
  exact componentLastPieceFull_visit hk
    (actualComponentPath_stronglyExitless hP (by omega) C) hfull

theorem actualComponentGeometry_weightEquations
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) :
    (actualComponentGeometry hP C).WeightEquations k :=
  componentGeometry_weightEquations hk
    (actualComponentPath_stronglyExitless hP (by omega) C)

theorem actualComponentGeometry_defectEquations
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (actualComponentGeometry hP C).DefectEquations k :=
  componentGeometry_defectEquations _

/-- 实际分量的费率缺陷满足正文命题 6.1 的几何正规形。 -/
theorem actual_component_defect_geometry
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) :
    (actualComponentGeometry hP C).defect =
      D k * ((actualComponentGeometry hP C).x +
        (actualComponentGeometry hP C).mu - 2) +
      (k - 2) * (actualComponentGeometry hP C).Delta -
        (actualComponentGeometry hP C).r :=
  Geometry.defect_geometry
    (actualComponentGeometry_weightEquations hP hk C)
    (actualComponentGeometry_defectEquations hP C)

/-- 实际分量的旋转类数满足正文公式 (18)。 -/
theorem actual_component_t_normal_form
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) :
    (actualComponentGeometry hP C).t =
      D k * (actualComponentGeometry hP C).m -
        (k - 1) * (actualComponentGeometry hP C).defect :=
  Geometry.t_normal_form
    (actualComponentGeometry_weightEquations hP hk C)
    (actualComponentGeometry_defectEquations hP C)

/-- 实际非满分量的组件入口最小权至少为二。 -/
theorem actual_component_minto_ge_two
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hnonspanning : C.1 ≠ Finset.univ) :
    2 ≤ compMinto (F P) C.1 := by
  rw [← actualComponentPath_minto hP C]
  apply stronglyExitless_minto_ge_two hk
    (actualComponentPath_stronglyExitless hP hk C)
  rwa [actualComponentPath_vertsFinset hP C]

/-- 无需外置证书的真实刚性终端门户定理。 -/
theorem actual_terminal_portal_positive
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hsEnd : actualChainRouteEnd s ≠ P.last)
    (hportal : ActualTerminalPortal hP
      (actualChainSourceComponent hP (by omega) s))
    (hmu : compMinto (F P)
      (actualNonterminalTargetComponent hP (by omega)
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2) :
    1 ≤ actualChainRouteNatCost hP (by omega) s := by
  apply actual_terminal_full_portal_positive hP (by omega) hred s hsEnd
  · exact actualComponentLastPieceFull_certificate hP hk _ hportal.2
  · exact hmu

end PreimageChain

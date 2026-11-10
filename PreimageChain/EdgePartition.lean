import PreimageChain.ChainGraph

/-!
# 预像链的实际边集分割

本模块把 Hunter 的两个删除边集直接分解为 `D_P` 的入口、内部与出口边。
所有有限集都由实际 Hamilton 路径和实际 `chainGraph` 构造，不使用抽象记账假设。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `D_P` 的每条内部边 `u → v` 对应原路径边 `u → σv`。 -/
noncomputable def chainInternalE1 (P : HPath k) : Finset (Vtx k × Vtx k) :=
  (chainGraph P).image fun e => (e.1, sigma e.2)

/-- 每个非终端链终点给出的实际 `E₁` 出口边。 -/
noncomputable def chainExitE1
    {P : HPath k} (hP : P.IsHamiltonian) : Finset (Vtx k × Vtx k) :=
  Finset.univ.image fun v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} =>
    (v.1, (chainTargetTail hP v).1)

/-- 每个链起点给出的实际 `E₂` 入口边。 -/
noncomputable def chainEntryE2
    {P : HPath k} (hP : P.IsHamiltonian) : Finset (Vtx k × Vtx k) :=
  Finset.univ.image fun v : {v : Vtx k // v ∈ chainStarts P} =>
    ((chainSourceHead hP v).1, sigma v.1)

/-- `D_P` 内部边的像全部属于第一次删除边集。 -/
theorem chainInternalE1_subset_E1 {P : HPath k} :
    chainInternalE1 P ⊆ E1removed P (Sset P) := by
  intro e he
  rw [chainInternalE1, Finset.mem_image] at he
  obtain ⟨d, hd, rfl⟩ := he
  have hdData := mem_chainGraph.mp hd
  rw [E1removed, Finset.mem_filter]
  exact ⟨hdData.2.2, hdData.1⟩

/-- 非终端链出口的像全部属于第一次删除边集。 -/
theorem chainExitE1_subset_E1
    {P : HPath k} (hP : P.IsHamiltonian) :
    chainExitE1 hP ⊆ E1removed P (Sset P) := by
  intro e he
  rw [chainExitE1, Finset.mem_image] at he
  obtain ⟨v, _hv, rfl⟩ := he
  exact chainTargetTail_spec hP v

/-- 链入口的像全部属于第二次删除边集。 -/
theorem chainEntryE2_subset_E2
    {P : HPath k} (hP : P.IsHamiltonian) :
    chainEntryE2 hP ⊆ E2removed P (Sset P) := by
  intro e he
  rw [chainEntryE2, Finset.mem_image] at he
  obtain ⟨v, _hv, rfl⟩ := he
  exact chainSourceHead_spec hP v

/-- 第二次删除边集恰由所有实际链入口组成。 -/
theorem chainEntryE2_eq
    {P : HPath k} (hP : P.IsHamiltonian) :
    chainEntryE2 hP = E2removed P (Sset P) := by
  apply Finset.Subset.antisymm (chainEntryE2_subset_E2 hP)
  intro e heE2
  have heOut : e ∈ out P.edges (heads (F P) \ heads P.edges) := by
    rw [Hunter.ProofsStructure.F_eq]
    rw [← Hunter.clm_e2 (Hunter.sset_sPrecond P)]
    exact heE2
  rw [out, Finset.mem_filter] at heOut
  have hsourceHead : e.1 ∈ heads (F P) \ heads P.edges := heOut.2
  let b : {b : Vtx k // b ∈ heads (F P) \ heads P.edges} := ⟨e.1, hsourceHead⟩
  obtain ⟨v, hv⟩ := chainSourceHead_surjective hP b
  have hentryE2 := chainSourceHead_spec hP v
  have hentryPath : ((chainSourceHead hP v).1, sigma v.1) ∈ P.edges :=
    E2removed_subset P (Sset P) hentryE2
  have hsource : (chainSourceHead hP v).1 = e.1 := by
    exact congrArg Subtype.val hv
  have hePath : e ∈ P.edges := E2removed_subset P (Sset P) heE2
  have hentryOut : ((chainSourceHead hP v).1, sigma v.1) ∈
      outV P.edges ((chainSourceHead hP v).1) := by
    rw [outV, mem_out]
    exact ⟨hentryPath, Finset.mem_singleton_self _⟩
  have heOut' : e ∈ outV P.edges ((chainSourceHead hP v).1) := by
    rw [outV, mem_out]
    exact ⟨hePath, by simpa [hsource]⟩
  have heq : ((chainSourceHead hP v).1, sigma v.1) = e :=
    Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_out_le_one P ((chainSourceHead hP v).1))
      _ hentryOut _ heOut'
  rw [chainEntryE2, Finset.mem_image]
  exact ⟨v, Finset.mem_univ _, heq⟩

/--
第一次删除边集恰是不交并之前的集合等式：每条边要么在 `D_P` 内继续，
要么从一个非终端链终点退出。
-/
theorem E1removed_eq_internal_union_exit
    {P : HPath k} (hP : P.IsHamiltonian) :
    E1removed P (Sset P) = chainInternalE1 P ∪ chainExitE1 hP := by
  apply Finset.Subset.antisymm
  · intro e heE1
    have heData := Finset.mem_filter.mp heE1
    have hePath : e ∈ P.edges := heData.1
    have hsourceS : e.1 ∈ Sset P := heData.2
    by_cases hinter : ∃ v : Vtx k, v ∈ Sset P ∧ e.2 = sigma v
    · obtain ⟨v, hvS, htarget⟩ := hinter
      have hd : (e.1, v) ∈ chainGraph P := by
        apply mem_chainGraph.mpr
        refine ⟨hsourceS, hvS, ?_⟩
        rw [← htarget]
        simpa only [Prod.eta] using hePath
      rw [Finset.mem_union]
      left
      rw [chainInternalE1, Finset.mem_image]
      exact ⟨(e.1, v), hd, Prod.ext rfl htarget.symm⟩
    · have hnotLast : e.1 ≠ P.last :=
        Hunter.ProofsStructure.ne_last_of_out_edge hePath
      have hnoSlot : ∀ v : Vtx k, v ∈ Sset P → e.2 ≠ sigma v := by
        intro v hvS heq
        exact hinter ⟨v, hvS, heq⟩
      have hend : e.1 ∈ chainEnds P := by
        apply (chainEnd_iff_terminal_or_unique_exit hP).mpr
        refine ⟨hsourceS, Or.inr ⟨e.2, ⟨hePath, hnoSlot⟩, ?_⟩⟩
        intro a ha
        have hedgeEq : (e.1, a) = e :=
          Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P e.1)
            (e.1, a) (by rw [outV, mem_out]; exact ⟨ha.1, by simp⟩)
            e (by rw [outV, mem_out]; exact ⟨hePath, by simp⟩)
        exact congrArg Prod.snd hedgeEq
      let v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
        ⟨e.1, hend, hnotLast⟩
      have hexit := chainTargetTail_spec hP v
      have hexitPath : (e.1, (chainTargetTail hP v).1) ∈ P.edges :=
        E1removed_subset P (Sset P) hexit
      have heq : (e.1, (chainTargetTail hP v).1) = e :=
        Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P e.1)
          _ (by rw [outV, mem_out]; exact ⟨hexitPath, by simp⟩)
          _ (by rw [outV, mem_out]; exact ⟨hePath, by simp⟩)
      rw [Finset.mem_union]
      right
      rw [chainExitE1, Finset.mem_image]
      exact ⟨v, Finset.mem_univ _, heq⟩
  · intro e he
    rw [Finset.mem_union] at he
    rcases he with hinter | hexit
    · exact chainInternalE1_subset_E1 hinter
    · exact chainExitE1_subset_E1 hP hexit

/-- 内部边与非终端出口边互不相交。 -/
theorem chainInternalE1_disjoint_exit
    {P : HPath k} (hP : P.IsHamiltonian) :
    Disjoint (chainInternalE1 P) (chainExitE1 hP) := by
  rw [Finset.disjoint_left]
  intro e hinter hexit
  rw [chainInternalE1, Finset.mem_image] at hinter
  obtain ⟨d, hd, hde⟩ := hinter
  rw [chainExitE1, Finset.mem_image] at hexit
  obtain ⟨v, _hv, hve⟩ := hexit
  have hsource : d.1 = v.1 := by
    have := congrArg Prod.fst (hde.trans hve.symm)
    simpa using this
  have hdOut : d ∈ outV (chainGraph P) v.1 := by
    rw [outV, mem_out]
    exact ⟨hd, by simpa [hsource]⟩
  have hvEmpty : outV (chainGraph P) v.1 = ∅ := (mem_chainEnds.mp v.2.1).2
  rw [hvEmpty] at hdOut
  exact Finset.notMem_empty _ hdOut

/-- `E₁` 上任意整数权函数的和精确分成内部项与出口项。 -/
theorem sum_E1removed_partition
    {P : HPath k} (hP : P.IsHamiltonian)
    (f : Vtx k × Vtx k → ℤ) :
    (∑ e ∈ E1removed P (Sset P), f e) =
      (∑ e ∈ chainInternalE1 P, f e) + ∑ e ∈ chainExitE1 hP, f e := by
  rw [E1removed_eq_internal_union_exit hP,
    Finset.sum_union (chainInternalE1_disjoint_exit hP)]

/-- `D_P` 内部边到原路径边的映射是单射。 -/
theorem chainInternalEdge_injective :
    Function.Injective (fun e : Vtx k × Vtx k => (e.1, sigma e.2)) := by
  intro a b hab
  apply Prod.ext
  · simpa using congrArg (fun e : Vtx k × Vtx k => e.1) hab
  · have hsigma : sigma a.2 = sigma b.2 := by
      simpa using congrArg (fun e : Vtx k × Vtx k => e.2) hab
    exact Hunter.ProofsSpine.sigma_inj hsigma

/-- 链入口映射是单射；入口靶点已经唯一确定槽位。 -/
theorem chainEntryEdge_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective
      (fun v : {v : Vtx k // v ∈ chainStarts P} =>
        ((chainSourceHead hP v).1, sigma v.1)) := by
  intro v w hvw
  apply Subtype.ext
  exact Hunter.ProofsSpine.sigma_inj (congrArg Prod.snd hvw)

/-- 链出口映射是单射；出口边的第一坐标就是链终点。 -/
theorem chainExitEdge_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective
      (fun v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} =>
        (v.1, (chainTargetTail hP v).1)) := by
  intro v w hvw
  apply Subtype.ext
  exact congrArg Prod.fst hvw

/-- `E₂` 的边数就是实际链起点数。 -/
theorem card_E2removed_eq_chainStarts
    {P : HPath k} (hP : P.IsHamiltonian) :
    (E2removed P (Sset P)).card = (chainStarts P).card := by
  rw [← chainEntryE2_eq hP, chainEntryE2,
    Finset.card_image_of_injective _ (chainEntryEdge_injective hP),
    Finset.card_univ, Fintype.card_coe]

/-- `E₂` 权重和在实际链入口上精确重索引。 -/
theorem sum_E2removed_reindex
    {P : HPath k} (hP : P.IsHamiltonian)
    (f : Vtx k × Vtx k → ℤ) :
    (∑ e ∈ E2removed P (Sset P), f e) =
      ∑ v : {v : Vtx k // v ∈ chainStarts P},
        f ((chainSourceHead hP v).1, sigma v.1) := by
  rw [← chainEntryE2_eq hP, chainEntryE2,
    Finset.sum_image (fun a _ b _ hab => chainEntryEdge_injective hP hab)]

/-- `E₁` 权重和在 `D_P` 内部边与实际非终端出口上精确重索引。 -/
theorem sum_E1removed_reindex
    {P : HPath k} (hP : P.IsHamiltonian)
    (f : Vtx k × Vtx k → ℤ) :
    (∑ e ∈ E1removed P (Sset P), f e) =
      (∑ d ∈ chainGraph P, f (d.1, sigma d.2)) +
        ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
          f (v.1, (chainTargetTail hP v).1) := by
  rw [sum_E1removed_partition hP f, chainInternalE1, chainExitE1,
    Finset.sum_image (fun a _ b _ hab => chainInternalEdge_injective hab),
    Finset.sum_image (fun a _ b _ hab => chainExitEdge_injective hP hab)]

/--
Hunter 精确权重式在实际预像链三类边上的展开。这里已经不再保留抽象的
`E₁/E₂` 求和：内部项直接在 `chainGraph P` 上求和，边界项直接在链起点与
非终端链终点上求和。
-/
theorem actual_preimage_edge_bookkeeping
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 1 ≤ k) :
    (P.wtP : ℤ) = (wEdges (F P) : ℤ)
      + ((∑ d ∈ chainGraph P, ((ew k d.1 (sigma d.2) : ℤ) - 1))
        + ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
          ((ew k v.1 (chainTargetTail hP v).1 : ℤ) - 1))
      - (indicatorI P (Sset P) : ℤ)
      + ∑ v : {v : Vtx k // v ∈ chainStarts P},
          (ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ) := by
  have hSV : Sset P ⊆ P.vertsFinset := by
    intro v _hv
    exact HPath.mem_vertsFinset.mpr (hP v)
  have hbook := Hunter.clm_eqq hk hSV (Hunter.sset_sPrecond P)
  rw [← Hunter.ProofsStructure.F_eq] at hbook
  rw [sum_E1removed_reindex hP
      (fun e => ((ew k e.1 e.2 : ℤ) - 1)),
    sum_E2removed_reindex hP
      (fun e => (ew k e.1 e.2 : ℤ))] at hbook
  exact hbook

/-- 每条 `D_P` 内部边的超额 `w(u,σv)-1` 非负。 -/
theorem chainInternal_excess_nonneg
    (hk : 1 ≤ k) {P : HPath k} {d : Vtx k × Vtx k}
    (_hd : d ∈ chainGraph P) :
    0 ≤ (ew k d.1 (sigma d.2) : ℤ) - 1 := by
  have hpos : 1 ≤ ew k d.1 (sigma d.2) := by
    rw [ew]
    exact (wt_spec hk (le_of_eq d.1.2.length)).1
  exact sub_nonneg.mpr (by exact_mod_cast hpos)

/-- 每条实际链入口边的超额 `w(h,σv)-2` 非负。 -/
theorem chainEntry_excess_nonneg
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (v : {v : Vtx k // v ∈ chainStarts P}) :
    0 ≤ (ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ) - 2 := by
  let b := (chainSourceHead hP v).1
  have hbNotS : b ∉ Sset P := by
    intro hbS
    have hnonempty : (outV (F P) b).Nonempty := by
      have hnonempty' := Hunter.ProofsSpine.outV_fPS_ne_empty_of_mem_S
        P (Sset P) (Hunter.sset_sPrecond P) hbS
      simpa only [Hunter.ProofsStructure.F_eq] using hnonempty'
    have hbHeadMem := (Finset.mem_sdiff.mp (chainSourceHead hP v).2).1
    have hbEmpty : outV (F P) b = ∅ :=
      (Finset.mem_filter.mp hbHeadMem).2
    rw [hbEmpty] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hpos : 1 ≤ ew k b (sigma v.1) := by
    rw [ew]
    exact (wt_spec (by omega) (le_of_eq b.2.length)).1
  have hneOne : ew k b (sigma v.1) ≠ 1 := by
    intro hone
    have hsigma : sigma v.1 = sigma b :=
      (Hunter.ProofsExitless.ew_eq_one_iff (by omega)).mp hone
    have hvb : v.1 = b := Hunter.ProofsSpine.sigma_inj hsigma
    exact hbNotS (hvb ▸ (mem_chainStarts.mp v.2).1)
  have htwo : 2 ≤ ew k b (sigma v.1) := by omega
  exact sub_nonneg.mpr (by exact_mod_cast htwo)

/-- 每条非终端出口边的权重至少为目标分量的最小入口权。 -/
theorem chainExit_excess_nonneg
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    0 ≤ (ew k v.1 (chainTargetTail hP v).1 : ℤ) -
      (compMinto (F P)
        (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ) := by
  have heE1 := chainTargetTail_spec hP v
  have hePath : (v.1, (chainTargetTail hP v).1) ∈ P.edges :=
    E1removed_subset P (Sset P) heE1
  have htail : (chainTargetTail hP v).1 ∈ tails (F P) :=
    (Finset.mem_sdiff.mp (chainTargetTail hP v).2).1
  have hle := Hunter.ProofsWP.compMinto_le_ew hP hk
    (Hunter.lem_pathrule hP) hePath htail
  exact sub_nonneg.mpr (by exact_mod_cast hle)

/--
由实际 `D_P` 定义的总剩余成本：入口超额、全部内部边超额（路径与环）以及
非终端出口超额之和。
-/
noncomputable def actualPreimageSurplus
    {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  (∑ v : {v : Vtx k // v ∈ chainStarts P},
      ((ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ) - 2))
  + (∑ d ∈ chainGraph P, ((ew k d.1 (sigma d.2) : ℤ) - 1))
  + ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
      ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
        (compMinto (F P)
          (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ))

/-- 实际预像链总剩余成本非负。 -/
theorem actualPreimageSurplus_nonneg
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    0 ≤ actualPreimageSurplus hP := by
  unfold actualPreimageSurplus
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg fun v _ => chainEntry_excess_nonneg hP hk v
    · exact Finset.sum_nonneg fun d hd => chainInternal_excess_nonneg (by omega) hd
  · exact Finset.sum_nonneg fun v _ => chainExit_excess_nonneg hP hk v

/-- 入口权重和等于每条入口的基线二加入口超额。 -/
theorem sum_chainEntries_eq_baseline_surplus
    {P : HPath k} (hP : P.IsHamiltonian) :
    (∑ v : {v : Vtx k // v ∈ chainStarts P},
        (ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ)) =
      2 * (Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℤ)
      + ∑ v : {v : Vtx k // v ∈ chainStarts P},
          ((ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ) - 2) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  ring

/-- 出口的 `w-1` 精确分成组件入口基线 `μ-1` 与出口超额 `w-μ`。 -/
theorem sum_chainExits_eq_baseline_surplus
    {P : HPath k} (hP : P.IsHamiltonian) :
    (∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) - 1)) =
      (∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((compMinto (F P)
          (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ) - 1))
      + ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
          (compMinto (F P)
            (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  ring

/-- 非根目标组件在实际链出口上贡献的基线和。 -/
noncomputable def actualExitBaseline
    {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
    ((compMinto (F P)
      (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ) - 1)

/--
从真实 Hunter 权重记账抽取入口基线二与非根出口基线后的精确等式。
下一步只需用靶端双射把 `actualExitBaseline` 改写为非根组件的 `μ-1` 求和，
再与 `MinThrough` 的最大项相消，即得到论文公式 (10) 的完整组件形式。
-/
theorem actual_preimage_surplus_identity
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 1 ≤ k) :
    (P.wtP : ℤ) = (wEdges (F P) : ℤ)
      + 2 * (Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℤ)
      + actualExitBaseline hP
      - (indicatorI P (Sset P) : ℤ)
      + actualPreimageSurplus hP := by
  rw [actual_preimage_edge_bookkeeping hP hk,
    sum_chainEntries_eq_baseline_surplus hP,
    sum_chainExits_eq_baseline_surplus hP]
  unfold actualExitBaseline actualPreimageSurplus
  ring

end PreimageChain

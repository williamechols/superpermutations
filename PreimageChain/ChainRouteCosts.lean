import PreimageChain.ChainRoutes
import PreimageChain.EdgePartition

/-!
# 实际预像链路线的成本

本模块把每条已线性化路线的内部边收集为有限集，证明不同路线的边集互不
相交，并把路线级入口/内部成本嵌入真实总剩余成本。未被路线使用的 `D_P`
边恰是可能的有向环部分；由于每条内部边超额非负，删除这些环只会降低成本。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 一条实际链路线中的相邻 `D_P` 边。 -/
noncomputable def actualChainRouteEdges
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    Finset (Vtx k × Vtx k) :=
  ((actualChainRoute s).zip (actualChainRoute s).tail).toFinset

theorem actualChainRouteEdges_subset
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainRouteEdges s ⊆ chainGraph P := by
  intro d hd
  rw [actualChainRouteEdges, List.mem_toFinset] at hd
  exact Hunter.ProofsPathrule.chain_rel_of_zip
    (actualChainRoute_isChain s) hd

/-- 不同实际链路线的边集互不相交。 -/
theorem actualChainRouteEdges_disjoint
    {P : HPath k} {s t : {v : Vtx k // v ∈ chainStarts P}} (hst : s ≠ t) :
    Disjoint (actualChainRouteEdges s) (actualChainRouteEdges t) := by
  rw [Finset.disjoint_left]
  intro d hds hdt
  have hds' : d ∈ (actualChainRoute s).zip (actualChainRoute s).tail := by
    simpa [actualChainRouteEdges] using hds
  have hdt' : d ∈ (actualChainRoute t).zip (actualChainRoute t).tail := by
    simpa [actualChainRouteEdges] using hdt
  have hsSource : d.1 ∈ (actualChainRoute s).toFinset :=
    List.mem_toFinset.mpr (List.of_mem_zip hds').1
  have htSource : d.1 ∈ (actualChainRoute t).toFinset :=
    List.mem_toFinset.mpr (List.of_mem_zip hdt').1
  exact Finset.disjoint_left.mp (actualChainRoutes_disjoint hst)
    hsSource htSource

/-- 所有从链起点出发的路径边之并；`D_P` 中未包含的边只属于环部分。 -/
noncomputable def actualChainPathEdges (P : HPath k) :
    Finset (Vtx k × Vtx k) :=
  Finset.univ.biUnion fun s : {v : Vtx k // v ∈ chainStarts P} =>
    actualChainRouteEdges s

theorem actualChainRouteEdges_pairwiseDisjoint (P : HPath k) :
    Set.PairwiseDisjoint
      (Set.univ : Set {v : Vtx k // v ∈ chainStarts P})
      (fun s => actualChainRouteEdges s) := by
  intro s _hs t _ht hst
  exact actualChainRouteEdges_disjoint hst

theorem actualChainPathEdges_subset (P : HPath k) :
    actualChainPathEdges P ⊆ chainGraph P := by
  intro d hd
  rw [actualChainPathEdges, Finset.mem_biUnion] at hd
  obtain ⟨s, _hs, hds⟩ := hd
  exact actualChainRouteEdges_subset s hds

/-- 路径部分全部内部边的总超额；环边没有计入。 -/
noncomputable def actualChainPathInternalSurplus (P : HPath k) : ℤ :=
  ∑ d ∈ actualChainPathEdges P, ((ew k d.1 (sigma d.2) : ℤ) - 1)

/-- 路径内部超额可无重复地按实际链起点重索引。 -/
theorem actualChainPathInternalSurplus_eq_route_sum (P : HPath k) :
    actualChainPathInternalSurplus P =
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        ∑ d ∈ actualChainRouteEdges s,
          ((ew k d.1 (sigma d.2) : ℤ) - 1) := by
  unfold actualChainPathInternalSurplus actualChainPathEdges
  rw [Finset.sum_biUnion (by
    intro s _hs t _ht hst
    exact actualChainRouteEdges_disjoint hst)]

/-- 删除非负的环边成本后，路径内部成本不超过 `D_P` 的全部内部成本。 -/
theorem actualChainPathInternalSurplus_le_all
    (hk : 1 ≤ k) (P : HPath k) :
    actualChainPathInternalSurplus P ≤
      ∑ d ∈ chainGraph P, ((ew k d.1 (sigma d.2) : ℤ) - 1) := by
  unfold actualChainPathInternalSurplus
  apply Finset.sum_le_sum_of_subset_of_nonneg (actualChainPathEdges_subset P)
  intro d hdGraph _hdPath
  exact chainInternal_excess_nonneg hk hdGraph

/-- 一条实际链的入口超额加路线内部超额（尚未加入非终端出口项）。 -/
noncomputable def actualChainRouteCoreCost
    {P : HPath k} (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ℤ :=
  ((ew k (chainSourceHead hP s).1 (sigma s.1) : ℤ) - 2) +
    ∑ d ∈ actualChainRouteEdges s,
      ((ew k d.1 (sigma d.2) : ℤ) - 1)

/-- 所有实际链的入口与路径内部成本和。 -/
noncomputable def actualChainCoreSurplus
    {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  ∑ s : {v : Vtx k // v ∈ chainStarts P},
    actualChainRouteCoreCost hP s

theorem actualChainCoreSurplus_eq
    {P : HPath k} (hP : P.IsHamiltonian) :
    actualChainCoreSurplus hP =
      (∑ s : {v : Vtx k // v ∈ chainStarts P},
        ((ew k (chainSourceHead hP s).1 (sigma s.1) : ℤ) - 2)) +
      actualChainPathInternalSurplus P := by
  unfold actualChainCoreSurplus actualChainRouteCoreCost
  rw [Finset.sum_add_distrib, actualChainPathInternalSurplus_eq_route_sum]

/--
真实总剩余成本支配所有实际链的入口与路径内部成本。差额由非负环成本和
非负出口成本组成。
-/
theorem actualChainCoreSurplus_le_actualPreimageSurplus
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualChainCoreSurplus hP ≤ actualPreimageSurplus hP := by
  rw [actualChainCoreSurplus_eq]
  unfold actualPreimageSurplus
  have hInternal := actualChainPathInternalSurplus_le_all (by omega) P
  have hExit : 0 ≤
      ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
          (compMinto (F P)
            (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ)) :=
    Finset.sum_nonneg fun v _ => chainExit_excess_nonneg hP hk v
  omega

/-! ## 加入链出口后的实际指派成本 -/

/-- 一个链终点的出口成本；Hamilton 路径最终顶点对应论文中的 `⋆`，成本为零。 -/
noncomputable def actualChainEndExitCost
    {P : HPath k} (hP : P.IsHamiltonian)
    (e : {v : Vtx k // v ∈ chainEnds P}) : ℤ :=
  if hlast : e.1 = P.last then 0 else
    (ew k e.1 (chainTargetTail hP ⟨e.1, e.2, hlast⟩).1 : ℤ) -
      (compMinto (F P)
        (Hunter.ProofsWP.block (F P)
          (chainTargetTail hP ⟨e.1, e.2, hlast⟩).1) : ℤ)

/-- 在全部链终点上求和时，`P.last` 的零成本项可删去。 -/
theorem sum_actualChainEndExitCost
    {P : HPath k} (hP : P.IsHamiltonian) :
    (∑ e : {v : Vtx k // v ∈ chainEnds P},
      actualChainEndExitCost hP e) =
      ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
          (compMinto (F P)
            (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ)) := by
  classical
  let p : {v : Vtx k // v ∈ chainEnds P} → Prop := fun e => e.1 ≠ P.last
  have hfilter :
      (∑ e ∈ (Finset.univ.filter p), actualChainEndExitCost hP e) =
        ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
          ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
            (compMinto (F P)
              (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ)) := by
    apply Finset.sum_bij
      (fun e he =>
        (⟨e.1, e.2, (Finset.mem_filter.mp he).2⟩ :
          {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}))
    · intro e he
      exact Finset.mem_univ _
    · intro a ha b hb hab
      apply Subtype.ext
      exact congrArg
        (fun x : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} => x.1) hab
    · intro b _hb
      let e : {v : Vtx k // v ∈ chainEnds P} := ⟨b.1, b.2.1⟩
      have he : e ∈ Finset.univ.filter p := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, b.2.2⟩
      exact ⟨e, he, by apply Subtype.ext; rfl⟩
    · intro e he
      have hne : e.1 ≠ P.last := (Finset.mem_filter.mp he).2
      simp [actualChainEndExitCost, hne]
  calc
    (∑ e : {v : Vtx k // v ∈ chainEnds P}, actualChainEndExitCost hP e) =
        ∑ e ∈ (Finset.univ.filter p), actualChainEndExitCost hP e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hlast : e.1 = P.last
      · simp [actualChainEndExitCost, hlast]
      · simp [actualChainEndExitCost, hlast]
    _ = _ := hfilter

/-- 一条真实链的完整成本：入口超额、路线内部超额及目标出口超额。 -/
noncomputable def actualChainRouteCost
    {P : HPath k} (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ℤ :=
  actualChainRouteCoreCost hP s +
    actualChainEndExitCost hP (chainStartEnd s)

/-- 真实链族给出的完整可行指派成本。 -/
noncomputable def actualChainAssignmentSurplus
    {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  ∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteCost hP s

/--
真实 `D_P` 路径族给出的完整指派成本不超过真实总剩余成本；唯一被删除的
仍是非负有向环内部成本。
-/
theorem actualChainAssignmentSurplus_le_actualPreimageSurplus
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualChainAssignmentSurplus hP ≤ actualPreimageSurplus hP := by
  unfold actualChainAssignmentSurplus actualChainRouteCost
  rw [Finset.sum_add_distrib]
  have hEndReindex :=
    (chainStartEndEquiv (by omega) P).sum_comp (actualChainEndExitCost hP)
  change (∑ s : {v : Vtx k // v ∈ chainStarts P},
      actualChainEndExitCost hP (chainStartEnd s)) =
    ∑ e : {v : Vtx k // v ∈ chainEnds P},
      actualChainEndExitCost hP e at hEndReindex
  rw [hEndReindex, sum_actualChainEndExitCost]
  change actualChainCoreSurplus hP +
      (∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) -
          (compMinto (F P)
            (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ))) ≤
    actualPreimageSurplus hP
  rw [actualChainCoreSurplus_eq]
  unfold actualPreimageSurplus
  have hInternal := actualChainPathInternalSurplus_le_all (by omega) P
  omega

end PreimageChain

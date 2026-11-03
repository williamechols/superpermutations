import PreimageChain.ChainRouteCosts
import PreimageChain.ComponentIdentity

/-!
# 实际预像链的组件级匹配

本模块为 `F(P)` 的每个实际路径组件选择其唯一头、尾，并把 `D_P` 的链源和
链靶提升到组件层。它是正文两种指派情形（无终端链/有唯一终端链）以及后续
最短路矩阵的共同索引接口。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `F(P)` 的实际 Hunter 组件类型。 -/
noncomputable abbrev ActualComponent (P : HPath k) := ↑(Comps (F P))

/-- 一个实际组件的唯一有向头。 -/
noncomputable def actualComponentHead
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Vtx k :=
  Classical.choose
    (Hunter.ProofsWP.compHeads_F_single (Hunter.lem_pathrule hP) C.2)

theorem actualComponentHead_spec
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    Hunter.ProofsWP.compHeads (F P) C.1 = {actualComponentHead hP C} :=
  Classical.choose_spec
    (Hunter.ProofsWP.compHeads_F_single (Hunter.lem_pathrule hP) C.2)

theorem actualComponentHead_mem_component
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualComponentHead hP C ∈ C.1 := by
  apply Hunter.ProofsWP.compHeads_subset
  rw [actualComponentHead_spec hP C, Finset.mem_singleton]

theorem actualComponentHead_mem_heads
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualComponentHead hP C ∈ heads (F P) := by
  rw [heads, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hm : actualComponentHead hP C ∈
      Hunter.ProofsWP.compHeads (F P) C.1 := by
    rw [actualComponentHead_spec hP C, Finset.mem_singleton]
  exact (Finset.mem_filter.mp hm).2

/-- 一个实际组件的唯一有向尾。 -/
noncomputable def actualComponentTail
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Vtx k :=
  Classical.choose
    (Hunter.ProofsWP.compTails_F_single (Hunter.lem_pathrule hP) C.2)

theorem actualComponentTail_spec
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    compTails (F P) C.1 = {actualComponentTail hP C} :=
  Classical.choose_spec
    (Hunter.ProofsWP.compTails_F_single (Hunter.lem_pathrule hP) C.2)

theorem actualComponentTail_mem_component
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualComponentTail hP C ∈ C.1 := by
  apply Hunter.ProofsWP.compTails_subset
  rw [actualComponentTail_spec hP C, Finset.mem_singleton]

theorem actualComponentTail_mem_tails
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualComponentTail hP C ∈ tails (F P) := by
  rw [tails, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hm : actualComponentTail hP C ∈ compTails (F P) C.1 := by
    rw [actualComponentTail_spec hP C, Finset.mem_singleton]
  exact (Finset.mem_filter.mp hm).2

theorem actualComponentHead_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective (actualComponentHead hP) := by
  intro C D hCD
  apply Subtype.ext
  have hC := actualComponentHead_mem_component hP C
  have hD := actualComponentHead_mem_component hP D
  exact (Hunter.ProofsWP.comp_eq_block_of_mem C.2 hC).trans
    ((Hunter.ProofsWP.comp_eq_block_of_mem D.2 (hCD ▸ hD)).symm)

theorem actualComponentTail_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective (actualComponentTail hP) := by
  intro C D hCD
  apply Subtype.ext
  have hC := actualComponentTail_mem_component hP C
  have hD := actualComponentTail_mem_component hP D
  exact (Hunter.ProofsWP.comp_eq_block_of_mem C.2 hC).trans
    ((Hunter.ProofsWP.comp_eq_block_of_mem D.2 (hCD ▸ hD)).symm)

/-- 组件到其唯一头（作为全局 `heads` 元素）的映射。 -/
noncomputable def actualComponentHeadAsHead
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    {v : Vtx k // v ∈ heads (F P)} :=
  ⟨actualComponentHead hP C, actualComponentHead_mem_heads hP C⟩

theorem actualComponentHeadAsHead_bijective
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Bijective (actualComponentHeadAsHead hP) := by
  constructor
  · intro C D hCD
    apply actualComponentHead_injective hP
    exact congrArg Subtype.val hCD
  · intro h
    have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
    have hhV : h.1 ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
    let C : ActualComponent P :=
      ⟨Hunter.ProofsWP.block (F P) h.1,
        Hunter.ProofsWP.block_mem_comps hhV⟩
    have hhComp : h.1 ∈ Hunter.ProofsWP.compHeads (F P) C.1 := by
      rw [Hunter.ProofsWP.compHeads, Finset.mem_filter]
      refine ⟨Hunter.ProofsWP.self_mem_block hhV, ?_⟩
      exact (Finset.mem_filter.mp h.2).2
    have hhEq : h.1 = actualComponentHead hP C := by
      rw [actualComponentHead_spec hP C, Finset.mem_singleton] at hhComp
      exact hhComp
    refine ⟨C, ?_⟩
    apply Subtype.ext
    exact hhEq.symm

/-- 实际组件与实际组件头之间的有限双射。 -/
noncomputable def actualComponentHeadEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ActualComponent P ≃ {v : Vtx k // v ∈ heads (F P)} :=
  Equiv.ofBijective (actualComponentHeadAsHead hP)
    (actualComponentHeadAsHead_bijective hP hk)

/-- 组件到其唯一尾（作为全局 `tails` 元素）的映射。 -/
noncomputable def actualComponentTailAsTail
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    {v : Vtx k // v ∈ tails (F P)} :=
  ⟨actualComponentTail hP C, actualComponentTail_mem_tails hP C⟩

theorem actualComponentTailAsTail_bijective
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Bijective (actualComponentTailAsTail hP) := by
  constructor
  · intro C D hCD
    apply actualComponentTail_injective hP
    exact congrArg Subtype.val hCD
  · intro t
    have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
    have htV : t.1 ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
    let C : ActualComponent P :=
      ⟨Hunter.ProofsWP.block (F P) t.1,
        Hunter.ProofsWP.block_mem_comps htV⟩
    have htComp : t.1 ∈ compTails (F P) C.1 := by
      rw [compTails, Finset.mem_filter]
      refine ⟨Hunter.ProofsWP.self_mem_block htV, ?_⟩
      exact (Finset.mem_filter.mp t.2).2
    have htEq : t.1 = actualComponentTail hP C := by
      rw [actualComponentTail_spec hP C, Finset.mem_singleton] at htComp
      exact htComp
    refine ⟨C, ?_⟩
    apply Subtype.ext
    exact htEq.symm

/-- 实际组件与实际组件尾之间的有限双射。 -/
noncomputable def actualComponentTailEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ActualComponent P ≃ {v : Vtx k // v ∈ tails (F P)} :=
  Equiv.ofBijective (actualComponentTailAsTail hP)
    (actualComponentTailAsTail_bijective hP hk)

/-- 包含 Hamilton 路径首点的实际根组件。 -/
noncomputable def actualRootComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ActualComponent P := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  exact ⟨Hunter.ProofsWP.block (F P) P.first,
    Hunter.ProofsWP.block_mem_comps (hV ▸ Finset.mem_univ _)⟩

/-- 包含 Hamilton 路径末点的实际末组件。 -/
noncomputable def actualLastComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ActualComponent P := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  exact ⟨Hunter.ProofsWP.block (F P) P.last,
    Hunter.ProofsWP.block_mem_comps (hV ▸ Finset.mem_univ _)⟩

/-- Hamilton 路径末点是旋转槽，当且仅当它不是 `F(P)` 的组件头。 -/
theorem last_mem_Sset_iff_not_mem_heads
    {P : HPath k} (hP : P.IsHamiltonian) :
    P.last ∈ Sset P ↔ P.last ∉ heads (F P) := by
  have hSiff : P.last ∈ Sset P ↔ P.last ∉ Cm1 P := by
    rw [Sset, Finset.mem_filter]
    exact ⟨fun h => h.2.1,
      fun h => ⟨Finset.mem_univ _, h, Hunter.ProofsWP.last_notMem_out_edge⟩⟩
  rw [hSiff, Hunter.ProofsWP.last_mem_heads_F_iff hP]

/-- Hamilton 路径末点属于 `D_P` 终点，当且仅当它是旋转槽。 -/
theorem last_mem_chainEnds_iff
    {P : HPath k} (hP : P.IsHamiltonian) :
    P.last ∈ chainEnds P ↔ P.last ∈ Sset P := by
  constructor
  · intro h
    exact (mem_chainEnds.mp h).1
  · intro h
    apply (chainEnd_iff_terminal_or_unique_exit hP).mpr
    exact ⟨h, Or.inl rfl⟩

/-- 一条实际链的源组件。 -/
noncomputable def actualChainSourceComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ActualComponent P :=
  (actualComponentHeadEquiv hP hk).symm
    ⟨(chainSourceHead hP s).1,
      (Finset.mem_sdiff.mp (chainSourceHead hP s).2).1⟩

theorem actualChainSourceComponent_head
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualComponentHead hP (actualChainSourceComponent hP hk s) =
      (chainSourceHead hP s).1 := by
  have h := (actualComponentHeadEquiv hP hk).apply_symm_apply
    ⟨(chainSourceHead hP s).1,
      (Finset.mem_sdiff.mp (chainSourceHead hP s).2).1⟩
  exact congrArg Subtype.val h

theorem actualChainSourceComponent_injective
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Injective (actualChainSourceComponent hP hk) := by
  intro s t hst
  apply chainSourceHead_injective hP
  apply Subtype.ext
  calc
    (chainSourceHead hP s).1 =
        actualComponentHead hP (actualChainSourceComponent hP hk s) :=
      (actualChainSourceComponent_head hP hk s).symm
    _ = actualComponentHead hP (actualChainSourceComponent hP hk t) := by rw [hst]
    _ = (chainSourceHead hP t).1 := actualChainSourceComponent_head hP hk t

/-! ## 根、末组件与两种实际匹配 -/

theorem actualComponentHead_last
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    actualComponentHead hP (actualLastComponent hP hk) = P.last := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hlastV : P.last ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have hm : P.last ∈ Hunter.ProofsWP.compHeads (F P)
      (actualLastComponent hP hk).1 := by
    rw [Hunter.ProofsWP.compHeads, Finset.mem_filter]
    refine ⟨Hunter.ProofsWP.self_mem_block hlastV, ?_⟩
    exact (Finset.mem_filter.mp hlast).2
  rw [actualComponentHead_spec hP, Finset.mem_singleton] at hm
  exact hm.symm

theorem actualComponentTail_root
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualComponentTail hP (actualRootComponent hP hk) = P.first := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hfirstV : P.first ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have hfirstTail : P.first ∈ tails (F P) :=
    Hunter.ProofsWP.first_mem_tails hP hk (Hunter.lem_pathrule hP)
  have hm : P.first ∈ compTails (F P)
      (actualRootComponent hP hk).1 := by
    rw [compTails, Finset.mem_filter]
    refine ⟨Hunter.ProofsWP.self_mem_block hfirstV, ?_⟩
    exact (Finset.mem_filter.mp hfirstTail).2
  rw [actualComponentTail_spec hP, Finset.mem_singleton] at hm
  exact hm.symm

/-- 非根组件的有限集表示与“组件不等于根”的表示之间的双射。 -/
noncomputable def nonRootComponentNeEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    NonRootComponent P ≃
      {C : ActualComponent P // C ≠ actualRootComponent hP hk} where
  toFun C := by
    have hmem := Finset.mem_sdiff.mp C.2
    refine ⟨⟨C.1, hmem.1⟩, ?_⟩
    intro hEq
    apply hmem.2
    rw [Finset.mem_singleton]
    exact congrArg Subtype.val hEq
  invFun C := by
    refine ⟨C.1.1, Finset.mem_sdiff.mpr ⟨C.1.2, ?_⟩⟩
    rw [Finset.mem_singleton]
    intro hEq
    apply C.2
    apply Subtype.ext
    exact hEq
  left_inv C := by apply Subtype.ext; rfl
  right_inv C := by apply Subtype.ext; rfl

/-- 无终端链情形下，一条链的源组件不是末组件。 -/
theorem actualChainSourceComponent_ne_last
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainSourceComponent hP hk s ≠ actualLastComponent hP hk := by
  intro hEq
  have hhead : (chainSourceHead hP s).1 = P.last := by
    calc
      (chainSourceHead hP s).1 =
          actualComponentHead hP (actualChainSourceComponent hP hk s) :=
        (actualChainSourceComponent_head hP hk s).symm
      _ = actualComponentHead hP (actualLastComponent hP hk) := by rw [hEq]
      _ = P.last := actualComponentHead_last hP hk hlast
  have hnot := (Finset.mem_sdiff.mp (chainSourceHead hP s).2).2
  apply hnot
  have hlastPathHead : P.last ∈ heads P.edges := by
    rw [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]
  exact hhead.symm ▸ hlastPathHead

/-- 无终端链情形的源端双射：链 ↔ 除末组件外的组件。 -/
noncomputable def actualChainSourceNonLastEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    {v : Vtx k // v ∈ chainStarts P} ≃
      {C : ActualComponent P // C ≠ actualLastComponent hP hk} := by
  let f := fun s : {v : Vtx k // v ∈ chainStarts P} =>
    (⟨actualChainSourceComponent hP hk s,
      actualChainSourceComponent_ne_last hP hk hlast s⟩ :
      {C : ActualComponent P // C ≠ actualLastComponent hP hk})
  apply Equiv.ofBijective f
  constructor
  · intro s t hst
    apply actualChainSourceComponent_injective hP hk
    exact congrArg Subtype.val hst
  · intro C
    let hC : {v : Vtx k // v ∈ heads (F P)} :=
      actualComponentHeadAsHead hP C.1
    have hCne : hC.1 ≠ P.last := by
      intro heq
      apply C.2
      apply actualComponentHead_injective hP
      calc
        actualComponentHead hP C.1 = P.last := heq
        _ = actualComponentHead hP (actualLastComponent hP hk) :=
          (actualComponentHead_last hP hk hlast).symm
    have hCnotPathHead : hC.1 ∉ heads P.edges := by
      rw [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]
      exact hCne
    let b : {v : Vtx k // v ∈ heads (F P) \ heads P.edges} :=
      ⟨hC.1, Finset.mem_sdiff.mpr ⟨hC.2, hCnotPathHead⟩⟩
    obtain ⟨s, hs⟩ := chainSourceHead_surjective hP b
    refine ⟨s, ?_⟩
    apply Subtype.ext
    apply actualComponentHead_injective hP
    calc
      actualComponentHead hP (actualChainSourceComponent hP hk s) =
          (chainSourceHead hP s).1 := actualChainSourceComponent_head hP hk s
      _ = b.1 := congrArg Subtype.val hs
      _ = actualComponentHead hP C.1 := rfl

/-- 有终端链情形的源端双射：每个组件恰发出一条链。 -/
noncomputable def actualChainSourceAllEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    {v : Vtx k // v ∈ chainStarts P} ≃ ActualComponent P := by
  apply Equiv.ofBijective (actualChainSourceComponent hP hk)
  constructor
  · exact actualChainSourceComponent_injective hP hk
  · intro C
    let hC : {v : Vtx k // v ∈ heads (F P)} :=
      actualComponentHeadAsHead hP C
    have hCne : hC.1 ≠ P.last := by
      intro heq
      apply hlast
      simpa [heq] using hC.2
    have hCnotPathHead : hC.1 ∉ heads P.edges := by
      rw [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]
      exact hCne
    let b : {v : Vtx k // v ∈ heads (F P) \ heads P.edges} :=
      ⟨hC.1, Finset.mem_sdiff.mpr ⟨hC.2, hCnotPathHead⟩⟩
    obtain ⟨s, hs⟩ := chainSourceHead_surjective hP b
    refine ⟨s, ?_⟩
    apply actualComponentHead_injective hP
    calc
      actualComponentHead hP (actualChainSourceComponent hP hk s) =
          (chainSourceHead hP s).1 := actualChainSourceComponent_head hP hk s
      _ = b.1 := congrArg Subtype.val hs
      _ = actualComponentHead hP C := rfl

/-- 若末点是 `F(P)` 的头，则所有 `D_P` 终点都是非终端终点。 -/
noncomputable def chainEndsAllNonterminalEquiv
    {P : HPath k} (hP : P.IsHamiltonian)
    (hlast : P.last ∈ heads (F P)) :
    {v : Vtx k // v ∈ chainEnds P} ≃
      {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} where
  toFun e := by
    refine ⟨e.1, e.2, ?_⟩
    intro heq
    have hlastEnd : P.last ∈ chainEnds P := heq ▸ e.2
    have hlastS := (last_mem_chainEnds_iff hP).mp hlastEnd
    exact ((last_mem_Sset_iff_not_mem_heads hP).mp hlastS) hlast
  invFun e := ⟨e.1, e.2.1⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- 若末点不是 `F(P)` 的头，则终点集分成非终端终点与唯一终端符号。 -/
noncomputable def chainEndsTerminalEquiv
    {P : HPath k} (hP : P.IsHamiltonian)
    (hlast : P.last ∉ heads (F P)) :
    {v : Vtx k // v ∈ chainEnds P} ≃
      Sum {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} Unit where
  toFun e := if heq : e.1 = P.last then Sum.inr ()
    else Sum.inl ⟨e.1, e.2, heq⟩
  invFun z := match z with
    | Sum.inl e => ⟨e.1, e.2.1⟩
    | Sum.inr _ =>
        ⟨P.last, (last_mem_chainEnds_iff hP).mpr
          ((last_mem_Sset_iff_not_mem_heads hP).mpr hlast)⟩
  left_inv e := by
    by_cases heq : e.1 = P.last
    · simp [heq]
      apply Subtype.ext
      exact heq.symm
    · simp [heq]
  right_inv z := by
    cases z with
    | inl e => simp [e.2.2]
    | inr u => cases u; simp

/-- 真实无终端链情形的完整组件匹配。 -/
noncomputable def actualChainMatchingZero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    ChainMatchingZero (ActualComponent P)
      {v : Vtx k // v ∈ chainStarts P} where
  root := actualRootComponent hP hk
  last := actualLastComponent hP hk
  source := actualChainSourceNonLastEquiv hP hk hlast
  target := (chainStartEndEquiv (by omega) P).trans
    ((chainEndsAllNonterminalEquiv hP hlast).trans
      ((chainTargetComponentEquiv hP hk).trans
        (nonRootComponentNeEquiv hP hk)))

/-- 真实有唯一终端链情形的完整组件匹配。 -/
noncomputable def actualChainMatchingOne
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    ChainMatchingOne (ActualComponent P)
      {v : Vtx k // v ∈ chainStarts P} where
  root := actualRootComponent hP hk
  source := actualChainSourceAllEquiv hP hk hlast
  target := (chainStartEndEquiv (by omega) P).trans
    ((chainEndsTerminalEquiv hP hlast).trans
      (Equiv.sumCongr
        ((chainTargetComponentEquiv hP hk).trans
          (nonRootComponentNeEquiv hP hk))
        (Equiv.refl Unit)))

end PreimageChain

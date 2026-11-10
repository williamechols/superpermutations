import Hunter.ProofsWP
import PreimageChain.Limitations

/-!
# Hunter 预像链图

本模块在固定的 Hunter 实现上直接定义正文公式 (8) 的 `D_P`。边 `u → v`
表示原 Hamilton 路径含边 `u → σv`。下面的度数定理不是抽象接口：它直接
使用 `HPath.edges`、`Sset` 和上游已经验证的简单路径入度/出度性质。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 论文的辅助有向图 `D_P`。 -/
noncomputable def chainGraph (P : HPath k) : Finset (Vtx k × Vtx k) :=
  ((Sset P).product (Sset P)).filter fun e => (e.1, sigma e.2) ∈ P.edges

@[simp] theorem mem_chainGraph {P : HPath k} {u v : Vtx k} :
    (u, v) ∈ chainGraph P ↔
      u ∈ Sset P ∧ v ∈ Sset P ∧ (u, sigma v) ∈ P.edges := by
  simp [chainGraph, and_assoc]

/-- 辅助图的每个顶点出度至多一。 -/
theorem chainGraph_out_le_one (hk : 1 ≤ k) (P : HPath k) (u : Vtx k) :
    (outV (chainGraph P) u).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [outV, mem_out] at ha hb
  have haD := (mem_chainGraph.mp ha.1).2.2
  have hbD := (mem_chainGraph.mp hb.1).2.2
  have ha1 : a.1 = u := by simpa using ha.2
  have hb1 : b.1 = u := by simpa using hb.2
  have haP : (u, sigma a.2) ∈ P.edges := by simpa [ha1] using haD
  have hbP : (u, sigma b.2) ∈ P.edges := by simpa [hb1] using hbD
  have heq : (u, sigma a.2) = (u, sigma b.2) :=
    Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P u)
      (u, sigma a.2) (by rw [outV, mem_out]; exact ⟨haP, by simp⟩)
      (u, sigma b.2) (by rw [outV, mem_out]; exact ⟨hbP, by simp⟩)
  have hsigma : sigma a.2 = sigma b.2 :=
    congrArg (fun e : Vtx k × Vtx k => e.2) heq
  have htarget : a.2 = b.2 := by
    have h := congrArg sigmaInv hsigma
    simpa [sigmaInv_sigma hk] using h
  exact Prod.ext (ha1.trans hb1.symm) htarget

/-- 辅助图的每个顶点入度至多一。 -/
theorem chainGraph_into_le_one (P : HPath k) (v : Vtx k) :
    (intoV (chainGraph P) v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [intoV, mem_into] at ha hb
  have haD := (mem_chainGraph.mp ha.1).2.2
  have hbD := (mem_chainGraph.mp hb.1).2.2
  have ha2 : a.2 = v := by simpa using ha.2
  have hb2 : b.2 = v := by simpa using hb.2
  have haP : (a.1, sigma v) ∈ P.edges := by simpa [ha2] using haD
  have hbP : (b.1, sigma v) ∈ P.edges := by simpa [hb2] using hbD
  have heq : (a.1, sigma v) = (b.1, sigma v) :=
    Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P (sigma v))
      (a.1, sigma v) (by rw [intoV, mem_into]; exact ⟨haP, by simp⟩)
      (b.1, sigma v) (by rw [intoV, mem_into]; exact ⟨hbP, by simp⟩)
  have hsource' := congrArg (fun e : Vtx k × Vtx k => e.1) heq
  have hsource : a.1 = b.1 := by simpa using hsource'
  exact Prod.ext hsource (ha2.trans hb2.symm)

/-- `D_P` 是有限的部分置换图：每点入度、出度均至多一。 -/
theorem chainGraph_degree (hk : 1 ≤ k) (P : HPath k) (v : Vtx k) :
    (outV (chainGraph P) v).card ≤ 1 ∧
      (intoV (chainGraph P) v).card ≤ 1 :=
  ⟨chainGraph_out_le_one hk P v, chainGraph_into_le_one P v⟩

/-- `D_P` 的起点集合。 -/
noncomputable def chainStarts (P : HPath k) : Finset (Vtx k) :=
  (Sset P).filter fun v => intoV (chainGraph P) v = ∅

/-- `D_P` 的终点集合。 -/
noncomputable def chainEnds (P : HPath k) : Finset (Vtx k) :=
  (Sset P).filter fun v => outV (chainGraph P) v = ∅

@[simp] theorem mem_chainStarts {P : HPath k} {v : Vtx k} :
    v ∈ chainStarts P ↔ v ∈ Sset P ∧ intoV (chainGraph P) v = ∅ := by
  simp [chainStarts]

@[simp] theorem mem_chainEnds {P : HPath k} {v : Vtx k} :
    v ∈ chainEnds P ↔ v ∈ Sset P ∧ outV (chainGraph P) v = ∅ := by
  simp [chainEnds]

/--
链起点与唯一的 `E₂` 型边界前驱等价。这里先在原路径中陈述边界性质；
前驱不属于 `S(P)` 正是它没有成为另一条 `D_P` 内边的原因。
-/
theorem chainStart_iff_unique_boundary_predecessor
    {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k} :
    v ∈ chainStarts P ↔
      v ∈ Sset P ∧
        ∃! b : Vtx k, b ∉ Sset P ∧ (b, sigma v) ∈ P.edges := by
  constructor
  · intro hv
    have hvData := mem_chainStarts.mp hv
    have hvS := hvData.1
    have hvNoIn := hvData.2
    have hvNotCm1 : v ∉ Cm1 P := by
      rw [Sset, Finset.mem_filter] at hvS
      exact hvS.2.1
    have hsigmaNotFirst : sigma v ≠ P.first := by
      intro heq
      have hsigmaC0 : sigma v ∈ C0 P := by
        rw [Hunter.ProofsPathrule.mem_C0_iff]
        intro u _hclass
        rw [heq, Hunter.ProofsStructure.pos_first]
        exact Nat.zero_le _
      exact hvNotCm1 (Hunter.ProofsPathrule.mem_Cm1_iff.mpr hsigmaC0)
    obtain ⟨b, hbEdge⟩ :=
      Hunter.ProofsSpine.exists_pred (hP (sigma v)) hsigmaNotFirst
    have hbNotS : b ∉ Sset P := by
      intro hbS
      have hbD : (b, v) ∈ chainGraph P :=
        mem_chainGraph.mpr ⟨hbS, hvS, hbEdge⟩
      have hbIn : (b, v) ∈ intoV (chainGraph P) v := by
        rw [intoV, mem_into]
        exact ⟨hbD, by simp⟩
      rw [hvNoIn] at hbIn
      exact Finset.notMem_empty _ hbIn
    refine ⟨hvS, b, ⟨hbNotS, hbEdge⟩, ?_⟩
    intro b' hb'
    have heq : (b', sigma v) = (b, sigma v) :=
      Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P (sigma v))
        (b', sigma v) (by rw [intoV, mem_into]; exact ⟨hb'.2, by simp⟩)
        (b, sigma v) (by rw [intoV, mem_into]; exact ⟨hbEdge, by simp⟩)
    have hfirst := congrArg (fun e : Vtx k × Vtx k => e.1) heq
    simpa using hfirst
  · rintro ⟨hvS, b, ⟨hbNotS, hbEdge⟩, _hunique⟩
    rw [mem_chainStarts]
    refine ⟨hvS, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [intoV, mem_into] at he
    have heD := mem_chainGraph.mp he.1
    have heTarget : e.2 = v := by simpa using he.2
    have hePath : (e.1, sigma v) ∈ P.edges := by
      simpa [heTarget] using heD.2.2
    have hedgeEq : (e.1, sigma v) = (b, sigma v) :=
      Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P (sigma v))
        (e.1, sigma v) (by rw [intoV, mem_into]; exact ⟨hePath, by simp⟩)
        (b, sigma v) (by rw [intoV, mem_into]; exact ⟨hbEdge, by simp⟩)
    have hsource' := congrArg (fun q : Vtx k × Vtx k => q.1) hedgeEq
    have hsource : e.1 = b := by simpa using hsource'
    exact hbNotS (hsource ▸ heD.1)

/-- 一个非 `S` 前驱与一个 `S` 旋转边共同指向同一点时，该点确为 Hunter 的 double。 -/
theorem boundary_target_mem_doubles
    {P : HPath k} {b v : Vtx k}
    (hbNotS : b ∉ Sset P) (hvS : v ∈ Sset P)
    (hbEdge : (b, sigma v) ∈ P.edges) :
    sigma v ∈ doubles P (Sset P) := by
  have hOriginal : (b, sigma v) ∈ Xstep1 P (Sset P) := by
    rw [Xstep1, Finset.mem_union]
    left
    rw [Finset.mem_sdiff]
    refine ⟨hbEdge, ?_⟩
    intro hremoved
    rw [E1removed, Finset.mem_filter] at hremoved
    exact hbNotS hremoved.2
  have hAdded : (v, sigma v) ∈ Xstep1 P (Sset P) := by
    rw [Xstep1, Finset.mem_union]
    right
    rw [addedEdges, Finset.mem_image]
    exact ⟨v, hvS, rfl⟩
  have hbne : b ≠ v := by
    intro heq
    exact hbNotS (heq ▸ hvS)
  have hedgeNe : (b, sigma v) ≠ (v, sigma v) := by simp [hbne]
  have hpair : ({(b, sigma v), (v, sigma v)} : Finset (Vtx k × Vtx k)) ⊆
      intoV (Xstep1 P (Sset P)) (sigma v) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rw [intoV, mem_into]
      exact ⟨hOriginal, by simp⟩
    · rw [intoV, mem_into]
      exact ⟨hAdded, by simp⟩
  have htwo : 2 ≤ (intoV (Xstep1 P (Sset P)) (sigma v)).card := by
    calc
      2 = ({(b, sigma v), (v, sigma v)} : Finset (Vtx k × Vtx k)).card :=
        (Finset.card_pair hedgeNe).symm
      _ ≤ _ := Finset.card_le_card hpair
  have hdecomp : intoV (Xstep1 P (Sset P)) (sigma v) =
      intoV (P.edges \ E1removed P (Sset P)) (sigma v) ∪
        intoV (addedEdges (Sset P)) (sigma v) := by
    unfold Xstep1
    exact Hunter.ProofsSpine.intoV_union _ _ _
  have hA : (intoV (P.edges \ E1removed P (Sset P)) (sigma v)).card ≤ 1 :=
    le_trans
      (Finset.card_le_card (Hunter.ProofsSpine.intoV_mono Finset.sdiff_subset _))
      (Hunter.ProofsSpine.path_into_le_one P _)
  have hB : (intoV (addedEdges (Sset P)) (sigma v)).card ≤ 1 :=
    Hunter.ProofsSpine.intoV_addedEdges_le_one _ _
  have hleTwo : (intoV (Xstep1 P (Sset P)) (sigma v)).card ≤ 2 := by
    rw [hdecomp]
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hcard : (intoV (Xstep1 P (Sset P)) (sigma v)).card = 2 :=
    le_antisymm hleTwo htwo
  rw [doubles, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hcard⟩

/-- 链起点的唯一边界前驱确是 `F(P)` 的分量头，且其边属于 `E₂`。 -/
theorem chainStart_has_unique_E2_head
    {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∈ chainStarts P) :
    ∃! b : Vtx k,
      b ∈ heads (F P) ∧ (b, sigma v) ∈ E2removed P (Sset P) := by
  obtain ⟨hvS, b, ⟨hbNotS, hbEdge⟩, hbUnique⟩ :=
    (chainStart_iff_unique_boundary_predecessor hP).mp hv
  have hdouble := boundary_target_mem_doubles hbNotS hvS hbEdge
  have hE2 : (b, sigma v) ∈ E2removed P (Sset P) := by
    rw [E2removed, Finset.mem_filter]
    exact ⟨hbEdge, hdouble⟩
  have hout : outV (F P) b = ∅ := by
    rw [Hunter.ProofsStructure.F_eq]
    exact (Hunter.ProofsSpine.key_doubles_iff P (Sset P)
      (Hunter.sset_sPrecond P) hbEdge).mp hdouble
  have hhead : b ∈ heads (F P) := by
    rw [heads, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hout⟩
  refine ⟨b, ⟨hhead, hE2⟩, ?_⟩
  intro b' hb'
  have hb'Edge : (b', sigma v) ∈ P.edges :=
    E2removed_subset P (Sset P) hb'.2
  have hedgeEq : (b', sigma v) = (b, sigma v) :=
    Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P (sigma v))
      (b', sigma v) (by rw [intoV, mem_into]; exact ⟨hb'Edge, by simp⟩)
      (b, sigma v) (by rw [intoV, mem_into]; exact ⟨hbEdge, by simp⟩)
  have hsource' := congrArg (fun q : Vtx k × Vtx k => q.1) hedgeEq
  simpa using hsource'

/--
链终点要么是 Hamilton 路径的最终顶点，要么有唯一的原路径后继，且该后继
不是任何 `S(P)` 槽位的旋转像。这是定理 4.1 靶端匹配的顶点级核心。
-/
theorem chainEnd_iff_terminal_or_unique_exit
    {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k} :
    v ∈ chainEnds P ↔
      v ∈ Sset P ∧
        (v = P.last ∨
          ∃! a : Vtx k, (v, a) ∈ P.edges ∧
            ∀ u : Vtx k, u ∈ Sset P → a ≠ sigma u) := by
  constructor
  · intro hv
    have hvData := mem_chainEnds.mp hv
    refine ⟨hvData.1, ?_⟩
    by_cases hvLast : v = P.last
    · exact Or.inl hvLast
    · right
      obtain ⟨a, haEdge⟩ :=
        Hunter.ProofsStructure.out_edge_of_ne_last (hP v) hvLast
      have haNoSlot : ∀ u : Vtx k, u ∈ Sset P → a ≠ sigma u := by
        intro u huS heq
        have hD : (v, u) ∈ chainGraph P := by
          apply mem_chainGraph.mpr
          refine ⟨hvData.1, huS, ?_⟩
          simpa [heq] using haEdge
        have hOut : (v, u) ∈ outV (chainGraph P) v := by
          rw [outV, mem_out]
          exact ⟨hD, by simp⟩
        rw [hvData.2] at hOut
        exact Finset.notMem_empty _ hOut
      refine ⟨a, ⟨haEdge, haNoSlot⟩, ?_⟩
      intro a' ha'
      have hedgeEq : (v, a') = (v, a) :=
        Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P v)
          (v, a') (by rw [outV, mem_out]; exact ⟨ha'.1, by simp⟩)
          (v, a) (by rw [outV, mem_out]; exact ⟨haEdge, by simp⟩)
      have htarget' := congrArg (fun q : Vtx k × Vtx k => q.2) hedgeEq
      simpa using htarget'
  · rintro ⟨hvS, hvLast | ⟨a, ⟨haEdge, haNoSlot⟩, _hunique⟩⟩
    · rw [mem_chainEnds]
      refine ⟨hvS, ?_⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [outV, mem_out] at he
      have hePath := (mem_chainGraph.mp he.1).2.2
      have heSource : e.1 = v := by simpa using he.2
      exact (Hunter.ProofsStructure.ne_last_of_out_edge hePath)
        (heSource.trans hvLast)
    · rw [mem_chainEnds]
      refine ⟨hvS, ?_⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [outV, mem_out] at he
      have heD := mem_chainGraph.mp he.1
      have heSource : e.1 = v := by simpa using he.2
      have hePath : (v, sigma e.2) ∈ P.edges := by
        simpa [heSource] using heD.2.2
      have hedgeEq : (v, sigma e.2) = (v, a) :=
        Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P v)
          (v, sigma e.2) (by rw [outV, mem_out]; exact ⟨hePath, by simp⟩)
          (v, a) (by rw [outV, mem_out]; exact ⟨haEdge, by simp⟩)
      have htarget' := congrArg (fun q : Vtx k × Vtx k => q.2) hedgeEq
      have htarget : sigma e.2 = a := by simpa using htarget'
      exact (haNoSlot e.2 heD.2.1) htarget.symm

/-- 非终端链的原路径出口在 `F(P)` 中成为分量尾，并且该边属于 `E₁`。 -/
theorem exit_target_is_tail
    {P : HPath k} {v a : Vtx k}
    (hvS : v ∈ Sset P) (haEdge : (v, a) ∈ P.edges)
    (haNoSlot : ∀ u : Vtx k, u ∈ Sset P → a ≠ sigma u) :
    a ∈ tails (F P) ∧ (v, a) ∈ E1removed P (Sset P) := by
  have hE1 : (v, a) ∈ E1removed P (Sset P) := by
    rw [E1removed, Finset.mem_filter]
    exact ⟨haEdge, hvS⟩
  have htail : a ∈ tails (F P) := by
    rw [tails, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [intoV, mem_into] at he
    have heTarget : e.2 = a := by simpa using he.2
    have heF := he.1
    rw [Hunter.ProofsStructure.F_eq, fPS, Finset.mem_sdiff] at heF
    rw [Xstep1, Finset.mem_union] at heF
    rcases heF.1 with heOriginal | heAdded
    · rw [Finset.mem_sdiff] at heOriginal
      have hePath : (e.1, a) ∈ P.edges := by
        rw [← heTarget]
        simpa only [Prod.eta] using heOriginal.1
      have hedgeEq : (e.1, a) = (v, a) :=
        Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P a)
          (e.1, a) (by rw [intoV, mem_into]; exact ⟨hePath, by simp⟩)
          (v, a) (by rw [intoV, mem_into]; exact ⟨haEdge, by simp⟩)
      have hsource' := congrArg (fun q : Vtx k × Vtx k => q.1) hedgeEq
      have hsource : e.1 = v := by simpa using hsource'
      apply heOriginal.2
      rw [E1removed, Finset.mem_filter]
      exact ⟨heOriginal.1, hsource ▸ hvS⟩
    · rw [addedEdges, Finset.mem_image] at heAdded
      obtain ⟨u, huS, hue⟩ := heAdded
      have htarget : sigma u = a := by
        calc
          sigma u = e.2 := congrArg Prod.snd hue
          _ = a := heTarget
      exact (haNoSlot u huS) htarget.symm
  exact ⟨htail, hE1⟩

/-- 每个非终端链终点有唯一的 `E₁` 出口，且出口靶点是 `F(P)` 的分量尾。 -/
theorem chainEnd_nonterminal_has_unique_E1_tail
    {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∈ chainEnds P) (hvNotLast : v ≠ P.last) :
    ∃! a : Vtx k,
      a ∈ tails (F P) ∧ (v, a) ∈ E1removed P (Sset P) := by
  obtain ⟨hvS, hvTerminal | ⟨a, ⟨haEdge, haNoSlot⟩, haUnique⟩⟩ :=
    (chainEnd_iff_terminal_or_unique_exit hP).mp hv
  · exact False.elim (hvNotLast hvTerminal)
  · have htailE1 := exit_target_is_tail hvS haEdge haNoSlot
    refine ⟨a, htailE1, ?_⟩
    intro a' ha'
    have ha'Edge : (v, a') ∈ P.edges :=
      E1removed_subset P (Sset P) ha'.2
    have hedgeEq : (v, a') = (v, a) :=
      Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P v)
        (v, a') (by rw [outV, mem_out]; exact ⟨ha'Edge, by simp⟩)
        (v, a) (by rw [outV, mem_out]; exact ⟨haEdge, by simp⟩)
    have htarget' := congrArg (fun q : Vtx k × Vtx k => q.2) hedgeEq
    simpa using htarget'

/-- 链起点对应的 `F(P)` 分量头；值由上面的存在唯一性定理确定。 -/
noncomputable def chainSourceHead
    {P : HPath k} (hP : P.IsHamiltonian)
    (v : {v : Vtx k // v ∈ chainStarts P}) :
    {b : Vtx k // b ∈ heads (F P) \ heads P.edges} := by
  let b := Classical.choose (chainStart_has_unique_E2_head hP v.2)
  have hb := Classical.choose_spec (chainStart_has_unique_E2_head hP v.2)
  refine ⟨b, Finset.mem_sdiff.mpr ⟨hb.1.1, ?_⟩⟩
  rw [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]
  have hbEdge : (b, sigma v.1) ∈ P.edges :=
    E2removed_subset P (Sset P) hb.1.2
  exact Hunter.ProofsStructure.ne_last_of_out_edge hbEdge

theorem chainSourceHead_spec
    {P : HPath k} (hP : P.IsHamiltonian)
    (v : {v : Vtx k // v ∈ chainStarts P}) :
    ((chainSourceHead hP v).1, sigma v.1) ∈ E2removed P (Sset P) := by
  unfold chainSourceHead
  exact (Classical.choose_spec (chainStart_has_unique_E2_head hP v.2)).1.2

/-- 不同链起点不能使用同一个源分量头。 -/
theorem chainSourceHead_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective (chainSourceHead hP) := by
  intro v w heq
  have hvE2 := chainSourceHead_spec hP v
  have hwE2 := chainSourceHead_spec hP w
  have hb : (chainSourceHead hP v).1 = (chainSourceHead hP w).1 :=
    congrArg Subtype.val heq
  have hvPath := E2removed_subset P (Sset P) hvE2
  have hwPath := E2removed_subset P (Sset P) hwE2
  have hedgeEq :
      ((chainSourceHead hP v).1, sigma v.1) =
        ((chainSourceHead hP v).1, sigma w.1) :=
    Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_out_le_one P (chainSourceHead hP v).1)
      ((chainSourceHead hP v).1, sigma v.1)
        (by rw [outV, mem_out]; exact ⟨hvPath, by simp⟩)
      ((chainSourceHead hP v).1, sigma w.1)
        (by rw [outV, mem_out]; exact ⟨by simpa [hb] using hwPath, by simp⟩)
  have hsigma' := congrArg (fun q : Vtx k × Vtx k => q.2) hedgeEq
  have hsigma : sigma v.1 = sigma w.1 := by simpa using hsigma'
  apply Subtype.ext
  exact Hunter.ProofsSpine.sigma_inj hsigma

/-- 每个不是原路径最终头的 `F(P)` 分量头都来自唯一链起点。 -/
theorem chainSourceHead_surjective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Surjective (chainSourceHead hP) := by
  intro b
  have hbNotHeadP : b.1 ∉ heads P.edges := (Finset.mem_sdiff.mp b.2).2
  have hbOut : outV P.edges b.1 ≠ ∅ := by
    intro hempty
    apply hbNotHeadP
    simpa [heads] using hempty
  obtain ⟨e, heOut⟩ := Finset.nonempty_iff_ne_empty.mpr hbOut
  rw [outV, mem_out] at heOut
  have heSource : e.1 = b.1 := by simpa using heOut.2
  have heE2 : e ∈ E2removed P (Sset P) := by
    rw [Hunter.clm_e2 (Hunter.sset_sPrecond P), out, Finset.mem_filter]
    refine ⟨heOut.1, ?_⟩
    -- Lean 4.35 port: `simpa using b.2` now simplifies the membership to `True`.
    simpa [heSource, F] using Finset.mem_sdiff.mp b.2
  have heDouble : e.2 ∈ doubles P (Sset P) := by
    rw [E2removed, Finset.mem_filter] at heE2
    exact heE2.2
  obtain ⟨ae, hae⟩ := Hunter.ProofsStructure.double_imp_added_inedge heDouble
  simp only [intoV, mem_into, addedEdges, Finset.mem_image,
    Finset.mem_singleton] at hae
  obtain ⟨⟨v, hvS, hve⟩, haeTarget⟩ := hae
  have hsigma : sigma v = e.2 := by
    rw [← hve] at haeTarget
    exact haeTarget
  have hbNotS : b.1 ∉ Sset P := by
    intro hbS
    have hnonempty : (outV (F P) b.1).Nonempty := by
      have hnonempty' := Hunter.ProofsSpine.outV_fPS_ne_empty_of_mem_S P (Sset P)
        (Hunter.sset_sPrecond P) hbS
      simpa only [Hunter.ProofsStructure.F_eq] using hnonempty'
    have hbHead : outV (F P) b.1 = ∅ := by
      have hbHeadMem := (Finset.mem_sdiff.mp b.2).1
      exact (Finset.mem_filter.mp hbHeadMem).2
    rw [hbHead] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hbEdge : (b.1, sigma v) ∈ P.edges := by
    have hePath : e ∈ P.edges := E2removed_subset P (Sset P) heE2
    rw [← heSource, hsigma]
    simpa only [Prod.eta] using hePath
  have hvStart : v ∈ chainStarts P := by
    apply (chainStart_iff_unique_boundary_predecessor hP).mpr
    refine ⟨hvS, b.1, ⟨hbNotS, hbEdge⟩, ?_⟩
    intro b' hb'
    have hedgeEq : (b', sigma v) = (b.1, sigma v) :=
      Finset.card_le_one.mp (Hunter.ProofsSpine.path_into_le_one P (sigma v))
        (b', sigma v) (by rw [intoV, mem_into]; exact ⟨hb'.2, by simp⟩)
        (b.1, sigma v) (by rw [intoV, mem_into]; exact ⟨hbEdge, by simp⟩)
    have hsource' := congrArg (fun q : Vtx k × Vtx k => q.1) hedgeEq
    simpa using hsource'
  let sv : {v : Vtx k // v ∈ chainStarts P} := ⟨v, hvStart⟩
  refine ⟨sv, ?_⟩
  apply Subtype.ext
  have hunique := chainStart_has_unique_E2_head hP hvStart
  apply hunique.unique
  · exact ⟨(Finset.mem_sdiff.mp (chainSourceHead hP sv).2).1,
      chainSourceHead_spec hP sv⟩
  · refine ⟨(Finset.mem_sdiff.mp b.2).1, ?_⟩
    have : (b.1, sigma v) ∈ E2removed P (Sset P) := by
      have heqPair : (b.1, sigma v) = e := by
        apply Prod.ext
        · exact heSource.symm
        · exact hsigma
      simpa [heqPair] using heE2
    exact this

/-- 源端的实际有限双射：链起点 ↔ 非最终的 `F(P)` 分量头。 -/
noncomputable def chainSourceHeadEquiv
    {P : HPath k} (hP : P.IsHamiltonian) :
    {v : Vtx k // v ∈ chainStarts P} ≃
      {b : Vtx k // b ∈ heads (F P) \ heads P.edges} :=
  Equiv.ofBijective (chainSourceHead hP)
    ⟨chainSourceHead_injective hP, chainSourceHead_surjective hP⟩

/-- 非终端链终点对应的 `F(P)` 分量尾。 -/
noncomputable def chainTargetTail
    {P : HPath k} (hP : P.IsHamiltonian)
    (v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    {a : Vtx k // a ∈ tails (F P) \ tails P.edges} := by
  let a := Classical.choose
    (chainEnd_nonterminal_has_unique_E1_tail hP v.2.1 v.2.2)
  have ha := Classical.choose_spec
    (chainEnd_nonterminal_has_unique_E1_tail hP v.2.1 v.2.2)
  refine ⟨a, Finset.mem_sdiff.mpr ⟨ha.1.1, ?_⟩⟩
  intro haTail
  have haEmpty : intoV P.edges a = ∅ :=
    (Finset.mem_filter.mp haTail).2
  have haEdge : (v.1, a) ∈ P.edges :=
    E1removed_subset P (Sset P) ha.1.2
  have haIn : (v.1, a) ∈ intoV P.edges a := by
    rw [intoV, mem_into]
    exact ⟨haEdge, by simp⟩
  rw [haEmpty] at haIn
  exact Finset.notMem_empty _ haIn

theorem chainTargetTail_spec
    {P : HPath k} (hP : P.IsHamiltonian)
    (v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    (v.1, (chainTargetTail hP v).1) ∈ E1removed P (Sset P) := by
  unfold chainTargetTail
  exact (Classical.choose_spec
    (chainEnd_nonterminal_has_unique_E1_tail hP v.2.1 v.2.2)).1.2

theorem chainTargetTail_injective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Injective (chainTargetTail hP) := by
  intro v w heq
  have hvE1 := chainTargetTail_spec hP v
  have hwE1 := chainTargetTail_spec hP w
  have ha : (chainTargetTail hP v).1 = (chainTargetTail hP w).1 :=
    congrArg Subtype.val heq
  have hvPath := E1removed_subset P (Sset P) hvE1
  have hwPath := E1removed_subset P (Sset P) hwE1
  have hedgeEq :
      (v.1, (chainTargetTail hP v).1) =
        (w.1, (chainTargetTail hP v).1) :=
    Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_into_le_one P (chainTargetTail hP v).1)
      (v.1, (chainTargetTail hP v).1)
        (by rw [intoV, mem_into]; exact ⟨hvPath, by simp⟩)
      (w.1, (chainTargetTail hP v).1)
        (by rw [intoV, mem_into]; exact ⟨by simpa [ha] using hwPath, by simp⟩)
  have hsource' := congrArg (fun q : Vtx k × Vtx k => q.1) hedgeEq
  apply Subtype.ext
  simpa using hsource'

theorem chainTargetTail_surjective
    {P : HPath k} (hP : P.IsHamiltonian) :
    Function.Surjective (chainTargetTail hP) := by
  intro a
  have haNotTailP : a.1 ∉ tails P.edges := (Finset.mem_sdiff.mp a.2).2
  have haInNe : intoV P.edges a.1 ≠ ∅ := by
    intro hempty
    apply haNotTailP
    simpa [tails] using hempty
  obtain ⟨e, heIn⟩ := Finset.nonempty_iff_ne_empty.mpr haInNe
  rw [intoV, mem_into] at heIn
  have heTarget : e.2 = a.1 := by simpa using heIn.2
  have heE1 : e ∈ E1removed P (Sset P) := by
    apply Hunter.clm_e1 (Hunter.sset_sPrecond P)
    rw [into, Finset.mem_filter]
    refine ⟨heIn.1, ?_⟩
    -- Lean 4.35 port: `simpa using a.2` now simplifies the membership to `True`.
    simpa [heTarget, F] using Finset.mem_sdiff.mp a.2
  have heSourceS : e.1 ∈ Sset P := by
    rw [E1removed, Finset.mem_filter] at heE1
    exact heE1.2
  have haNoSlot : ∀ u : Vtx k, u ∈ Sset P → a.1 ≠ sigma u := by
    intro u huS heq
    have huNotCm1 : u ∉ Cm1 P := by
      rw [Sset, Finset.mem_filter] at huS
      exact huS.2.1
    have huF : (u, sigma u) ∈ F P :=
      Hunter.ProofsStructure.mem_F_sigma_of_not_Cm1 huNotCm1
    have huIn : (u, sigma u) ∈ intoV (F P) a.1 := by
      rw [intoV, mem_into]
      exact ⟨huF, by simp [heq]⟩
    have haTailMem := (Finset.mem_sdiff.mp a.2).1
    have haEmpty : intoV (F P) a.1 = ∅ :=
      (Finset.mem_filter.mp haTailMem).2
    rw [haEmpty] at huIn
    exact Finset.notMem_empty _ huIn
  have heEdge : (e.1, a.1) ∈ P.edges := by
    rw [← heTarget]
    simpa only [Prod.eta] using heIn.1
  have heNotLast : e.1 ≠ P.last :=
    Hunter.ProofsStructure.ne_last_of_out_edge heEdge
  have heEnd : e.1 ∈ chainEnds P := by
    apply (chainEnd_iff_terminal_or_unique_exit hP).mpr
    refine ⟨heSourceS, Or.inr ⟨a.1, ⟨heEdge, haNoSlot⟩, ?_⟩⟩
    intro a' ha'
    have hedgeEq : (e.1, a') = (e.1, a.1) :=
      Finset.card_le_one.mp (Hunter.ProofsSpine.path_out_le_one P e.1)
        (e.1, a') (by rw [outV, mem_out]; exact ⟨ha'.1, by simp⟩)
        (e.1, a.1) (by rw [outV, mem_out]; exact ⟨heEdge, by simp⟩)
    have htarget' := congrArg (fun q : Vtx k × Vtx k => q.2) hedgeEq
    simpa using htarget'
  let ev : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
    ⟨e.1, heEnd, heNotLast⟩
  refine ⟨ev, ?_⟩
  apply Subtype.ext
  have hunique := chainEnd_nonterminal_has_unique_E1_tail hP heEnd heNotLast
  apply hunique.unique
  · exact ⟨(Finset.mem_sdiff.mp (chainTargetTail hP ev).2).1,
      chainTargetTail_spec hP ev⟩
  · refine ⟨(Finset.mem_sdiff.mp a.2).1, ?_⟩
    have heqPair : (e.1, a.1) = e := by
      apply Prod.ext
      · rfl
      · exact heTarget.symm
    simpa [heqPair] using heE1

/-- 靶端的实际有限双射：非终端链终点 ↔ 非根的 `F(P)` 分量尾。 -/
noncomputable def chainTargetTailEquiv
    {P : HPath k} (hP : P.IsHamiltonian) :
    {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} ≃
      {a : Vtx k // a ∈ tails (F P) \ tails P.edges} :=
  Equiv.ofBijective (chainTargetTail hP)
    ⟨chainTargetTail_injective hP, chainTargetTail_surjective hP⟩

/-- 源端双射给出的精确链数：总链数为 `c-1+I` 的布尔形式。 -/
theorem card_chainStarts
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (chainStarts P).card + (if P.last ∈ heads (F P) then 1 else 0) =
      numComps (F P) := by
  have hequiv := Fintype.card_congr (chainSourceHeadEquiv hP)
  have hcard : (chainStarts P).card =
      (heads (F P) \ heads P.edges).card := by
    calc
      (chainStarts P).card = Fintype.card ↑(chainStarts P) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card ↑(heads (F P) \ heads P.edges) := hequiv
      _ = (heads (F P) \ heads P.edges).card := Fintype.card_coe _
  rw [hcard]
  exact Hunter.ProofsWP.head_count hP hk (Hunter.lem_pathrule hP)

/-- 非终端链恰有 `c-1` 条；靶端遗漏的唯一尾是根分量尾 `P.first`。 -/
theorem card_nonterminal_chainEnds
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Fintype.card {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} + 1 =
      numComps (F P) := by
  have hequiv := Fintype.card_congr (chainTargetTailEquiv hP)
  have htargetCard :
      Fintype.card {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} =
        (tails (F P) \ tails P.edges).card := by
    calc
      Fintype.card {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} =
          Fintype.card ↑(tails (F P) \ tails P.edges) := hequiv
      _ = (tails (F P) \ tails P.edges).card := Fintype.card_coe _
  rw [htargetCard]
  have hsubset : tails P.edges ⊆ tails (F P) := by
    rw [Hunter.ProofsWP.tails_edges_ham hP]
    intro v hv
    have hvfirst : v = P.first := by simpa using hv
    simpa [hvfirst] using
      (Hunter.ProofsWP.first_mem_tails hP hk (Hunter.lem_pathrule hP))
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  have htailCard : (tails (F P)).card = numComps (F P) :=
    Hunter.ProofsWP.card_tails_eq_numComps
      (Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk)
      (fun C hC => Hunter.ProofsWP.compTails_F_single (Hunter.lem_pathrule hP) hC)
  rw [htailCard] at hsplit
  rw [Hunter.ProofsWP.tails_edges_ham hP] at hsplit ⊢
  simpa using hsplit

end PreimageChain

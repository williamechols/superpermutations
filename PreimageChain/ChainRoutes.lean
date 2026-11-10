import PreimageChain.ChainGraph

/-!
# 预像链的实际路线

本模块把 `D_P` 中从零入度槽位出发的部分函数轨道线性化为有限、无重复的
顶点列表。核心有限性论证只用 `D_P` 的入度至多一：若从零入度点出发后进入
有向环，沿唯一前驱反推便会得到一条进入起点的边，矛盾。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/--
左唯一关系中，从无前驱头部出发的有限链不会重复顶点。这是线性化 `D_P`
路径分量时排除“尾部掉进有向环”的一般引理。
-/
theorem nodup_of_chain_leftUnique_of_head_no_pred
    {α : Type*} {r : α → α → Prop} {L : List α}
    (hne : L ≠ [])
    (hchain : L.IsChain r)
    (hleft : ∀ ⦃a b c : α⦄, r a c → r b c → a = b)
    (hsource : ∀ a : α, ¬ r a (L.head hne)) :
    L.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  apply Fin.ext
  wlog hle : i.1 ≤ j.1 generalizing i j
  · have hji : L[j.1] = L[i.1] := hij.symm
    have := this hji (Nat.le_of_not_ge hle)
    exact this.symm
  have aux : ∀ (m n : ℕ) (hm : m < L.length) (hn : n < L.length),
      m ≤ n → L[m] = L[n] → m = n := by
    intro m
    induction m with
    | zero =>
        intro n hm hn _hle hmn
        cases n with
        | zero => rfl
        | succ n =>
            have hnstep : n + 1 < L.length := by omega
            have hrel : r L[n] L[n + 1] := hchain.getElem n hnstep
            have hhead : L[0] = L.head hne := by
              obtain ⟨a, t, hL⟩ := List.exists_cons_of_ne_nil hne
              simp [hL]
            exfalso
            apply hsource L[n]
            rw [← hhead, hmn]
            exact hrel
    | succ m ih =>
        intro n hm hn hmn heq
        obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := by
          use n - 1
          omega
        have hmq : m ≤ q := by omega
        have hmstep : m + 1 < L.length := hm
        have hqstep : q + 1 < L.length := hn
        have hmrel : r L[m] L[m + 1] := hchain.getElem m hmstep
        have hqrel : r L[q] L[q + 1] := hchain.getElem q hqstep
        have hprev : L[m] = L[q] := hleft hmrel (by simpa [heq] using hqrel)
        have := ih q (by omega) (by omega) hmq hprev
        omega
  exact aux i.1 j.1 i.2 j.2 hle hij

/-- 有限关系链的头部可以到达链中的任意成员。 -/
theorem chain_head_reaches_of_mem
    {α : Type*} {r : α → α → Prop} {L : List α}
    (hne : L ≠ []) (hchain : L.IsChain r) {v : α} (hv : v ∈ L) :
    Relation.ReflTransGen r (L.head hne) v := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.head_cons]
  induction t generalizing a with
  | nil =>
      simp only [List.mem_singleton] at hv
      subst v
      exact Relation.ReflTransGen.refl
  | cons b t ih =>
      rw [List.isChain_cons_cons] at hchain
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact Relation.ReflTransGen.refl
      · exact (ih (a := b) (List.cons_ne_nil _ _) hchain.2 hv).head hchain.1

/-- 从实际链起点沿 `D_P` 的唯一后继至多追踪 `|S(P)|` 步。 -/
noncomputable def actualChainRoute
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) : List (Vtx k) :=
  Hunter.ProofsPathrule.iterOpt
    (Hunter.ProofsPathrule.succ (chainGraph P)) (Sset P).card s.1

theorem actualChainRoute_ne_nil
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainRoute s ≠ [] :=
  Hunter.ProofsPathrule.iterOpt_ne_nil _ _ _

theorem actualChainRoute_head
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainRoute s).head (actualChainRoute_ne_nil s) = s.1 :=
  Hunter.ProofsPathrule.iterOpt_head_eq _ _ _

/-- 实际路线的每个相邻点对都是一条 `D_P` 边。 -/
theorem actualChainRoute_isChain
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainRoute s).IsChain
      (fun a b => (a, b) ∈ chainGraph P) := by
  exact List.IsChain.imp
    (fun ⦃a b : Vtx k⦄
      (hab : Hunter.ProofsPathrule.succ (chainGraph P) a = some b) =>
        Hunter.ProofsPathrule.edge_of_succ_some hab)
    (Hunter.ProofsPathrule.iterOpt_chain
      (Hunter.ProofsPathrule.succ (chainGraph P)) (Sset P).card s.1)

/-- 实际路线始终留在槽位集合 `S(P)` 中。 -/
theorem mem_Sset_of_mem_actualChainRoute
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P})
    {v : Vtx k} (hv : v ∈ actualChainRoute s) :
    v ∈ Sset P := by
  apply Hunter.ProofsPathrule.iterOpt_mem_closed
    (f := Hunter.ProofsPathrule.succ (chainGraph P))
    (C := Sset P) ?_ (Sset P).card s.1 (mem_chainStarts.mp s.2).1 v hv
  intro a b hab _ha
  exact (mem_chainGraph.mp
    (Hunter.ProofsPathrule.edge_of_succ_some hab)).2.1

/-- 从链起点生成的实际路线无重复。 -/
theorem actualChainRoute_nodup
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainRoute s).Nodup := by
  apply nodup_of_chain_leftUnique_of_head_no_pred
    (actualChainRoute_ne_nil s) (actualChainRoute_isChain s)
  · intro a b c hac hbc
    have haIn : (a, c) ∈ intoV (chainGraph P) c := by
      rw [intoV, mem_into]
      exact ⟨hac, Finset.mem_singleton_self _⟩
    have hbIn : (b, c) ∈ intoV (chainGraph P) c := by
      rw [intoV, mem_into]
      exact ⟨hbc, Finset.mem_singleton_self _⟩
    have heq := Finset.card_le_one.mp (chainGraph_into_le_one P c)
      (a, c) haIn (b, c) hbIn
    exact congrArg Prod.fst heq
  · intro a ha
    have hsHead := actualChainRoute_head s
    have ha' : (a, s.1) ∈ chainGraph P := by simpa [hsHead] using ha
    have haIn : (a, s.1) ∈ intoV (chainGraph P) s.1 := by
      rw [intoV, mem_into]
      exact ⟨ha', Finset.mem_singleton_self _⟩
    rw [(mem_chainStarts.mp s.2).2] at haIn
    exact Finset.notMem_empty _ haIn

/-- 实际路线的长度不超过槽位总数。 -/
theorem actualChainRoute_length_le
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainRoute s).length ≤ (Sset P).card := by
  rw [← List.toFinset_card_of_nodup (actualChainRoute_nodup s)]
  apply Finset.card_le_card
  intro v hv
  exact mem_Sset_of_mem_actualChainRoute s (List.mem_toFinset.mp hv)

/-- 实际路线的最后一个槽位没有 `D_P` 后继。 -/
theorem actualChainRoute_last_succ_none
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    ∀ z, (actualChainRoute s).getLast? = some z →
      Hunter.ProofsPathrule.succ (chainGraph P) z = none := by
  rcases Hunter.ProofsPathrule.iterOpt_last_spec
      (Hunter.ProofsPathrule.succ (chainGraph P)) (Sset P).card s.1 with hlast | hfull
  · exact hlast
  · have hle := actualChainRoute_length_le s
    change (Hunter.ProofsPathrule.iterOpt
      (Hunter.ProofsPathrule.succ (chainGraph P)) (Sset P).card s.1).length ≤
        (Sset P).card at hle
    omega

/-- 一条实际链路线的终点。 -/
noncomputable def actualChainRouteEnd
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) : Vtx k :=
  (actualChainRoute s).getLast (actualChainRoute_ne_nil s)

theorem actualChainRouteEnd_mem_route
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainRouteEnd s ∈ actualChainRoute s :=
  List.getLast_mem (actualChainRoute_ne_nil s)

/-- 每条从起点出发的路线确实终止于 `chainEnds P`。 -/
theorem actualChainRouteEnd_mem_chainEnds
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainRouteEnd s ∈ chainEnds P := by
  rw [mem_chainEnds]
  refine ⟨mem_Sset_of_mem_actualChainRoute s
    (actualChainRouteEnd_mem_route s), ?_⟩
  rw [← Hunter.ProofsPathrule.succ_eq_none_iff]
  apply actualChainRoute_last_succ_none s (actualChainRouteEnd s)
  exact List.getLast?_eq_getLast_of_ne_nil (actualChainRoute_ne_nil s)

/-- 实际路线给出从链起点到其终点的可达性证明。 -/
theorem actualChainRoute_reaches_end
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) s.1 (actualChainRouteEnd s) := by
  have hreach := List.relationReflTransGen_of_exists_isChain
    (actualChainRoute s) (actualChainRoute_isChain s) (actualChainRoute_ne_nil s)
  simpa [actualChainRouteEnd, actualChainRoute_head] using hreach

/-- 实际路线起点可以到达路线中的每个槽位。 -/
theorem actualChainRoute_reaches_mem
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P})
    {v : Vtx k} (hv : v ∈ actualChainRoute s) :
    Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) s.1 v := by
  have h := chain_head_reaches_of_mem (actualChainRoute_ne_nil s)
    (actualChainRoute_isChain s) hv
  simpa [actualChainRoute_head] using h

/-- 到达零入度链起点的 `D_P` 可达关系只能是零步关系。 -/
theorem chain_reaches_start_eq
    {P : HPath k} {x s : Vtx k} (hs : s ∈ chainStarts P)
    (h : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) x s) :
    x = s := by
  rcases h.cases_tail with hxs | ⟨c, _hxc, hcs⟩
  · exact hxs.symm
  · have hIn : (c, s) ∈ intoV (chainGraph P) s := by
      rw [intoV, mem_into]
      exact ⟨hcs, Finset.mem_singleton_self _⟩
    rw [(mem_chainStarts.mp hs).2] at hIn
    exact False.elim (Finset.notMem_empty _ hIn)

/-- 起点到终点的实际映射。 -/
noncomputable def chainStartEnd
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    {v : Vtx k // v ∈ chainEnds P} :=
  ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s⟩

/-- 不同链起点的实际路线不能汇合到同一个终点。 -/
theorem chainStartEnd_injective
    {P : HPath k} : Function.Injective (@chainStartEnd k P) := by
  intro s t hst
  have hsreach := actualChainRoute_reaches_end s
  have htreach : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) t.1 (actualChainRouteEnd s) := by
    have hend : actualChainRouteEnd t = actualChainRouteEnd s :=
      (congrArg Subtype.val hst).symm
    simpa [hend] using actualChainRoute_reaches_end t
  have hleft : Relator.RightUnique
      (Function.swap (fun a b => (a, b) ∈ chainGraph P)) := by
    intro a b c hba hca
    have hbIn : (b, a) ∈ intoV (chainGraph P) a := by
      rw [intoV, mem_into]
      exact ⟨hba, Finset.mem_singleton_self _⟩
    have hcIn : (c, a) ∈ intoV (chainGraph P) a := by
      rw [intoV, mem_into]
      exact ⟨hca, Finset.mem_singleton_self _⟩
    have heq := Finset.card_le_one.mp (chainGraph_into_le_one P a)
      (b, a) hbIn (c, a) hcIn
    exact congrArg Prod.fst heq
  rcases Relation.ReflTransGen.total_of_right_unique hleft
      hsreach.swap htreach.swap with hstReach | htsReach
  · have hreach : Relation.ReflTransGen
        (fun a b => (a, b) ∈ chainGraph P) t.1 s.1 := by
      simpa only [Function.swap] using hstReach.swap
    apply Subtype.ext
    exact (chain_reaches_start_eq (P := P) (x := t.1) (s := s.1) s.2 hreach).symm
  · have hreach : Relation.ReflTransGen
        (fun a b => (a, b) ∈ chainGraph P) s.1 t.1 := by
      simpa only [Function.swap] using htsReach.swap
    apply Subtype.ext
    exact chain_reaches_start_eq (P := P) (x := s.1) (s := t.1) t.2 hreach

/-- 两条实际链若到达同一个槽位，则它们的链起点相同。 -/
theorem chainStarts_eq_of_reaches_common
    {P : HPath k} (s t : {v : Vtx k // v ∈ chainStarts P}) {v : Vtx k}
    (hs : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) s.1 v)
    (ht : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) t.1 v) :
    s = t := by
  have hleft : Relator.RightUnique
      (Function.swap (fun a b => (a, b) ∈ chainGraph P)) := by
    intro a b c hba hca
    have hbIn : (b, a) ∈ intoV (chainGraph P) a := by
      rw [intoV, mem_into]
      exact ⟨hba, Finset.mem_singleton_self _⟩
    have hcIn : (c, a) ∈ intoV (chainGraph P) a := by
      rw [intoV, mem_into]
      exact ⟨hca, Finset.mem_singleton_self _⟩
    have heq := Finset.card_le_one.mp (chainGraph_into_le_one P a)
      (b, a) hbIn (c, a) hcIn
    exact congrArg Prod.fst heq
  rcases Relation.ReflTransGen.total_of_right_unique hleft
      hs.swap ht.swap with hst | hts
  · have hreach : Relation.ReflTransGen
        (fun a b => (a, b) ∈ chainGraph P) t.1 s.1 := by
      simpa only [Function.swap] using hst.swap
    apply Subtype.ext
    exact (chain_reaches_start_eq (P := P) (x := t.1) (s := s.1)
      s.2 hreach).symm
  · have hreach : Relation.ReflTransGen
        (fun a b => (a, b) ∈ chainGraph P) s.1 t.1 := by
      simpa only [Function.swap] using hts.swap
    apply Subtype.ext
    exact chain_reaches_start_eq (P := P) (x := s.1) (s := t.1)
      t.2 hreach

/-- 不同起点生成的实际链路线顶点集互不相交。 -/
theorem actualChainRoutes_disjoint
    {P : HPath k} {s t : {v : Vtx k // v ∈ chainStarts P}} (hst : s ≠ t) :
    Disjoint (actualChainRoute s).toFinset (actualChainRoute t).toFinset := by
  rw [Finset.disjoint_left]
  intro v hvs hvt
  apply hst
  apply chainStarts_eq_of_reaches_common s t
  · exact actualChainRoute_reaches_mem s (List.mem_toFinset.mp hvs)
  · exact actualChainRoute_reaches_mem t (List.mem_toFinset.mp hvt)

/-! ## 从终点逆向追踪以及起终点双射 -/

/-- 从实际链终点沿 `D_P` 的唯一前驱逆向追踪至多 `|S(P)|` 步。 -/
noncomputable def actualReverseChainRoute
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) : List (Vtx k) :=
  Hunter.ProofsPathrule.iterOpt
    (Hunter.ProofsPathrule.pred (chainGraph P)) (Sset P).card e.1

theorem actualReverseChainRoute_ne_nil
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    actualReverseChainRoute e ≠ [] :=
  Hunter.ProofsPathrule.iterOpt_ne_nil _ _ _

theorem actualReverseChainRoute_head
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    (actualReverseChainRoute e).head (actualReverseChainRoute_ne_nil e) = e.1 :=
  Hunter.ProofsPathrule.iterOpt_head_eq _ _ _

/-- 逆向路线的相邻点对按反方向对应 `D_P` 边。 -/
theorem actualReverseChainRoute_isChain
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    (actualReverseChainRoute e).IsChain
      (Function.swap fun a b => (a, b) ∈ chainGraph P) := by
  exact List.IsChain.imp
    (fun ⦃a b : Vtx k⦄
      (hab : Hunter.ProofsPathrule.pred (chainGraph P) a = some b) =>
        Hunter.ProofsPathrule.edge_of_pred_some hab)
    (Hunter.ProofsPathrule.iterOpt_chain
      (Hunter.ProofsPathrule.pred (chainGraph P)) (Sset P).card e.1)

theorem mem_Sset_of_mem_actualReverseChainRoute
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P})
    {v : Vtx k} (hv : v ∈ actualReverseChainRoute e) :
    v ∈ Sset P := by
  apply Hunter.ProofsPathrule.iterOpt_mem_closed
    (f := Hunter.ProofsPathrule.pred (chainGraph P))
    (C := Sset P) ?_ (Sset P).card e.1 (mem_chainEnds.mp e.2).1 v hv
  intro a b hab _ha
  exact (mem_chainGraph.mp
    (Hunter.ProofsPathrule.edge_of_pred_some hab)).1

/-- 在 `k ≥ 1` 时，从链终点逆向生成的路线无重复。 -/
theorem actualReverseChainRoute_nodup
    (hk : 1 ≤ k) {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    (actualReverseChainRoute e).Nodup := by
  apply nodup_of_chain_leftUnique_of_head_no_pred
    (actualReverseChainRoute_ne_nil e) (actualReverseChainRoute_isChain e)
  · intro a b c hca hcb
    have haOut : (c, a) ∈ outV (chainGraph P) c := by
      rw [outV, mem_out]
      exact ⟨hca, Finset.mem_singleton_self _⟩
    have hbOut : (c, b) ∈ outV (chainGraph P) c := by
      rw [outV, mem_out]
      exact ⟨hcb, Finset.mem_singleton_self _⟩
    have heq := Finset.card_le_one.mp (chainGraph_out_le_one hk P c)
      (c, a) haOut (c, b) hbOut
    exact congrArg Prod.snd heq
  · intro a ha
    have heHead := actualReverseChainRoute_head e
    have ha' : (e.1, a) ∈ chainGraph P := by simpa [heHead] using ha
    have haOut : (e.1, a) ∈ outV (chainGraph P) e.1 := by
      rw [outV, mem_out]
      exact ⟨ha', Finset.mem_singleton_self _⟩
    rw [(mem_chainEnds.mp e.2).2] at haOut
    exact Finset.notMem_empty _ haOut

theorem actualReverseChainRoute_length_le
    (hk : 1 ≤ k) {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    (actualReverseChainRoute e).length ≤ (Sset P).card := by
  rw [← List.toFinset_card_of_nodup (actualReverseChainRoute_nodup hk e)]
  apply Finset.card_le_card
  intro v hv
  exact mem_Sset_of_mem_actualReverseChainRoute e (List.mem_toFinset.mp hv)

theorem actualReverseChainRoute_last_pred_none
    (hk : 1 ≤ k) {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    ∀ z, (actualReverseChainRoute e).getLast? = some z →
      Hunter.ProofsPathrule.pred (chainGraph P) z = none := by
  rcases Hunter.ProofsPathrule.iterOpt_last_spec
      (Hunter.ProofsPathrule.pred (chainGraph P)) (Sset P).card e.1 with hlast | hfull
  · exact hlast
  · have hle := actualReverseChainRoute_length_le hk e
    change (Hunter.ProofsPathrule.iterOpt
      (Hunter.ProofsPathrule.pred (chainGraph P)) (Sset P).card e.1).length ≤
        (Sset P).card at hle
    omega

/-- 逆向路线抵达的实际链起点。 -/
noncomputable def actualReverseChainRouteStart
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) : Vtx k :=
  (actualReverseChainRoute e).getLast (actualReverseChainRoute_ne_nil e)

theorem actualReverseChainRouteStart_mem_route
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    actualReverseChainRouteStart e ∈ actualReverseChainRoute e :=
  List.getLast_mem (actualReverseChainRoute_ne_nil e)

theorem actualReverseChainRouteStart_mem_chainStarts
    (hk : 1 ≤ k) {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    actualReverseChainRouteStart e ∈ chainStarts P := by
  rw [mem_chainStarts]
  refine ⟨mem_Sset_of_mem_actualReverseChainRoute e
    (actualReverseChainRouteStart_mem_route e), ?_⟩
  rw [← Hunter.ProofsPathrule.pred_eq_none_iff]
  apply actualReverseChainRoute_last_pred_none hk e (actualReverseChainRouteStart e)
  exact List.getLast?_eq_getLast_of_ne_nil (actualReverseChainRoute_ne_nil e)

/-- 逆向路线反转后给出从所得起点到原终点的 `D_P` 可达性。 -/
theorem actualReverseChainRoute_reaches_end
    {P : HPath k} (e : {v : Vtx k // v ∈ chainEnds P}) :
    Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) (actualReverseChainRouteStart e) e.1 := by
  have hreach := List.relationReflTransGen_of_exists_isChain
    (actualReverseChainRoute e) (actualReverseChainRoute_isChain e)
    (actualReverseChainRoute_ne_nil e)
  have hrev : Relation.ReflTransGen
      (Function.swap fun a b => (a, b) ∈ chainGraph P)
      e.1 (actualReverseChainRouteStart e) := by
    simpa [actualReverseChainRouteStart, actualReverseChainRoute_head] using hreach
  simpa only [Function.swap] using hrev.swap

/-- 从零出度链终点出发的 `D_P` 可达关系只能是零步关系。 -/
theorem chain_end_reaches_eq
    {P : HPath k} {e y : Vtx k} (he : e ∈ chainEnds P)
    (h : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) e y) :
    y = e := by
  rcases h.cases_head with hey | ⟨c, hec, _hcy⟩
  · exact hey.symm
  · have hOut : (e, c) ∈ outV (chainGraph P) e := by
      rw [outV, mem_out]
      exact ⟨hec, Finset.mem_singleton_self _⟩
    rw [(mem_chainEnds.mp he).2] at hOut
    exact False.elim (Finset.notMem_empty _ hOut)

/-- 每个实际链终点都来自某条正向路线。 -/
theorem chainStartEnd_surjective
    (hk : 1 ≤ k) {P : HPath k} : Function.Surjective (@chainStartEnd k P) := by
  intro e
  let s : {v : Vtx k // v ∈ chainStarts P} :=
    ⟨actualReverseChainRouteStart e,
      actualReverseChainRouteStart_mem_chainStarts hk e⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  change actualChainRouteEnd s = e.1
  have htoE : Relation.ReflTransGen
      (fun a b => (a, b) ∈ chainGraph P) s.1 e.1 := by
    exact actualReverseChainRoute_reaches_end e
  have htoActual := actualChainRoute_reaches_end s
  have hright : Relator.RightUnique
      (fun a b => (a, b) ∈ chainGraph P) := by
    intro a b c hab hac
    have hbOut : (a, b) ∈ outV (chainGraph P) a := by
      rw [outV, mem_out]
      exact ⟨hab, Finset.mem_singleton_self _⟩
    have hcOut : (a, c) ∈ outV (chainGraph P) a := by
      rw [outV, mem_out]
      exact ⟨hac, Finset.mem_singleton_self _⟩
    have heq := Finset.card_le_one.mp (chainGraph_out_le_one hk P a)
      (a, b) hbOut (a, c) hcOut
    exact congrArg Prod.snd heq
  rcases Relation.ReflTransGen.total_of_right_unique hright htoE htoActual with h | h
  · exact chain_end_reaches_eq (P := P) (e := e.1)
      (y := actualChainRouteEnd s) e.2 h
  · exact (chain_end_reaches_eq (P := P) (e := actualChainRouteEnd s)
      (y := e.1) (actualChainRouteEnd_mem_chainEnds s) h).symm

/-- `k ≥ 1` 时的实际有限双射：链起点与链终点一一对应。 -/
noncomputable def chainStartEndEquiv
    (hk : 1 ≤ k) (P : HPath k) :
    {v : Vtx k // v ∈ chainStarts P} ≃ {v : Vtx k // v ∈ chainEnds P} :=
  Equiv.ofBijective chainStartEnd
    ⟨chainStartEnd_injective, chainStartEnd_surjective hk⟩

end PreimageChain

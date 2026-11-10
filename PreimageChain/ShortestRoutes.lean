import PreimageChain.ComponentMatching

/-!
# 预像槽位的最短路线成本

本模块按正文定义扩展自然数 `ℕ ∪ {∞}` 上的槽位路线距离。空可行集的下确界
为 `∞`；任何实际 `D_P` 链路线都给出相应距离的有限上界。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `S(P)` 中的非空槽位序列。 -/
structure SlotSequence (P : HPath k) where
  slots : List (Vtx k)
  ne : slots ≠ []
  mem_Sset : ∀ v ∈ slots, v ∈ Sset P

namespace SlotSequence

def first {P : HPath k} (q : SlotSequence P) : Vtx k :=
  q.slots.head q.ne

def last {P : HPath k} (q : SlotSequence P) : Vtx k :=
  q.slots.getLast q.ne

theorem first_mem {P : HPath k} (q : SlotSequence P) : q.first ∈ q.slots :=
  List.head_mem q.ne

theorem last_mem {P : HPath k} (q : SlotSequence P) : q.last ∈ q.slots :=
  List.getLast_mem q.ne

theorem first_mem_Sset {P : HPath k} (q : SlotSequence P) : q.first ∈ Sset P :=
  q.mem_Sset q.first q.first_mem

theorem last_mem_Sset {P : HPath k} (q : SlotSequence P) : q.last ∈ Sset P :=
  q.mem_Sset q.last q.last_mem

end SlotSequence

/-- 槽位序列的内部成本 `Σ [w(vᵢ,σvᵢ₊₁)-1]`。 -/
noncomputable def slotInternalCost
    {P : HPath k} (q : SlotSequence P) : ℕ :=
  ((q.slots.zip q.slots.tail).map
    (fun d => ew k d.1 (sigma d.2) - 1)).sum

/-- 从组件 `B` 的头进入槽位序列并沿序列行走的成本。 -/
noncomputable def slotRouteStarCost
    {P : HPath k} (hP : P.IsHamiltonian)
    (B : ActualComponent P) (q : SlotSequence P) : ℕ :=
  ew k (actualComponentHead hP B) (sigma q.first) - 2 +
    slotInternalCost q

/-- 从组件 `B` 经槽位序列进入组件 `A` 的完整成本。 -/
noncomputable def slotRouteCost
    {P : HPath k} (hP : P.IsHamiltonian)
    (B A : ActualComponent P) (q : SlotSequence P) : ℕ :=
  slotRouteStarCost hP B q +
    (ew k q.last (actualComponentTail hP A) - compMinto (F P) A.1)

/-- 正文的终端距离 `d_X(B,⋆)`；若没有槽位序列则为 `∞`。 -/
noncomputable def slotDistanceStar
    {P : HPath k} (hP : P.IsHamiltonian) (B : ActualComponent P) : WithTop ℕ :=
  sInf {d : WithTop ℕ |
    ∃ q : SlotSequence P, (slotRouteStarCost hP B q : WithTop ℕ) = d}

/-- 正文的组件距离 `d_X(B,A)`；末槽必须位于 `A` 外部。 -/
noncomputable def slotDistance
    {P : HPath k} (hP : P.IsHamiltonian)
    (B A : ActualComponent P) : WithTop ℕ :=
  sInf {d : WithTop ℕ |
    ∃ q : SlotSequence P, q.last ∉ A.1 ∧
      (slotRouteCost hP B A q : WithTop ℕ) = d}

theorem slotDistanceStar_le_route
    {P : HPath k} (hP : P.IsHamiltonian)
    (B : ActualComponent P) (q : SlotSequence P) :
    slotDistanceStar hP B ≤ (slotRouteStarCost hP B q : WithTop ℕ) := by
  apply sInf_le
  exact ⟨q, rfl⟩

theorem slotDistance_le_route
    {P : HPath k} (hP : P.IsHamiltonian)
    (B A : ActualComponent P) (q : SlotSequence P) (hlast : q.last ∉ A.1) :
    slotDistance hP B A ≤ (slotRouteCost hP B A q : WithTop ℕ) := by
  apply sInf_le
  exact ⟨q, hlast, rfl⟩

/-- 一条实际 `D_P` 链路线视为非空槽位序列。 -/
noncomputable def actualChainSlotSequence
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) : SlotSequence P where
  slots := actualChainRoute s
  ne := actualChainRoute_ne_nil s
  mem_Sset := fun v hv => mem_Sset_of_mem_actualChainRoute s hv

theorem actualChainSlotSequence_first
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainSlotSequence s).first = s.1 :=
  actualChainRoute_head s

theorem actualChainSlotSequence_last
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainSlotSequence s).last = actualChainRouteEnd s := by
  rfl

/-- 一个非终端链终点所进入的实际目标组件。 -/
noncomputable def actualNonterminalTargetComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) : ActualComponent P := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  exact ⟨Hunter.ProofsWP.block (F P) (chainTargetTail hP e).1,
    Hunter.ProofsWP.block_mem_comps
      (hV ▸ Finset.mem_univ (chainTargetTail hP e).1)⟩

theorem actualNonterminalTargetComponent_tail
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    actualComponentTail hP (actualNonterminalTargetComponent hP hk e) =
      (chainTargetTail hP e).1 := by
  let t := (chainTargetTail hP e).1
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have htV : t ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have htTail : t ∈ tails (F P) :=
    (Finset.mem_sdiff.mp (chainTargetTail hP e).2).1
  have hm : t ∈ compTails (F P)
      (actualNonterminalTargetComponent hP hk e).1 := by
    rw [compTails, Finset.mem_filter]
    refine ⟨Hunter.ProofsWP.self_mem_block htV, ?_⟩
    exact (Finset.mem_filter.mp htTail).2
  rw [actualComponentTail_spec hP, Finset.mem_singleton] at hm
  exact hm.symm

/-- 非终端出口的源槽位位于其目标组件之外。 -/
theorem nonterminalChainEnd_not_mem_targetComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    e.1 ∉ (actualNonterminalTargetComponent hP hk e).1 := by
  let t := (chainTargetTail hP e).1
  have htail : t ∈ tails (F P) :=
    (Finset.mem_sdiff.mp (chainTargetTail hP e).2).1
  have hedgeE1 := chainTargetTail_spec hP e
  have hedge : (e.1, t) ∈ P.edges :=
    E1removed_subset P (Sset P) hedgeE1
  obtain ⟨p, hpv, hpfirst, hpc, hmin⟩ :=
    Hunter.ProofsWP.tail_data hP hk (Hunter.lem_pathrule hP) htail
  intro heMem
  have hle : P.pos t ≤ P.pos e.1 := hmin e.1 heMem
  have hlt : P.pos e.1 < P.pos t := by
    rw [Hunter.ProofsStructure.edge_pos_succ hedge]
    omega
  omega

/-- 每条实际链给出其源组件到 `⋆` 的有限候选路线。 -/
theorem slotDistanceStar_actual_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    slotDistanceStar hP (actualChainSourceComponent hP hk s) ≤
      (slotRouteStarCost hP (actualChainSourceComponent hP hk s)
        (actualChainSlotSequence s) : WithTop ℕ) :=
  slotDistanceStar_le_route hP _ _

/-- 每条非终端实际链给出其源组件到真实目标组件的有限候选路线。 -/
theorem slotDistance_actual_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hsEnd : actualChainRouteEnd s ≠ P.last) :
    let e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩
    slotDistance hP (actualChainSourceComponent hP hk s)
        (actualNonterminalTargetComponent hP hk e) ≤
      (slotRouteCost hP (actualChainSourceComponent hP hk s)
        (actualNonterminalTargetComponent hP hk e)
        (actualChainSlotSequence s) : WithTop ℕ) := by
  dsimp
  apply slotDistance_le_route
  rw [actualChainSlotSequence_last]
  exact nonterminalChainEnd_not_mem_targetComponent hP hk _

end PreimageChain

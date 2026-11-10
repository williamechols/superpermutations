import PreimageChain.ShortestRoutes

/-!
# 最短路线成本与真实链成本的桥接

本模块证明正文的自然数槽位路线成本在嵌入 `ℤ` 后，逐项等于此前由真实
`E₁/E₂` 边定义的链成本。因此最短路线不等式可以安全求和并接到
`actualPreimageSurplus`。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

theorem nodup_zip_of_left
    {α β : Type*} {l : List α} {m : List β} (hl : l.Nodup) :
    (l.zip m).Nodup := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
      cases m with
      | nil => simp
      | cons b m =>
          rw [List.zip_cons_cons, List.nodup_cons] at ⊢
          rw [List.nodup_cons] at hl
          refine ⟨?_, ih hl.2⟩
          intro hab
          exact hl.1 (List.of_mem_zip hab).1

theorem finset_sum_toFinset_eq_list_sum_map
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {l : List α} (hl : l.Nodup) (f : α → M) :
    (∑ x ∈ l.toFinset, f x) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hl
      rw [List.toFinset_cons, Finset.sum_insert]
      · rw [List.map_cons, List.sum_cons, ih hl.2]
      · exact fun ha => hl.1 (List.mem_toFinset.mp ha)

theorem cast_finset_sum_nat_sub_one
    {α : Type*} [DecidableEq α] (S : Finset α) (w : α → ℕ)
    (h : ∀ x ∈ S, 1 ≤ w x) :
    ((S.sum (fun x => w x - 1) : ℕ) : ℤ) =
      S.sum (fun x => (w x : ℤ) - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have haW : 1 ≤ w a := h a (Finset.mem_insert_self _ _)
      have hS : ∀ x ∈ S, 1 ≤ w x := by
        intro x hx
        exact h x (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Nat.cast_add, Nat.cast_sub haW, ih hS]
      norm_num

theorem slotInternalCost_actual_eq
    {P : HPath k} (s : {v : Vtx k // v ∈ chainStarts P}) :
    slotInternalCost (actualChainSlotSequence s) =
      ∑ d ∈ actualChainRouteEdges s, (ew k d.1 (sigma d.2) - 1) := by
  unfold slotInternalCost actualChainRouteEdges actualChainSlotSequence
  change (((actualChainRoute s).zip (actualChainRoute s).tail).map
      (fun d => ew k d.1 (sigma d.2) - 1)).sum = _
  have h := finset_sum_toFinset_eq_list_sum_map
    (nodup_zip_of_left (m := (actualChainRoute s).tail)
      (actualChainRoute_nodup s))
    (fun d : Vtx k × Vtx k => ew k d.1 (sigma d.2) - 1)
  exact h.symm

theorem cast_actual_internal_cost
    {P : HPath k} (hk : 1 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (slotInternalCost (actualChainSlotSequence s) : ℤ) =
      ∑ d ∈ actualChainRouteEdges s,
        ((ew k d.1 (sigma d.2) : ℤ) - 1) := by
  rw [slotInternalCost_actual_eq]
  apply cast_finset_sum_nat_sub_one
  intro d hd
  exact_mod_cast (sub_nonneg.mp (chainInternal_excess_nonneg hk
    (actualChainRouteEdges_subset s hd)))

theorem cast_slotRouteStarCost_actual
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (slotRouteStarCost hP (actualChainSourceComponent hP hk s)
        (actualChainSlotSequence s) : ℤ) =
      actualChainRouteCoreCost hP s := by
  unfold slotRouteStarCost actualChainRouteCoreCost
  have hentry : 2 ≤ ew k (chainSourceHead hP s).1 (sigma s.1) := by
    exact_mod_cast (sub_nonneg.mp (chainEntry_excess_nonneg hP hk s))
  rw [actualChainSourceComponent_head hP hk s,
    actualChainSlotSequence_first, Nat.cast_add,
    Nat.cast_sub hentry, cast_actual_internal_cost (by omega) s]
  norm_num

/-- 一条实际链的正文自然数成本；终端链省略出口项。 -/
noncomputable def actualChainRouteNatCost
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ℕ :=
  if hs : actualChainRouteEnd s = P.last then
    slotRouteStarCost hP (actualChainSourceComponent hP hk s)
      (actualChainSlotSequence s)
  else
    let e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩
    slotRouteCost hP (actualChainSourceComponent hP hk s)
      (actualNonterminalTargetComponent hP hk e) (actualChainSlotSequence s)

theorem cast_slotRouteCost_actual_nonterminal
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) :
    let e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩
    (slotRouteCost hP (actualChainSourceComponent hP hk s)
        (actualNonterminalTargetComponent hP hk e)
        (actualChainSlotSequence s) : ℤ) =
      actualChainRouteCost hP s := by
  dsimp
  unfold slotRouteCost actualChainRouteCost
  have hexit := chainExit_excess_nonneg hP hk
    (⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ :
      {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last})
  have hExitNat : compMinto (F P)
      (Hunter.ProofsWP.block (F P)
        (chainTargetTail hP
          (⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ :
            {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last})).1) ≤
      ew k (actualChainRouteEnd s)
        (chainTargetTail hP
          (⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ :
            {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last})).1 := by
    exact_mod_cast (sub_nonneg.mp hexit)
  rw [Nat.cast_add, cast_slotRouteStarCost_actual hP hk s,
    actualChainSlotSequence_last,
    actualNonterminalTargetComponent_tail hP hk]
  rw [show (actualNonterminalTargetComponent hP hk
      (⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ :
        {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last})).1 =
      Hunter.ProofsWP.block (F P)
        (chainTargetTail hP
          (⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ :
            {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last})).1 from rfl]
  rw [Nat.cast_sub hExitNat]
  unfold actualChainEndExitCost
  have hs' : (chainStartEnd s).1 ≠ P.last := hs
  rw [dif_neg hs']
  rfl

theorem cast_actualChainRouteNatCost
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainRouteNatCost hP hk s : ℤ) = actualChainRouteCost hP s := by
  unfold actualChainRouteNatCost
  by_cases hs : actualChainRouteEnd s = P.last
  · rw [dif_pos hs, cast_slotRouteStarCost_actual hP hk s]
    unfold actualChainRouteCost actualChainEndExitCost
    have hs' : (chainStartEnd s).1 = P.last := hs
    rw [dif_pos hs', add_zero]
  · rw [dif_neg hs]
    exact cast_slotRouteCost_actual_nonterminal hP hk s hs

theorem actualChainRouteCost_nonneg
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    0 ≤ actualChainRouteCost hP s := by
  rw [← cast_actualChainRouteNatCost hP hk s]
  exact Int.natCast_nonneg _

theorem cast_actualChainAssignmentNatCost
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ((∑ s : {v : Vtx k // v ∈ chainStarts P},
      actualChainRouteNatCost hP hk s : ℕ) : ℤ) =
      actualChainAssignmentSurplus hP := by
  unfold actualChainAssignmentSurplus
  push_cast
  apply Finset.sum_congr rfl
  intro s _hs
  exact cast_actualChainRouteNatCost hP hk s

/-- 真实链自然数总成本的整数嵌入仍由真实总剩余成本支配。 -/
theorem cast_actualChainAssignmentNatCost_le_surplus
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ((∑ s : {v : Vtx k // v ∈ chainStarts P},
      actualChainRouteNatCost hP hk s : ℕ) : ℤ) ≤
      actualPreimageSurplus hP := by
  rw [cast_actualChainAssignmentNatCost hP hk]
  exact actualChainAssignmentSurplus_le_actualPreimageSurplus hP hk

end PreimageChain

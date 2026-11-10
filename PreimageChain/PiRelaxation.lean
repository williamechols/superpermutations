import PreimageChain.ShortestRouteBridge

/-!
# 组件指派松弛 `Π`

本模块按正文定义 `Π₀`、`Π₁`：分别在候选根、候选末组件及组件双射上取
扩展自然数中的下确界。随后把真实预像链匹配嵌入候选集合，为最终逐路径
加强提供可行解。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `F(P)` 的组件最小进入权重最大值。 -/
noncomputable def actualComponentMuMax (P : HPath k) : ℕ :=
  (Comps (F P)).sup (compMinto (F P))

/-- 无终端链情形的一组候选根、候选末组件和组件指派。 -/
structure PiZeroChoice (P : HPath k) where
  root : ActualComponent P
  last : ActualComponent P
  assign : {B : ActualComponent P // B ≠ last} ≃
    {A : ActualComponent P // A ≠ root}

/-- 有唯一终端链情形的一组候选根和含终端符号的组件指派。 -/
structure PiOneChoice (P : HPath k) where
  root : ActualComponent P
  assign : ActualComponent P ≃
    Sum {A : ActualComponent P // A ≠ root} Unit

/-- `Π₀` 中一个候选指派的目标值。 -/
noncomputable def piZeroObjective
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiZeroChoice P) : WithTop ℕ :=
  (actualComponentMuMax P - compMinto (F P) Q.root.1 : ℕ) +
    ∑ B : {B : ActualComponent P // B ≠ Q.last},
      slotDistance hP B.1 (Q.assign B).1

/-- `Π₁` 中一条组件指派边的距离；终端符号使用 `d_X(B,⋆)`。 -/
noncomputable def piOneAssignmentCost
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiOneChoice P)
    (B : ActualComponent P) : WithTop ℕ :=
  match Q.assign B with
  | Sum.inl A => slotDistance hP B A.1
  | Sum.inr _ => slotDistanceStar hP B

/-- `Π₁` 中一个候选指派的目标值，包含终端指示项一。 -/
noncomputable def piOneObjective
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiOneChoice P) : WithTop ℕ :=
  1 + (actualComponentMuMax P - compMinto (F P) Q.root.1 : ℕ) +
    ∑ B : ActualComponent P, piOneAssignmentCost hP Q B

/-- 正文的 `Π₀(F(P))`。 -/
noncomputable def preimagePiZero
    {P : HPath k} (hP : P.IsHamiltonian) : WithTop ℕ :=
  sInf {d : WithTop ℕ | ∃ Q : PiZeroChoice P, piZeroObjective hP Q = d}

/-- 正文的 `Π₁(F(P))`。 -/
noncomputable def preimagePiOne
    {P : HPath k} (hP : P.IsHamiltonian) : WithTop ℕ :=
  sInf {d : WithTop ℕ | ∃ Q : PiOneChoice P, piOneObjective hP Q = d}

/-- 正文的组件指派松弛 `Π(F(P)) = min(Π₀,Π₁)`。 -/
noncomputable def preimagePi
    {P : HPath k} (hP : P.IsHamiltonian) : WithTop ℕ :=
  min (preimagePiZero hP) (preimagePiOne hP)

theorem preimagePiZero_le_choice
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiZeroChoice P) :
    preimagePiZero hP ≤ piZeroObjective hP Q := by
  apply sInf_le
  exact ⟨Q, rfl⟩

theorem preimagePiOne_le_choice
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiOneChoice P) :
    preimagePiOne hP ≤ piOneObjective hP Q := by
  apply sInf_le
  exact ⟨Q, rfl⟩

theorem preimagePi_le_zero_choice
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiZeroChoice P) :
    preimagePi hP ≤ piZeroObjective hP Q := by
  exact (min_le_left _ _).trans (preimagePiZero_le_choice hP Q)

theorem preimagePi_le_one_choice
    {P : HPath k} (hP : P.IsHamiltonian) (Q : PiOneChoice P) :
    preimagePi hP ≤ piOneObjective hP Q := by
  exact (min_le_right _ _).trans (preimagePiOne_le_choice hP Q)

/-- 无终端真实链匹配给出的 `Π₀` 可行候选。 -/
noncomputable def actualPiZeroChoice
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) : PiZeroChoice P :=
  let M := actualChainMatchingZero hP hk hlast
  { root := M.root
    last := M.last
    assign := M.source.symm.trans M.target }

/-- 有终端真实链匹配给出的 `Π₁` 可行候选。 -/
noncomputable def actualPiOneChoice
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) : PiOneChoice P :=
  let M := actualChainMatchingOne hP hk hlast
  { root := M.root
    assign := M.source.symm.trans M.target }

theorem chainEnd_ne_last_of_last_mem_heads
    {P : HPath k} (hP : P.IsHamiltonian)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    actualChainRouteEnd s ≠ P.last := by
  intro heq
  have hEnd : P.last ∈ chainEnds P :=
    heq ▸ actualChainRouteEnd_mem_chainEnds s
  have hSlot := (last_mem_chainEnds_iff hP).mp hEnd
  exact ((last_mem_Sset_iff_not_mem_heads hP).mp hSlot) hlast

@[simp] theorem actualPiZeroChoice_root
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    (actualPiZeroChoice hP hk hlast).root = actualRootComponent hP hk := rfl

@[simp] theorem actualPiZeroChoice_last
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    (actualPiZeroChoice hP hk hlast).last = actualLastComponent hP hk := rfl

@[simp] theorem actualPiOneChoice_root
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    (actualPiOneChoice hP hk hlast).root = actualRootComponent hP hk := rfl

theorem actualPiZeroChoice_assign_source
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualPiZeroChoice hP hk hlast).assign
        ((actualChainMatchingZero hP hk hlast).source s) =
      (actualChainMatchingZero hP hk hlast).target s := by
  change (actualChainMatchingZero hP hk hlast).target
      ((actualChainMatchingZero hP hk hlast).source.symm
        ((actualChainMatchingZero hP hk hlast).source s)) = _
  rw [(actualChainMatchingZero hP hk hlast).source.symm_apply_apply]

theorem actualPiOneChoice_assign_source
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualPiOneChoice hP hk hlast).assign
        ((actualChainMatchingOne hP hk hlast).source s) =
      (actualChainMatchingOne hP hk hlast).target s := by
  change (actualChainMatchingOne hP hk hlast).target
      ((actualChainMatchingOne hP hk hlast).source.symm
        ((actualChainMatchingOne hP hk hlast).source s)) = _
  rw [(actualChainMatchingOne hP hk hlast).source.symm_apply_apply]

theorem actualChainMatchingZero_source_val
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    ((actualChainMatchingZero hP hk hlast).source s).1 =
      actualChainSourceComponent hP hk s := rfl

theorem actualChainMatchingOne_source
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    (actualChainMatchingOne hP hk hlast).source s =
      actualChainSourceComponent hP hk s := rfl

theorem actualChainMatchingZero_target_val
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    ((actualChainMatchingZero hP hk hlast).target s).1 =
      actualNonterminalTargetComponent hP hk
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s,
          chainEnd_ne_last_of_last_mem_heads hP hlast s⟩ := rfl

/-- 有终端情形下一条非终端真实链的靶组件，带非根证明。 -/
noncomputable def actualOneNonterminalTarget
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) :
    {A : ActualComponent P // A ≠ actualRootComponent hP hk} :=
  ((chainTargetComponentEquiv hP hk).trans
    (nonRootComponentNeEquiv hP hk))
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩

theorem actualOneNonterminalTarget_val
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) :
    (actualOneNonterminalTarget hP hk s hs).1 =
      actualNonterminalTargetComponent hP hk
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩ := rfl

theorem actualChainMatchingOne_target_terminal
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s = P.last) :
    (actualChainMatchingOne hP hk hlast).target s = Sum.inr () := by
  unfold actualChainMatchingOne
  simp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ (Equiv.refl Unit))
      ((chainEndsTerminalEquiv hP hlast)
        (chainStartEnd s)) = Sum.inr ()
  simp [chainEndsTerminalEquiv, chainStartEnd, hs]

theorem actualChainMatchingOne_target_nonterminal
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) :
    (actualChainMatchingOne hP hk hlast).target s =
      Sum.inl (actualOneNonterminalTarget hP hk s hs) := by
  unfold actualChainMatchingOne
  simp only [Equiv.trans_apply]
  change (Equiv.sumCongr _ (Equiv.refl Unit))
      ((chainEndsTerminalEquiv hP hlast)
        (chainStartEnd s)) = Sum.inl _
  simp [chainEndsTerminalEquiv, chainStartEnd, hs,
    actualOneNonterminalTarget]

/-- `Π₀` 的真实组件指派距离和由逐链自然数成本支配。 -/
theorem actualPiZero_distanceSum_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    (∑ B : {B : ActualComponent P //
        B ≠ (actualChainMatchingZero hP hk hlast).last},
      slotDistance hP B.1
        (((actualChainMatchingZero hP hk hlast).source.symm.trans
          (actualChainMatchingZero hP hk hlast).target) B).1) ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        (actualChainRouteNatCost hP hk s : WithTop ℕ) := by
  have hreindex :=
    (actualChainMatchingZero hP hk hlast).source.sum_comp
      (fun B => slotDistance hP B.1
        (((actualChainMatchingZero hP hk hlast).source.symm.trans
          (actualChainMatchingZero hP hk hlast).target) B).1)
  rw [← hreindex]
  apply Finset.sum_le_sum
  intro s _hs
  have hsEnd := chainEnd_ne_last_of_last_mem_heads hP hlast s
  rw [Equiv.trans_apply,
    (actualChainMatchingZero hP hk hlast).source.symm_apply_apply,
    actualChainMatchingZero_source_val hP hk hlast s,
    actualChainMatchingZero_target_val hP hk hlast s]
  simpa [actualChainRouteNatCost, hsEnd] using
    (slotDistance_actual_le hP hk s hsEnd)

/-- `Π₁` 真实指派中每条链的距离项由该链自然数成本支配。 -/
theorem actualPiOne_assignmentCost_source_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P))
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    piOneAssignmentCost hP (actualPiOneChoice hP hk hlast)
        ((actualChainMatchingOne hP hk hlast).source s) ≤
      (actualChainRouteNatCost hP hk s : WithTop ℕ) := by
  unfold piOneAssignmentCost
  rw [actualPiOneChoice_assign_source hP hk hlast s]
  by_cases hsEnd : actualChainRouteEnd s = P.last
  · rw [actualChainMatchingOne_target_terminal hP hk hlast s hsEnd]
    rw [actualChainMatchingOne_source hP hk hlast s]
    simpa [actualChainRouteNatCost, hsEnd] using
      (slotDistanceStar_actual_le hP hk s)
  · rw [actualChainMatchingOne_target_nonterminal hP hk hlast s hsEnd]
    simp only
    rw [actualChainMatchingOne_source hP hk hlast s,
      actualOneNonterminalTarget_val hP hk s hsEnd]
    simpa [actualChainRouteNatCost, hsEnd] using
      (slotDistance_actual_le hP hk s hsEnd)

/-- `Π₁` 的真实组件指派距离和由逐链自然数成本支配。 -/
theorem actualPiOne_distanceSum_le
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    (∑ B : ActualComponent P,
      piOneAssignmentCost hP (actualPiOneChoice hP hk hlast) B) ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        (actualChainRouteNatCost hP hk s : WithTop ℕ) := by
  have hreindex :=
    (actualChainMatchingOne hP hk hlast).source.sum_comp
      (piOneAssignmentCost hP (actualPiOneChoice hP hk hlast))
  rw [← hreindex]
  exact Finset.sum_le_sum fun s _hs =>
    actualPiOne_assignmentCost_source_le hP hk hlast s

/-- 无终端情形下，`Π` 由真实指派的根差与链成本支配。 -/
theorem preimagePi_le_actual_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∈ heads (F P)) :
    preimagePi hP ≤
      (actualComponentMuMax P -
          compMinto (F P) (actualRootComponent hP hk).1 : ℕ) +
        ∑ s : {v : Vtx k // v ∈ chainStarts P},
          (actualChainRouteNatCost hP hk s : WithTop ℕ) := by
  refine (preimagePi_le_zero_choice hP
    (actualPiZeroChoice hP hk hlast)).trans ?_
  unfold piZeroObjective
  change
    (actualComponentMuMax P -
          compMinto (F P) (actualRootComponent hP hk).1 : ℕ) +
        (∑ B : {B : ActualComponent P //
            B ≠ (actualChainMatchingZero hP hk hlast).last},
          slotDistance hP B.1
            (((actualChainMatchingZero hP hk hlast).source.symm.trans
              (actualChainMatchingZero hP hk hlast).target) B).1) ≤ _
  exact add_le_add le_rfl (actualPiZero_distanceSum_le hP hk hlast)

/-- 有终端情形下，`Π` 由指示项一、真实根差与链成本支配。 -/
theorem preimagePi_le_actual_one
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    preimagePi hP ≤
      1 + (actualComponentMuMax P -
          compMinto (F P) (actualRootComponent hP hk).1 : ℕ) +
        ∑ s : {v : Vtx k // v ∈ chainStarts P},
          (actualChainRouteNatCost hP hk s : WithTop ℕ) := by
  refine (preimagePi_le_one_choice hP
    (actualPiOneChoice hP hk hlast)).trans ?_
  unfold piOneObjective
  rw [actualPiOneChoice_root]
  exact add_le_add le_rfl (actualPiOne_distanceSum_le hP hk hlast)

/-- 真实链给出的有限 `Π` 预算。 -/
noncomputable def actualPiBudget
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  actualComponentMuMax P -
      compMinto (F P) (actualRootComponent hP hk).1 +
    indicatorI P (Sset P) +
    ∑ s : {v : Vtx k // v ∈ chainStarts P},
      actualChainRouteNatCost hP hk s

/-- 两种终端情形合并后，`Π` 始终不超过真实有限预算。 -/
theorem preimagePi_le_actualPiBudget
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    preimagePi hP ≤ (actualPiBudget hP hk : WithTop ℕ) := by
  unfold actualPiBudget
  by_cases hlast : P.last ∈ heads (F P)
  · have h := preimagePi_le_actual_zero hP hk hlast
    rw [Hunter.ProofsWP.indicatorI_eq_ite hP]
    rw [if_pos hlast]
    simpa [actualPiBudget, Nat.cast_add, Nat.cast_sum, add_assoc] using h
  · have h := preimagePi_le_actual_one hP hk hlast
    rw [Hunter.ProofsWP.indicatorI_eq_ite hP]
    rw [if_neg hlast]
    simpa [actualPiBudget, Nat.cast_add, Nat.cast_sum,
      add_assoc, add_comm, add_left_comm] using h

theorem preimagePi_ne_top
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    preimagePi hP ≠ ⊤ := by
  intro htop
  have h := preimagePi_le_actualPiBudget hP hk
  rw [htop] at h
  exact WithTop.not_top_le_coe (actualPiBudget hP hk) h

/-- `Π(F(P))` 的自然数值；有限性由真实链候选证明，而不是作为假设加入。 -/
noncomputable def preimagePiNat
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  (preimagePi hP).untop (preimagePi_ne_top hP hk)

@[simp] theorem coe_preimagePiNat
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (preimagePiNat hP hk : WithTop ℕ) = preimagePi hP :=
  WithTop.coe_untop _ _

theorem preimagePiNat_le_actualPiBudget
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    preimagePiNat hP hk ≤ actualPiBudget hP hk := by
  apply WithTop.coe_le_coe.mp
  change (preimagePiNat hP hk : WithTop ℕ) ≤
    (actualPiBudget hP hk : WithTop ℕ)
  rw [coe_preimagePiNat]
  exact preimagePi_le_actualPiBudget hP hk

/-- 根组件的 `μ` 不超过全部组件上的最大 `μ`。 -/
theorem actualRootMu_le_componentMuMax
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    compMinto (F P) (actualRootComponent hP hk).1 ≤ actualComponentMuMax P := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hroot : (actualRootComponent hP hk).1 ∈ Comps (F P) :=
    (actualRootComponent hP hk).2
  exact Finset.le_sup hroot

/-- 自然数 `Π` 嵌入整数后，由公式 (10) 中的根差、指示项和真实剩余成本支配。 -/
theorem cast_preimagePiNat_le_identity_correction
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (preimagePiNat hP hk : ℤ) ≤
      (actualComponentMuMax P : ℤ) -
        (compMinto (F P) (actualRootComponent hP hk).1 : ℤ) +
      (indicatorI P (Sset P) : ℤ) + actualPreimageSurplus hP := by
  have hPiNat := preimagePiNat_le_actualPiBudget hP hk
  have hPi : (preimagePiNat hP hk : ℤ) ≤ (actualPiBudget hP hk : ℤ) := by
    exact_mod_cast hPiNat
  have hroot := actualRootMu_le_componentMuMax hP hk
  have hchains := cast_actualChainAssignmentNatCost_le_surplus hP hk
  unfold actualPiBudget at hPi
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hroot] at hPi
  linarith

/-- 正文推论：实际 Hunter 基线加 `Π(F(P))` 不超过原 Hamilton 路径权重。 -/
theorem actual_component_preimagePi_strengthening
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) +
        (wEdges (F P) : ℤ) + (preimagePiNat hP hk : ℤ) ≤
      (P.wtP : ℤ) := by
  have hid := actual_preimage_chain_identity_components hP hk
  have hPi := cast_preimagePiNat_le_identity_correction hP hk
  unfold actualComponentMuMax at hPi
  change (preimagePiNat hP hk : ℤ) ≤
      (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) -
        (compMinto (F P)
          (Hunter.ProofsWP.block (F P) P.first) : ℤ) +
      (indicatorI P (Sset P) : ℤ) + actualPreimageSurplus hP at hPi
  linarith

/-- 同一加强的自然数版本，直接对应正文中的 `B₁(F(P))+Π(F(P))≤wt(P)`。 -/
theorem actual_component_preimagePi_strengthening_nat
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) +
        preimagePiNat hP hk ≤ P.wtP := by
  have h := actual_component_preimagePi_strengthening hP hk
  have hc : 1 ≤ numComps (F P) :=
    Hunter.ProofsWP.one_le_numComps_F hP hk
  have hcast :
      ((((numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) +
        preimagePiNat hP hk : ℕ)) : ℤ) =
        (numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) +
          (wEdges (F P) : ℤ) + (preimagePiNat hP hk : ℤ) := by
    push_cast [hc]
    ring
  rw [← hcast] at h
  exact_mod_cast h

end PreimageChain

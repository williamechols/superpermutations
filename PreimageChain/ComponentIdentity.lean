import PreimageChain.EdgePartition

/-!
# 预像链恒等式的组件级闭合

本模块把非终端链出口经唯一组件尾重索引到 `F(P)` 的非根组件，并将真实
边级剩余成本等式与 `MinThrough = Σ μ - μ_max` 接合。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- `F(P)` 中除包含 `P.first` 的根组件外的实际组件类型。 -/
noncomputable abbrev NonRootComponent (P : HPath k) :=
  ↑(Comps (F P) \ {Hunter.ProofsWP.block (F P) P.first})

/-- 同一 `F(P)` 组件中的两个尾必相同。 -/
theorem tails_eq_of_same_block
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    {a b : Vtx k} (ha : a ∈ tails (F P)) (hb : b ∈ tails (F P))
    (hab : Hunter.ProofsWP.block (F P) a = Hunter.ProofsWP.block (F P) b) :
    a = b := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hav : a ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have hbv : b ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  obtain ⟨t, htsingle⟩ := Hunter.ProofsWP.compTails_F_single
    (Hunter.lem_pathrule hP) (Hunter.ProofsWP.block_mem_comps hav)
  have hain : a ∈ compTails (F P) (Hunter.ProofsWP.block (F P) a) := by
    rw [compTails, Finset.mem_filter]
    exact ⟨Hunter.ProofsWP.self_mem_block hav, (Finset.mem_filter.mp ha).2⟩
  have hbin : b ∈ compTails (F P) (Hunter.ProofsWP.block (F P) a) := by
    rw [compTails, Finset.mem_filter]
    refine ⟨?_, (Finset.mem_filter.mp hb).2⟩
    rw [hab]
    exact Hunter.ProofsWP.self_mem_block hbv
  rw [htsingle, Finset.mem_singleton] at hain hbin
  exact hain.trans hbin.symm

/-- 一个非根组件尾映到它所属的非根组件。 -/
noncomputable def nonRootTailComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (a : {a : Vtx k // a ∈ tails (F P) \ tails P.edges}) :
    NonRootComponent P := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have haTail : a.1 ∈ tails (F P) := (Finset.mem_sdiff.mp a.2).1
  have haV : a.1 ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have hfirstTail : P.first ∈ tails (F P) :=
    Hunter.ProofsWP.first_mem_tails hP hk (Hunter.lem_pathrule hP)
  have haNeFirst : a.1 ≠ P.first := by
    intro heq
    have haNotTailP := (Finset.mem_sdiff.mp a.2).2
    have hfirstMem : P.first ∈ tails P.edges := by
      rw [Hunter.ProofsWP.tails_edges_ham hP, Finset.mem_singleton]
    exact haNotTailP (heq.symm ▸ hfirstMem)
  refine ⟨Hunter.ProofsWP.block (F P) a.1, Finset.mem_sdiff.mpr ⟨
    Hunter.ProofsWP.block_mem_comps haV, ?_⟩⟩
  rw [Finset.mem_singleton]
  intro hroot
  exact haNeFirst (tails_eq_of_same_block hP hk haTail hfirstTail hroot)

/-- 非根组件尾到非根组件的映射是单射。 -/
theorem nonRootTailComponent_injective
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Injective (nonRootTailComponent hP hk) := by
  intro a b hab
  apply Subtype.ext
  have hblocks := congrArg Subtype.val hab
  exact tails_eq_of_same_block hP hk
    (Finset.mem_sdiff.mp a.2).1 (Finset.mem_sdiff.mp b.2).1 hblocks

/-- 每个非根组件都有一个唯一组件尾，因而来自非根尾映射。 -/
theorem nonRootTailComponent_surjective
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Surjective (nonRootTailComponent hP hk) := by
  intro C
  have hC : C.1 ∈ Comps (F P) := (Finset.mem_sdiff.mp C.2).1
  have hCne : C.1 ≠ Hunter.ProofsWP.block (F P) P.first := by
    simpa using (Finset.mem_sdiff.mp C.2).2
  obtain ⟨t, htsingle⟩ := Hunter.ProofsWP.compTails_F_single
    (Hunter.lem_pathrule hP) hC
  have htC : t ∈ C.1 := Hunter.ProofsWP.compTails_subset
    (by rw [htsingle]; exact Finset.mem_singleton_self t)
  have htTail : t ∈ tails (F P) := by
    rw [tails, Finset.mem_filter]
    have htCompTail : t ∈ compTails (F P) C.1 := by
      rw [htsingle]
      exact Finset.mem_singleton_self t
    rw [compTails, Finset.mem_filter] at htCompTail
    exact ⟨Finset.mem_univ _, htCompTail.2⟩
  have hblock : Hunter.ProofsWP.block (F P) t = C.1 :=
    (Hunter.ProofsWP.comp_eq_block_of_mem hC htC).symm
  have htNeFirst : t ≠ P.first := by
    intro heq
    apply hCne
    rw [← hblock, heq]
  have htNotTailP : t ∉ tails P.edges := by
    rw [Hunter.ProofsWP.tails_edges_ham hP, Finset.mem_singleton]
    exact htNeFirst
  let a : {a : Vtx k // a ∈ tails (F P) \ tails P.edges} :=
    ⟨t, Finset.mem_sdiff.mpr ⟨htTail, htNotTailP⟩⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact hblock

/-- 非根组件尾与非根组件之间的实际有限双射。 -/
noncomputable def nonRootTailComponentEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {a : Vtx k // a ∈ tails (F P) \ tails P.edges} ≃ NonRootComponent P :=
  Equiv.ofBijective (nonRootTailComponent hP hk)
    ⟨nonRootTailComponent_injective hP hk,
      nonRootTailComponent_surjective hP hk⟩

/-- 非终端链终点与非根 Hunter 组件的复合双射。 -/
noncomputable def chainTargetComponentEquiv
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} ≃ NonRootComponent P :=
  (chainTargetTailEquiv hP).trans (nonRootTailComponentEquiv hP hk)

/-- 实际出口基线精确等于所有非根组件的 `μ-1` 求和。 -/
theorem actualExitBaseline_eq_nonRootComponentSum
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualExitBaseline hP =
      ∑ C : NonRootComponent P, ((compMinto (F P) C.1 : ℤ) - 1) := by
  unfold actualExitBaseline
  refine Fintype.sum_equiv (chainTargetComponentEquiv hP hk)
    (fun v =>
      (compMinto (F P)
        (Hunter.ProofsWP.block (F P) (chainTargetTail hP v).1) : ℤ) - 1)
    (fun C => (compMinto (F P) C.1 : ℤ) - 1) ?_
  intro v
  rfl

/-- 链起点数的有符号整数形式：`|K| = c-1+I`。 -/
theorem card_chainStarts_int
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℤ) =
      (numComps (F P) : ℤ) - 1 + (indicatorI P (Sset P) : ℤ) := by
  rw [Fintype.card_coe, Hunter.ProofsWP.indicatorI_eq_ite hP]
  have hcard := card_chainStarts hP hk
  by_cases hh : P.last ∈ heads (F P)
  · rw [if_pos hh] at hcard ⊢
    have hcardZ : ((chainStarts P).card : ℤ) + 1 = (numComps (F P) : ℤ) := by
      exact_mod_cast hcard
    omega
  · rw [if_neg hh] at hcard ⊢
    have hcardZ : ((chainStarts P).card : ℤ) = (numComps (F P) : ℤ) := by
      exact_mod_cast hcard
    omega

/-- 非根组件的出口基线和展开为总 `μ` 和减根项、再减 `c-1`。 -/
theorem nonRootComponentBaseline_eq
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (∑ C : NonRootComponent P, ((compMinto (F P) C.1 : ℤ) - 1)) =
      (∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ))
        - (compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) : ℤ)
        - ((numComps (F P) : ℤ) - 1) := by
  let C0 := Hunter.ProofsWP.block (F P) P.first
  let D := Comps (F P) \ {C0}
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hC0 : C0 ∈ Comps (F P) :=
    Hunter.ProofsWP.block_mem_comps (hV ▸ Finset.mem_univ P.first)
  have hnc1 := Hunter.ProofsWP.one_le_numComps_F hP hk
  have hDcard : D.card = numComps (F P) - 1 := by
    have h : D.card + 1 = (Comps (F P)).card := by
      dsimp only [D]
      simpa using Finset.card_sdiff_add_card_eq_card
        (Finset.singleton_subset_iff.mpr hC0)
    change D.card = (Comps (F P)).card - 1
    omega
  have hsumsdiff :
      (∑ C ∈ D, (compMinto (F P) C : ℤ)) + (compMinto (F P) C0 : ℤ) =
        ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
    have h := Finset.sum_sdiff
      (f := fun C => (compMinto (F P) C : ℤ))
      (Finset.singleton_subset_iff.mpr hC0)
    rwa [Finset.sum_singleton] at h
  change (∑ C : ↑D, ((compMinto (F P) C.1 : ℤ) - 1)) = _
  have hcoe :
      (∑ C : ↑D, ((compMinto (F P) C.1 : ℤ) - 1)) =
        ∑ C ∈ D, ((compMinto (F P) C : ℤ) - 1) :=
    Finset.sum_coe_sort D
      (fun C => ((compMinto (F P) C : ℤ) - 1))
  rw [hcoe, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one, hDcard]
  change (∑ C ∈ D, (compMinto (F P) C : ℤ)) - (↑(numComps (F P) - 1) : ℤ) = _
  push_cast [hnc1]
  change _ = _ - (compMinto (F P) C0 : ℤ) - _
  linarith [hsumsdiff]

/--
论文公式 (10) 的完整实际组件形式。`μmax` 由组件有限集上的 `sup compMinto`
给出；右端总剩余成本完全由实际 `D_P` 的入口、内部边和非终端出口定义。
-/
theorem actual_preimage_chain_identity_components
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (P.wtP : ℤ) -
        ((numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) +
          (wEdges (F P) : ℤ)) =
      (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ)
        - (compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) : ℤ)
        + (indicatorI P (Sset P) : ℤ)
        + actualPreimageSurplus hP := by
  have hminNat := Hunter.ProofsGB2.minThrough_add_sup (F P)
  have hmin :
      (MinThrough (F P) : ℤ) +
          (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) =
        ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
    calc
      (MinThrough (F P) : ℤ) +
          (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) =
          ((MinThrough (F P) +
            (Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) := by
              push_cast
              ring
      _ = ((∑ C ∈ Comps (F P), compMinto (F P) C : ℕ) : ℤ) := by
            rw [hminNat]
      _ = ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
            push_cast
            rfl
  rw [actual_preimage_surplus_identity hP (by omega),
    actualExitBaseline_eq_nonRootComponentSum hP hk,
    nonRootComponentBaseline_eq hP hk,
    card_chainStarts_int hP hk]
  rw [← hmin]
  ring

/-- 完整实际组件恒等式直接推出 Hunter 基线不超过原路径权重。 -/
theorem actual_component_baseline_le_pathWeight
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) +
        (wEdges (F P) : ℤ) ≤ (P.wtP : ℤ) := by
  have hV := Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk
  have hrootMem : Hunter.ProofsWP.block (F P) P.first ∈ Comps (F P) :=
    Hunter.ProofsWP.block_mem_comps (hV ▸ Finset.mem_univ P.first)
  have hrootNat :
      compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) ≤
        (Comps (F P)).sup (compMinto (F P)) :=
    Finset.le_sup hrootMem
  have hroot :
      (compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) : ℤ) ≤
        (((Comps (F P)).sup (compMinto (F P)) : ℕ) : ℤ) := by
    exact_mod_cast hrootNat
  have hsurplus := actualPreimageSurplus_nonneg hP hk
  have hid := actual_preimage_chain_identity_components hP hk
  have hindicator : 0 ≤ (indicatorI P (Sset P) : ℤ) := by omega
  linarith

end PreimageChain

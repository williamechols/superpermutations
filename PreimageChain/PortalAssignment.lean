import PreimageChain.PiRelaxation
import PreimageChain.Layerwise

/-!
# 门户义务与容量一指派

本模块闭合分层证明中的有限组合核心：若零成本门户只能注入一个给定的吸收器
集合，则除这些吸收器外的门户义务必须在总指派成本中各贡献至少一。
-/

namespace PreimageChain

open scoped Classical

/-- 容量一靶映射把零成本门户注入吸收器时，剩余门户数由总自然数成本支配。 -/
theorem portal_obligation_cost_lower_bound
    {Source Target : Type*} [Fintype Source]
    [DecidableEq Source] [DecidableEq Target]
    (target : Source → Target) (htarget : Function.Injective target)
    (portals : Finset Source) (absorbers : Finset Target)
    (cost : Source → ℕ)
    (hzero : ∀ s ∈ portals, cost s = 0 → target s ∈ absorbers) :
    portals.card - absorbers.card ≤ ∑ s, cost s := by
  classical
  let zeroPortals := portals.filter fun s => cost s = 0
  let positivePortals := portals.filter fun s => cost s ≠ 0
  have himage : zeroPortals.image target ⊆ absorbers := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨s, hsZero, rfl⟩ := hy
    have hs := Finset.mem_filter.mp hsZero
    exact hzero s hs.1 hs.2
  have hzeroCard : zeroPortals.card ≤ absorbers.card := by
    calc
      zeroPortals.card = (zeroPortals.image target).card :=
        (Finset.card_image_of_injective zeroPortals htarget).symm
      _ ≤ absorbers.card := Finset.card_le_card himage
  have hpartition : zeroPortals.card + positivePortals.card = portals.card := by
    simpa [zeroPortals, positivePortals] using
      (Finset.card_filter_add_card_filter_not (s := portals)
        (fun s => cost s = 0))
  have hremaining : portals.card - absorbers.card ≤ positivePortals.card := by
    omega
  have hpositive : positivePortals.card ≤ ∑ s, cost s := by
    calc
      positivePortals.card = ∑ s ∈ positivePortals, 1 := by simp
      _ ≤ ∑ s ∈ positivePortals, cost s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsPos : cost s ≠ 0 :=
          (Finset.mem_filter.mp hs).2
        omega
      _ ≤ ∑ s ∈ (Finset.univ : Finset Source), cost s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ positivePortals)
        intro s _hs _hnot
        exact Nat.zero_le _
      _ = ∑ s, cost s := rfl
  exact hremaining.trans hpositive

/-- 允许至多一个末组件/终端链例外后的门户义务下界。 -/
theorem portal_obligation_with_one_exception
    {Source Target : Type*} [Fintype Source]
    [DecidableEq Source] [DecidableEq Target]
    (target : Source → Target) (htarget : Function.Injective target)
    (portals exceptional : Finset Source) (absorbers : Finset Target)
    (cost : Source → ℕ) (hexceptional : exceptional.card ≤ 1)
    (hzero : ∀ s ∈ portals, s ∉ exceptional → cost s = 0 →
      target s ∈ absorbers) :
    portals.card - 1 - absorbers.card ≤ ∑ s, cost s := by
  classical
  let eligible := portals \ exceptional
  have heligibleLower : portals.card - 1 ≤ eligible.card := by
    have hinter : (portals ∩ exceptional).card ≤ 1 := by
      exact (Finset.card_le_card (Finset.inter_subset_right)).trans hexceptional
    rw [show eligible.card = portals.card - (portals ∩ exceptional).card by
      simp [eligible, Finset.card_sdiff, Finset.inter_comm]]
    omega
  have hbase : eligible.card - absorbers.card ≤ ∑ s, cost s := by
    apply portal_obligation_cost_lower_bound target htarget eligible absorbers cost
    intro s hsEligible hsZero
    have hs := Finset.mem_sdiff.mp hsEligible
    exact hzero s hs.1 hs.2 hsZero
  omega

end PreimageChain

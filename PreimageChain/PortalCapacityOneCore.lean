import PreimageChain.LayerCorrectionAlgebra

/-!
# Lightweight capacity-one portal counting

This module isolates the finite-set counting used by the final pathwise proof from the heavier
actual-chain API.
-/

namespace PreimageChain

open scoped BigOperators Classical

/-- An injective target map sends all zero-cost selected sources into a bounded absorber set. -/
theorem portal_obligation_cost_lower_bound_core
    {Source Target : Type*} [Fintype Source]
    [DecidableEq Source] [DecidableEq Target]
    (target : Source → Target) (htarget : Function.Injective target)
    (portals : Finset Source) (absorbers : Finset Target)
    (cost : Source → ℕ)
    (hzero : ∀ s ∈ portals, cost s = 0 → target s ∈ absorbers) :
    portals.card - absorbers.card ≤ ∑ s, cost s := by
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
        have hsPos : cost s ≠ 0 := (Finset.mem_filter.mp hs).2
        omega
      _ ≤ ∑ s ∈ (Finset.univ : Finset Source), cost s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ positivePortals)
        intro s _hs _hnot
        exact Nat.zero_le _
      _ = ∑ s, cost s := rfl
  exact hremaining.trans hpositive

end PreimageChain

import PreimageChain.PathwisePortalCountCore
import PreimageChain.PortalCoverageAlgebra

/-!
# Actual portal sources

The actual chain-source map is injective and misses at most one component.  Consequently the
sources whose components are non-distinguished terminal portals cover the theoretical portal count
up to the single exception already present in the paper.
-/

namespace PreimageChain

open Hunter
open scoped Classical BigOperators

variable {k : ℕ}

/-- Actual chain starts whose source component is a non-distinguished terminal portal. -/
noncomputable def actualPortalSourcesCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset {v : Vtx k // v ∈ chainStarts P} :=
  Finset.univ.filter fun s =>
    let C := actualChainSourceComponent hP hk s
    C ≠ distinguishedComponent hP hk ∧ actualPortalBit hP C = 1

/-- The cardinality form of the non-distinguished portal sum. -/
theorem nondistinguishedPortalCountCore_eq_filter_card
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    nondistinguishedPortalCountCore hP hk =
      ((Finset.univ : Finset (ActualComponents P)).filter fun C =>
        C ≠ distinguishedComponent hP hk ∧ actualPortalBit hP C = 1).card := by
  classical
  unfold nondistinguishedPortalCountCore
  let predicate : ActualComponents P → Prop := fun C =>
    C ≠ distinguishedComponent hP hk ∧ actualPortalBit hP C = 1
  calc
    (∑ C : ActualComponents P,
        if C = distinguishedComponent hP hk then 0 else actualPortalBit hP C) =
      ∑ C ∈ (Finset.univ : Finset (ActualComponents P)),
        if predicate C then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro C _
          by_cases hstar : C = distinguishedComponent hP hk
          · simp [predicate, hstar]
          · have hbit := actualPortalBit_le_one hP C
            by_cases hone : actualPortalBit hP C = 1
            · simp [predicate, hstar, hone]
            · have hzero : actualPortalBit hP C = 0 := by omega
              simp [predicate, hstar, hone, hzero]
    _ = ((Finset.univ : Finset (ActualComponents P)).filter predicate).card := by
      exact Finset.sum_boole predicate (Finset.univ : Finset (ActualComponents P))

/-- The chain-source type has codimension at most one in the actual component type. -/
theorem actualChainSource_card_codimension_one_core
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Fintype.card (ActualComponents P) ≤
      Fintype.card {v : Vtx k // v ∈ chainStarts P} + 1 := by
  have hcard := card_chainStarts hP hk
  have hcomponents :
      Fintype.card (ActualComponents P) = (Comps (F P)).card := by
    change Fintype.card ↑(Comps (F P)) = (Comps (F P)).card
    exact Fintype.card_coe _
  have hstarts :
      Fintype.card {v : Vtx k // v ∈ chainStarts P} = (chainStarts P).card := by
    exact Fintype.card_coe _
  rw [hcomponents, hstarts]
  unfold numComps at hcard
  by_cases hlast : P.last ∈ heads (F P)
  · rw [if_pos hlast] at hcard
    omega
  · rw [if_neg hlast] at hcard
    omega

/-- All but at most one theoretical portal are represented by actual chain sources. -/
theorem nondistinguishedPortalCountCore_sub_one_le_sources
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    nondistinguishedPortalCountCore hP hk - 1 ≤
      (actualPortalSourcesCore hP hk).card := by
  let predicate : ActualComponents P → Prop := fun C =>
    C ≠ distinguishedComponent hP hk ∧ actualPortalBit hP C = 1
  have hcoverage := filtered_univ_source_card_codimension_one
    (actualChainSourceComponent hP hk)
    (actualChainSourceComponent_injective hP hk)
    predicate
    (actualChainSource_card_codimension_one_core hP hk)
  rw [← nondistinguishedPortalCountCore_eq_filter_card hP hk] at hcoverage
  simpa [actualPortalSourcesCore, predicate] using hcoverage

end PreimageChain

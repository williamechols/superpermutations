import PreimageChain.PathwiseHighEntryCore
import PreimageChain.PathwisePaymentCore

/-!
# Ordinary and paid actual chain targets

Non-root high-entry components are ordinary zero-cost absorbers.  A distinguished non-root target
is paid by the exact root-`μ` gap; in the unique-terminal-chain case the terminal symbol is paid by
the exact indicator term.
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- The non-root component target type used by both actual chain matchings. -/
abbrev ActualNonRootTarget
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :=
  {C : ActualComponents P // C ≠ actualRootComponent hP hk}

/-- Ordinary non-root targets: non-distinguished components of minimum entry at least three. -/
noncomputable def ordinaryComponentTargetsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset (ActualNonRootTarget hP hk) :=
  Finset.univ.filter fun A =>
    A.1 ≠ distinguishedComponent hP hk ∧ 3 ≤ actualMu A.1

/-- The possible distinguished non-root target. -/
noncomputable def distinguishedComponentTargetsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset (ActualNonRootTarget hP hk) :=
  Finset.univ.filter fun A => A.1 = distinguishedComponent hP hk

/-- Ordinary targets inject into the global high-entry non-distinguished component set. -/
theorem ordinaryComponentTargetsCore_card_le_highEntry
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (ordinaryComponentTargetsCore hP hk).card ≤
      (nondistinguishedHighEntryComponentsCore hP hk).card := by
  let f : ActualNonRootTarget hP hk → ActualComponents P := fun A => A.1
  have hf : Function.Injective f := by
    intro A B h
    exact Subtype.ext h
  have himage : (ordinaryComponentTargetsCore hP hk).image f ⊆
      nondistinguishedHighEntryComponentsCore hP hk := by
    intro C hC
    rw [Finset.mem_image] at hC
    obtain ⟨A, hA, rfl⟩ := hC
    have hmem := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.2⟩
  calc
    (ordinaryComponentTargetsCore hP hk).card =
        ((ordinaryComponentTargetsCore hP hk).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ (nondistinguishedHighEntryComponentsCore hP hk).card :=
      Finset.card_le_card himage

/-- There is at most one distinguished non-root target. -/
theorem distinguishedComponentTargetsCore_card_le_one
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (distinguishedComponentTargetsCore hP hk).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro A hA B hB
  apply Subtype.ext
  have hAeq := (Finset.mem_filter.mp hA).2
  have hBeq := (Finset.mem_filter.mp hB).2
  exact hAeq.trans hBeq.symm

/-- The distinguished non-root target is paid by the natural root gap. -/
theorem distinguishedComponentTargetsCore_card_le_rootGap
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (distinguishedComponentTargetsCore hP hk).card ≤ actualRootGap hP hk := by
  by_cases hstar : distinguishedComponent hP hk = actualRootComponent hP hk
  · have hempty : distinguishedComponentTargetsCore hP hk = ∅ := by
      ext A
      simp [distinguishedComponentTargetsCore, hstar, A.2]
    rw [hempty]
    exact Nat.zero_le _
  · exact (distinguishedComponentTargetsCore_card_le_one hP hk).trans
      (one_le_actualRootGap_of_distinguished_ne_root hP hk hstar)

/-- Ordinary targets in the unique-terminal matching. -/
noncomputable def terminalOrdinaryTargetsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset (Sum (ActualNonRootTarget hP hk) Unit) :=
  (ordinaryComponentTargetsCore hP hk).image Sum.inl

/-- Paid targets in the unique-terminal matching: distinguished non-root target plus `⋆`. -/
noncomputable def terminalPaidTargetsCore
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Finset (Sum (ActualNonRootTarget hP hk) Unit) :=
  (distinguishedComponentTargetsCore hP hk).image Sum.inl ∪ {Sum.inr ()}

/-- The terminal ordinary target count is bounded by the global high-entry count. -/
theorem terminalOrdinaryTargetsCore_card_le_highEntry
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (terminalOrdinaryTargetsCore hP hk).card ≤
      (nondistinguishedHighEntryComponentsCore hP hk).card := by
  let inl : ActualNonRootTarget hP hk →
      Sum (ActualNonRootTarget hP hk) Unit := fun A => Sum.inl A
  have hinl : Function.Injective inl := by
    intro A B h
    exact Sum.inl.inj h
  calc
    (terminalOrdinaryTargetsCore hP hk).card =
        (ordinaryComponentTargetsCore hP hk).card := by
      unfold terminalOrdinaryTargetsCore
      change ((ordinaryComponentTargetsCore hP hk).image inl).card = _
      exact Finset.card_image_of_injective _ hinl
    _ ≤ (nondistinguishedHighEntryComponentsCore hP hk).card :=
      ordinaryComponentTargetsCore_card_le_highEntry hP hk

/-- In the unique-terminal case the paid target count is bounded by root gap plus indicator. -/
theorem terminalPaidTargetsCore_card_le_payment
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hlast : P.last ∉ heads (F P)) :
    (terminalPaidTargetsCore hP hk).card ≤
      actualRootGap hP hk + actualTerminalIndicatorCore P := by
  have hdist := distinguishedComponentTargetsCore_card_le_rootGap hP hk
  let inl : ActualNonRootTarget hP hk →
      Sum (ActualNonRootTarget hP hk) Unit := fun A => Sum.inl A
  have hinl : Function.Injective inl := by
    intro A B h
    exact Sum.inl.inj h
  have himage :
      ((distinguishedComponentTargetsCore hP hk).image inl).card =
        (distinguishedComponentTargetsCore hP hk).card :=
    Finset.card_image_of_injective _ hinl
  have hunion := Finset.card_union_le
    ((distinguishedComponentTargetsCore hP hk).image inl)
    ({Sum.inr ()} : Finset (Sum (ActualNonRootTarget hP hk) Unit))
  have hindicator : actualTerminalIndicatorCore P = 1 := by
    unfold actualTerminalIndicatorCore
    rw [Hunter.ProofsWP.indicatorI_eq_ite hP, if_neg hlast]
  unfold terminalPaidTargetsCore
  change ((distinguishedComponentTargetsCore hP hk).image inl ∪
      {Sum.inr ()}).card ≤ _
  rw [himage] at hunion
  simp only [Finset.card_singleton] at hunion
  omega

end PreimageChain

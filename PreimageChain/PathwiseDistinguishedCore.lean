import PreimageChain.PathwiseBaseline
import PreimageChain.ComponentGeometry
import PreimageChain.RootBiasedArgmaxNat

/-!
# Root-biased distinguished actual component

The distinguished component maximizes minimum entry weight and selects the actual root on a
tie, exactly as in Section 9 of the paper.
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

noncomputable abbrev ActualComponents {k : ℕ} (P : HPath k) := ActualComponent P

/-- The component of `F(P)` containing the first path vertex is the existing component-matching root. -/
@[simp] theorem actualRootComponent_val
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualRootComponent hP hk).1 = Hunter.ProofsWP.block (F P) P.first := rfl

/-- Minimum entry weight of an actual component. -/
noncomputable def actualMu {P : HPath k} (C : ActualComponents P) : ℕ :=
  compMinto (F P) C.1

/-- Integer geometry data of an actual component. -/
noncomputable def actualGeom {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponents P) : Geometry :=
  actualComponentGeometry hP C

/-- Maximum-`μ` component, choosing the actual root on a tie. -/
noncomputable def distinguishedComponent
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ActualComponents P :=
  rootBiasedArgmaxNat actualMu (actualRootComponent hP hk)

/-- The distinguished component has maximum minimum-entry weight. -/
theorem actualMu_le_distinguished
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponents P) :
    actualMu C ≤ actualMu (distinguishedComponent hP hk) := by
  exact score_le_rootBiasedArgmaxNat actualMu (actualRootComponent hP hk) C

/-- Its `μ` is exactly the supremum over Hunter components. -/
theorem distinguished_mu_eq_sup
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualMu (distinguishedComponent hP hk) =
      (Comps (F P)).sup (compMinto (F P)) := by
  apply le_antisymm
  · exact Finset.le_sup (distinguishedComponent hP hk).2
  · apply Finset.sup_le
    intro C hC
    exact actualMu_le_distinguished hP hk ⟨C, hC⟩

/-- If the root reaches the maximum score, the tie rule chooses it. -/
theorem distinguished_eq_root_of_mu_ge
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hmu : actualMu (distinguishedComponent hP hk) ≤
      actualMu (actualRootComponent hP hk)) :
    distinguishedComponent hP hk = actualRootComponent hP hk := by
  exact rootBiasedArgmaxNat_eq_root_of_score_ge
    actualMu (actualRootComponent hP hk) hmu

/-- If the distinguished component is not the root, its score is at least one larger. -/
theorem root_mu_add_one_le_distinguished
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hne : distinguishedComponent hP hk ≠ actualRootComponent hP hk) :
    actualMu (actualRootComponent hP hk) + 1 ≤
      actualMu (distinguishedComponent hP hk) := by
  exact root_score_add_one_le_argmaxNat
    actualMu (actualRootComponent hP hk) hne

/-- Distinct actual components are vertex-disjoint, so a spanning component is unique. -/
theorem nondistinguished_nonspanning
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponents P)
    (hne : C ≠ distinguishedComponent hP hk) :
    C.1 ≠ Finset.univ := by
  intro hspan
  apply hne
  apply Subtype.ext
  by_contra hval
  have hdisj := Hunter.ProofsWP.comps_disjoint C.2
    (distinguishedComponent hP hk).2 hval
  let v := actualComponentHead hP (distinguishedComponent hP hk)
  have hvStar : v ∈ (distinguishedComponent hP hk).1 :=
    actualComponentHead_mem_component hP (distinguishedComponent hP hk)
  have hvC : v ∈ C.1 := by
    rw [hspan]
    exact Finset.mem_univ v
  exact Finset.disjoint_left.mp hdisj hvC hvStar

/-- The root-gap term appearing in the exact preimage-chain identity. -/
noncomputable def actualRootGap
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) : ℕ :=
  actualMu (distinguishedComponent hP hk) - actualMu (actualRootComponent hP hk)

/-- A non-root distinguished target carries at least one unit of root-gap payment. -/
theorem one_le_actualRootGap_of_distinguished_ne_root
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hne : distinguishedComponent hP hk ≠ actualRootComponent hP hk) :
    1 ≤ actualRootGap hP hk := by
  unfold actualRootGap
  have h := root_mu_add_one_le_distinguished hP hk hne
  omega

/-- The natural root gap is the exact max-minus-root term from the component identity. -/
theorem actualRootGap_eq_sup_sub_root
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualRootGap hP hk =
      (Comps (F P)).sup (compMinto (F P)) -
        compMinto (F P) (Hunter.ProofsWP.block (F P) P.first) := by
  unfold actualRootGap
  rw [distinguished_mu_eq_sup hP hk]
  rfl

end PreimageChain

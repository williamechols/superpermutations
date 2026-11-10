import LowerBounds.SBridge
import LowerBounds.TheoremCWords

/-!
# Theorem C from the model

`ModelStatement k cn bn q` (the window bound for all model chains, `SModelDef.lean`) in place of
the hypothesis `HStatement k cn bn q` of Theorem C: the statements of `TheoremC.lean` and
`TheoremCWords.lean` with `hStatement_of_model` applied.  With a proof of
`ModelStatement k cn bn q` (a finite search) and the three arithmetic conditions
`ConditionsC k cn bn q` these are bounds without a hypothesis about paths.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain SuperpermutationBounds

variable {k cn bn q : ℕ}

/-- Theorem C for one Hamiltonian path, from the model. -/
theorem theoremC_pathwise_of_model (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hM : ModelStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) :=
  theoremC_pathwise hk hcond (hStatement_of_model hk hM) hP

/-- Theorem C for the length of the shortest superpermutation, from the model. -/
theorem superperm_boundC_of_model (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hM : ModelStatement k cn bn q) : boundC k cn bn q ≤ Ssuper k :=
  superperm_boundC hk hcond (hStatement_of_model hk hM)

/-- Theorem C for covering words over `Fin k`, from the model. -/
theorem covers_length_ge_boundC_of_model (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hM : ModelStatement k cn bn q) :
    ∀ w : List (Fin k), Covers w → boundC k cn bn q ≤ w.length :=
  covers_length_ge_boundC hk hcond (hStatement_of_model hk hM)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.theoremC_pathwise_of_model
#print axioms SuperpermLowerBounds.superperm_boundC_of_model
#print axioms SuperpermLowerBounds.covers_length_ge_boundC_of_model

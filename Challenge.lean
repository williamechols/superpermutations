import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Basic

/-!
Independent statements of the upper bounds, separate from their proofs.

`Covers` means that every permutation occurs as a contiguous substring.
`Finite` and `FiniteInteger` state the main explicit parameter bounds.
`Eventual` is their asymptotic consequence: each positive rational epsilon
eventually permits the coefficient 43/80 + epsilon.

The propositions in this file make no unproved assertions. Their proofs are
in `Solution.lean`. The sharper logarithmic error rate has a paper proof;
that rate is not claimed by this formalization.

Every subtraction and division in `Cost`, except its guarded factorial
index, is rational. The integer parameter is used without truncation.
-/
namespace SuperpermutationBounds

def Covers {K : ℕ} (w : List (Fin K)) : Prop :=
  ∀ p : List (Fin K), p.length = K → p.Nodup →
    ∃ u v : List (Fin K), w = u ++ p ++ v

def F3 (K : ℕ) : ℚ :=
  (Nat.factorial K : ℚ) + (Nat.factorial (K - 1) : ℚ) +
    (Nat.factorial (K - 2) : ℚ)

def Cost (m : ℕ) (a : ℤ) : ℚ :=
  F3 (m + 2) + (43 / 80 : ℚ) * (Nat.factorial (m - 1) : ℚ) +
    ((a : ℚ) - 2) * ((17 / 240 : ℚ) * (Nat.factorial (m - 1) : ℚ) /
      ((m : ℚ) - 1)) +
    ((m : ℚ) - (a : ℚ)) * min
      ((17 / 240 : ℚ) * (Nat.factorial (m - 1) : ℚ) / ((m : ℚ) - 1))
      ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1).toNat : ℚ))

def Finite : Prop :=
  ∀ m a : ℕ, 9 ≤ m → 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost m (a : ℤ)

def FiniteInteger : Prop :=
  ∀ m : ℕ, ∀ a : ℤ, 9 ≤ m → 2 ≤ a → a ≤ (m : ℤ) →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ Cost m a

def Eventual : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 11 ≤ N ∧
    ∀ K : ℕ, N ≤ K → ∃ w : List (Fin K),
      Covers w ∧ (w.length : ℚ) ≤
        F3 K + ((43 / 80 : ℚ) + ε) * (Nat.factorial (K - 3) : ℚ)

/-- A finite upper bound asserts existence of an actual covering word. -/
def HasWord (K bound : ℕ) : Prop :=
  ∃ w : List (Fin K), Covers w ∧ w.length ≤ bound

/-- A uniform finite bound valid at every size at least ten. -/
def UniformThreeFifths : Prop :=
  ∀ K : ℕ, 10 ≤ K → ∃ w : List (Fin K), Covers w ∧
    5 * w.length ≤
      5 * (K.factorial + (K - 1).factorial + (K - 2).factorial) +
        3 * (K - 3).factorial

/-- A uniform finite bound valid at every size at least eight. -/
def Uniform101Over120 : Prop :=
  ∀ K : ℕ, 8 ≤ K → ∃ w : List (Fin K), Covers w ∧
    120 * w.length ≤
      120 * (K.factorial + (K - 1).factorial + (K - 2).factorial) +
        101 * (K - 3).factorial

end SuperpermutationBounds

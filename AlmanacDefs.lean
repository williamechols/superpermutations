/-!
# Superpermutation Almanac: the definitions file

Published by the Almanac, the same for every submission at a given Lean version. It imports
nothing beyond Lean's core, so it compiles unchanged on every allowed toolchain. The judge writes
this file over any file of the same name in a submitted repository.
-/
namespace Almanac

/-- A word on `n` symbols. -/
abbrev Word (n : Nat) : Type := List (Fin n)

/-- `w` is a superpermutation on `n` symbols: every arrangement of the `n` symbols (a
duplicate-free word of length `n`) occurs in `w` as a contiguous block. -/
def IsSuperpermutation (n : Nat) (w : Word n) : Prop :=
  ∀ p : Word n, p.Nodup → p.length = n → p <:+: w

/-- The factorial, defined here because core Lean has none. -/
def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k

/-- A formula in `n`, evaluated in `Rat`: rational constants, `n`, `+`, `-`, `*`,
powers `n ^ j`, factorials `(n - k)!`, and division. The site checks that every divisor is
positive and every `k` is at most `n₀` before it writes a statement. -/
inductive Expr where
  | const (q : Rat)
  | var
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | pow (j : Nat)
  | fact (k : Nat)
  | div (a b : Expr)

/-- The value of a formula at `n`. -/
def Expr.eval (n : Nat) : Expr → Rat
  | .const q => q
  | .var => (n : Rat)
  | .add a b => a.eval n + b.eval n
  | .sub a b => a.eval n - b.eval n
  | .mul a b => a.eval n * b.eval n
  | .pow j => (n : Rat) ^ j
  | .fact k => ((Almanac.fact (n - k) : Nat) : Rat)
  | .div a b => a.eval n / b.eval n

/-- Shape 1: every superpermutation on `n` symbols has length at least `v`. -/
def LowerBoundAt (n v : Nat) : Prop :=
  ∀ w : Word n, IsSuperpermutation n w → v ≤ w.length

/-- Shape 2: for every `n ≥ n₀`, every superpermutation on `n` symbols has length at least `f n`. -/
def LowerBoundFrom (n₀ : Nat) (f : Expr) : Prop :=
  ∀ n : Nat, n₀ ≤ n → ∀ w : Word n, IsSuperpermutation n w → f.eval n ≤ (w.length : Rat)

/-- Shape 2: for `n₀ ≤ n ≤ n₁`, every superpermutation on `n` symbols has length at least `f n`. -/
def LowerBoundRange (n₀ n₁ : Nat) (f : Expr) : Prop :=
  ∀ n : Nat, n₀ ≤ n → n ≤ n₁ → ∀ w : Word n, IsSuperpermutation n w → f.eval n ≤ (w.length : Rat)

/-- Shape 2: for every `n ≥ n₀` there is a superpermutation on `n` symbols of length at most `f n`. -/
def UpperBoundFrom (n₀ : Nat) (f : Expr) : Prop :=
  ∀ n : Nat, n₀ ≤ n → ∃ w : Word n, IsSuperpermutation n w ∧ (w.length : Rat) ≤ f.eval n

/-- `n! + (n-1)! + (n-2)! + c (n-3)!`, the form of the asymptotic shapes. -/
def asymptoticForm (n : Nat) (c : Rat) : Rat :=
  (fact n : Rat) + (fact (n - 1) : Rat) + (fact (n - 2) : Rat) + c * (fact (n - 3) : Rat)

/-- Shape 3: for every `ε > 0`, for all large `n`, some superpermutation on `n` symbols has length
at most `n! + (n-1)! + (n-2)! + (c + ε) (n-3)!`. -/
def AsymptoticUpper (c : Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∃ w : Word n, IsSuperpermutation n w ∧ (w.length : Rat) ≤ asymptoticForm n (c + ε)

/-- Shape 3: for every `ε > 0`, for all large `n`, every superpermutation on `n` symbols has length
at least `n! + (n-1)! + (n-2)! + (c - ε) (n-3)!`. -/
def AsymptoticLower (c : Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∀ w : Word n, IsSuperpermutation n w → asymptoticForm n (c - ε) ≤ (w.length : Rat)

end Almanac

/-!
## Factorial-scale asymptotic shapes

Added for batch submissions (Oct 27, 2026); everything above is unchanged. `asymptoticFormAt 3`
is `asymptoticForm`, so `AsymptoticUpperAt 3 c` and `AsymptoticLowerAt 3 c` are
`AsymptoticUpper c` and `AsymptoticLower c` by definition.
-/
namespace Almanac

/-- `n! + (n-1)! + (n-2)! + c (n-k)!`, the form of the factorial-scale asymptotic shapes. -/
def asymptoticFormAt (k n : Nat) (c : Rat) : Rat :=
  (fact n : Rat) + (fact (n - 1) : Rat) + (fact (n - 2) : Rat) + c * (fact (n - k) : Rat)

/-- Shape 3 at the scale `(n-k)!`: for every `ε > 0`, for all large `n`, some superpermutation on
`n` symbols has length at most `n! + (n-1)! + (n-2)! + (c + ε) (n-k)!`. -/
def AsymptoticUpperAt (k : Nat) (c : Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∃ w : Word n, IsSuperpermutation n w ∧ (w.length : Rat) ≤ asymptoticFormAt k n (c + ε)

/-- Shape 3 at the scale `(n-k)!`: for every `ε > 0`, for all large `n`, every superpermutation on
`n` symbols has length at least `n! + (n-1)! + (n-2)! + (c - ε) (n-k)!`. -/
def AsymptoticLowerAt (k : Nat) (c : Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∀ w : Word n, IsSuperpermutation n w → asymptoticFormAt k n (c - ε) ≤ (w.length : Rat)

end Almanac

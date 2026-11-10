import PreimageChain.PathwiseBaselineArithmetic

/-!
# Fixed Hamilton-path actual baseline and nonnegative layer

This is the public natural-number interface built on the kernel-checked pointwise Hunter
estimate.
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- Hunter's path baseline, namely the string bound minus the final `k` symbols. -/
def hunterPathBound (k : ℕ) : ℕ := Numerics.hunterBound k - k

/-- The actual Bound-1 value of the concrete Hunter image. -/
noncomputable def actualBaseline {k : ℕ} (P : HPath k) : ℕ := actualBaselineCore P

@[simp] theorem actualBaseline_eq_core {P : HPath k} :
    actualBaseline P = actualBaselineCore P := rfl

/-- Hunter's string bound contains the final `k` symbols without truncation. -/
theorem hunterBound_ge_k (hk : 5 ≤ k) : k ≤ Numerics.hunterBound k := by
  rw [Numerics.hunterBound]
  have hkfac : k ≤ k.factorial := Nat.self_le_factorial k
  omega

@[simp] theorem hunterPathBound_add_k (hk : 5 ≤ k) :
    hunterPathBound k + k = Numerics.hunterBound k := by
  unfold hunterPathBound
  exact Nat.sub_add_cancel (hunterBound_ge_k hk)

/-- Every actual Hamilton image lies at or above Hunter's rounded path baseline. -/
theorem actual_baseline_ge_hunterPath
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    hunterPathBound k ≤ actualBaseline P := by
  exact actualBaselineCore_ge_hunterPath hk hP

/-- The nonnegative integer layer of the actual image. -/
noncomputable def actualLayer
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) : ℕ :=
  actualBaseline P - hunterPathBound k

@[simp] theorem actualBaseline_eq_hunterPath_add_layer
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    actualBaseline P = hunterPathBound k + actualLayer hk hP := by
  have hge := actual_baseline_ge_hunterPath hk hP
  unfold actualLayer
  exact (Nat.add_sub_of_le hge).symm

@[simp] theorem actualBaseline_int_eq_hunterPath_add_layer
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (actualBaseline P : ℤ) = (hunterPathBound k : ℤ) + actualLayer hk hP := by
  exact_mod_cast actualBaseline_eq_hunterPath_add_layer hk hP

end PreimageChain

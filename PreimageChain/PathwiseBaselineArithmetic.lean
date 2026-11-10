import Hunter.Paper
import PreimageChain.PathwiseBaselineCore
import PreimageChain.Numerics

/-!
# Exact integer rounding of the pointwise Hunter baseline

The real pivot estimate is rewritten in factorial form and then rounded using the integrality
of the actual Bound-1 value.
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- The integral part of Hunter's path baseline, before the rational correction. -/
def hunterPathBaseNat (k : ℕ) : ℕ :=
  k.factorial + (k - 1).factorial + (k - 2).factorial - 3

/-- Numerator of Hunter's rational correction. -/
def hunterCorrectionNumerator (k : ℕ) : ℕ :=
  (k - 2).factorial - (k - 2)

/-- Coefficient form of the pointwise actual-image bound. -/
theorem actualBaselineCore_real_ge_coeff
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (actualBaselineCore P : ℝ) ≥
      coeff k * (k.factorial : ℝ) + ((k : ℝ) - 2) - coeff k * (k : ℝ) := by
  have hpivot : HasExitlessPath k (k * (k - 1) * (k - 2)) :=
    Hunter.Proved.hasExitlessPath_pivot k hk
  have hPpos : 0 < k * (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega,
      show m + 3 - 2 = m + 1 by omega]
    positivity
  have hi : iExitless k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 := by
    rw [Hunter.Proved.thm2_equality hk hPpos (le_refl _) hpivot,
      Hunter.ProofsReductions.j_pivot hk]
  have h := actualBaselineCore_real_ge_pivot hk hP
  rw [hi, Hunter.ProofsReductions.castI hk,
    Hunter.ProofsReductions.castP (by omega),
    Hunter.ProofsReductions.ratio_eq_coeff hk] at h
  have hD := Hunter.ProofsReductions.D_pos hk
  have hq : coeff k *
      ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ)) =
      (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2 := by
    rw [← Hunter.ProofsReductions.ratio_eq_coeff hk, div_mul_cancel₀]
    exact ne_of_gt hD
  have e1 : coeff k *
      ((k.factorial : ℝ) - (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) =
      coeff k * (k.factorial : ℝ) -
        coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) := by
    ring
  have e2 : coeff k *
      ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ)) =
      coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) -
        coeff k * (k : ℝ) := by
    ring
  linarith

/-- Exact algebraic expansion of the path-level coefficient expression. -/
theorem coeff_path_eq_factorial
    (hk : 3 ≤ k) :
    coeff k * (k.factorial : ℝ) + ((k : ℝ) - 2) - coeff k * (k : ℝ) =
      (k.factorial : ℝ) + ((k - 1).factorial : ℝ) +
        ((k - 2).factorial : ℝ) +
        (((k - 2).factorial : ℝ) - ((k : ℝ) - 2)) /
          ((k : ℝ) ^ 2 - 3 * (k : ℝ) + 1) - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  have f2 : ((m + 2).factorial : ℝ) =
      ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((m + 3).factorial : ℝ) =
      ((m : ℝ) + 3) * ((m + 2).factorial : ℝ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  set x : ℝ := ((m + 1).factorial : ℝ) with hx
  have key : coeff (m + 3) * (((m + 3).factorial : ℝ)) + ((m : ℝ) + 3)
        + (((m : ℝ) + 3) - 2) - coeff (m + 3) * ((m : ℝ) + 3) =
      ((m + 3).factorial : ℝ) + ((m + 2).factorial : ℝ) + x
        + ((x - (((m : ℝ) + 3) - 2)) /
          (((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1))
        + ((m : ℝ) + 3) - 3 := by
    rw [f3, f2, coeff]
    push_cast
    have hne1 : ((m : ℝ) + 3) ≠ 0 := by positivity
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hne2 : ((m : ℝ) + 3 - 1) ≠ 0 :=
      ne_of_gt (by linarith : (0 : ℝ) < (m : ℝ) + 3 - 1)
    have hne3 : ((m : ℝ) + 3) * ((m : ℝ) + 3 - 1) *
        ((m : ℝ) + 3 - 2) - ((m : ℝ) + 3) ≠ 0 := by
      rw [show ((m : ℝ) + 3) * ((m : ℝ) + 3 - 1) *
          ((m : ℝ) + 3 - 2) - ((m : ℝ) + 3) =
          ((m : ℝ) + 3) * ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 1) by ring]
      positivity
    have hne4 : ((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1 ≠ 0 := by
      rw [show ((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1 =
          (m : ℝ) ^ 2 + 3 * (m : ℝ) + 1 by ring]
      positivity
    have hne5 : (1 + (m : ℝ) * 3 + (m : ℝ) ^ 2) ≠ 0 := by positivity
    field_simp
    linear_combination mul_inv_cancel₀ hne5
  push_cast at key ⊢
  linarith [key]

/-- Factorial real form of the pointwise actual-image bound. -/
theorem actualBaselineCore_real_ge_factorial
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (actualBaselineCore P : ℝ) ≥
      (k.factorial : ℝ) + ((k - 1).factorial : ℝ) +
        ((k - 2).factorial : ℝ) +
        (((k - 2).factorial : ℝ) - ((k : ℝ) - 2)) /
          ((k : ℝ) ^ 2 - 3 * (k : ℝ) + 1) - 3 := by
  rw [← coeff_path_eq_factorial hk]
  exact actualBaselineCore_real_ge_coeff hk hP

/-- Cast of the natural denominator `dNat`. -/
theorem dNat_cast_real (hk : 3 ≤ k) :
    (Numerics.dNat k : ℝ) = (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1 := by
  unfold Numerics.dNat
  have hprod : 1 ≤ (k - 1) * (k - 2) := by
    have hp : 0 < (k - 1) * (k - 2) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  rw [Nat.cast_sub hprod, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
  push_cast
  ring

/-- Cast of the correction numerator. -/
theorem hunterCorrectionNumerator_cast_real (hk : 5 ≤ k) :
    (hunterCorrectionNumerator k : ℝ) =
      ((k - 2).factorial : ℝ) - ((k : ℝ) - 2) := by
  unfold hunterCorrectionNumerator
  have hle : k - 2 ≤ (k - 2).factorial :=
    Nat.self_le_factorial (k - 2)
  rw [Nat.cast_sub hle, Nat.cast_sub (by omega : 2 ≤ k)]
  push_cast
  ring

/-- Cast of the integral path baseline. -/
theorem hunterPathBaseNat_cast_real (hk : 5 ≤ k) :
    (hunterPathBaseNat k : ℝ) =
      (k.factorial : ℝ) + ((k - 1).factorial : ℝ) +
        ((k - 2).factorial : ℝ) - 3 := by
  unfold hunterPathBaseNat
  have hthree : 3 ≤ k.factorial + (k - 1).factorial + (k - 2).factorial := by
    have hpos := Nat.factorial_pos k
    have hpos1 := Nat.factorial_pos (k - 1)
    have hpos2 := Nat.factorial_pos (k - 2)
    omega
  rw [Nat.cast_sub hthree]
  push_cast
  ring

/-- Generic integrality lemma turning a real quotient bound into a natural ceiling bound. -/
theorem nat_add_ceilDiv_le_of_cast_add_div_le
    {A B n d : ℕ} (hd : 0 < d)
    (h : (A : ℝ) + (n : ℝ) / (d : ℝ) ≤ (B : ℝ)) :
    A + n ⌈/⌉ d ≤ B := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnonneg : 0 ≤ (n : ℝ) / (d : ℝ) := by positivity
  have hABR : (A : ℝ) ≤ (B : ℝ) := by linarith
  have hAB : A ≤ B := by exact_mod_cast hABR
  have hdiv : (n : ℝ) / (d : ℝ) ≤ (B : ℝ) - (A : ℝ) := by linarith
  have hmulR : (n : ℝ) ≤ ((B : ℝ) - (A : ℝ)) * (d : ℝ) :=
    (div_le_iff₀ hdR).mp hdiv
  have hcastSub : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) :=
    Nat.cast_sub hAB
  have hmulNat : n ≤ d * (B - A) := by
    exact_mod_cast (by
      rw [← hcastSub] at hmulR
      nlinarith : (n : ℝ) ≤ (d : ℝ) * ((B - A : ℕ) : ℝ))
  have hceil : n ⌈/⌉ d ≤ B - A :=
    (ceilDiv_le_iff_le_mul hd).2 hmulNat
  omega

/-- Natural-number version of the exact pointwise Hunter path baseline. -/
theorem actualBaselineCore_ge_roundedHunter
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    hunterPathBaseNat k +
        hunterCorrectionNumerator k ⌈/⌉ Numerics.dNat k ≤
      actualBaselineCore P := by
  apply nat_add_ceilDiv_le_of_cast_add_div_le (Numerics.dNat_pos (by omega))
  rw [hunterPathBaseNat_cast_real hk,
    hunterCorrectionNumerator_cast_real hk, dNat_cast_real (by omega)]
  have hreal := actualBaselineCore_real_ge_factorial (by omega) hP
  nlinarith

/-- The path-level Hunter bound is exactly the rounded expression above. -/
theorem hunterBound_sub_k_eq_rounded (hk : 5 ≤ k) :
    Numerics.hunterBound k - k =
      hunterPathBaseNat k +
        hunterCorrectionNumerator k ⌈/⌉ Numerics.dNat k := by
  unfold Numerics.hunterBound hunterPathBaseNat hunterCorrectionNumerator
  have hkfac : k ≤ k.factorial := Nat.self_le_factorial k
  have hthree : 3 ≤ k.factorial + (k - 1).factorial + (k - 2).factorial := by
    have h0 := Nat.factorial_pos k
    have h1 := Nat.factorial_pos (k - 1)
    have h2 := Nat.factorial_pos (k - 2)
    omega
  omega

/-- Every actual image lies in a nonnegative integer layer over Hunter's path baseline. -/
theorem actualBaselineCore_ge_hunterPath
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    Numerics.hunterBound k - k ≤ actualBaselineCore P := by
  rw [hunterBound_sub_k_eq_rounded hk]
  exact actualBaselineCore_ge_roundedHunter hk hP

end PreimageChain

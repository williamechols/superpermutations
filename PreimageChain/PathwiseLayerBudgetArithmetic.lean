import PreimageChain.PathwiseBaseline

/-!
# Exact arithmetic form of the layer defect budget

This module rewrites `K_s = κ_k + s D_k` in the affine form used by the component
bookkeeping identity (29).
-/

namespace PreimageChain

open scoped Classical

variable {k s : ℕ}

/-- Integer cast of the natural `D_k`. -/
theorem dNat_cast_int (hk : 3 ≤ k) :
    (Numerics.dNat k : ℤ) = D (k : ℤ) := by
  unfold Numerics.dNat D
  have hprod : 1 ≤ (k - 1) * (k - 2) := by
    have hp : 0 < (k - 1) * (k - 2) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  rw [Nat.cast_sub hprod, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
  ring

/-- Integer cast of the rational-correction numerator. -/
theorem hunterCorrectionNumerator_cast_int (hk : 5 ≤ k) :
    (hunterCorrectionNumerator k : ℤ) =
      ((k - 2).factorial : ℤ) - ((k : ℤ) - 2) := by
  unfold hunterCorrectionNumerator
  have hle : k - 2 ≤ (k - 2).factorial := Nat.self_le_factorial (k - 2)
  rw [Nat.cast_sub hle, Nat.cast_sub (by omega : 2 ≤ k)]
  norm_num

/-- Integer cast of the integral part of Hunter's path baseline. -/
theorem hunterPathBaseNat_cast_int (hk : 5 ≤ k) :
    (hunterPathBaseNat k : ℤ) =
      (k.factorial : ℤ) + ((k - 1).factorial : ℤ) +
        ((k - 2).factorial : ℤ) - 3 := by
  unfold hunterPathBaseNat
  have hthree : 3 ≤ k.factorial + (k - 1).factorial + (k - 2).factorial := by
    have h0 := Nat.factorial_pos k
    have h1 := Nat.factorial_pos (k - 1)
    have h2 := Nat.factorial_pos (k - 2)
    omega
  rw [Nat.cast_sub hthree]
  push_cast
  ring

/-- The factorial identity underlying the definition of `κ_k`. -/
theorem layer_factorial_identity (hk : 5 ≤ k) :
    D (k : ℤ) *
        ((k.factorial : ℤ) + ((k - 1).factorial : ℤ) +
          ((k - 2).factorial : ℤ)) +
      ((k - 2).factorial : ℤ) =
        A (k : ℤ) * ((k - 1).factorial : ℤ) := by
  have hkEq : k = (k - 1) + 1 := by omega
  have hk1Eq : k - 1 = (k - 2) + 1 := by omega
  have hfacK :
      (k.factorial : ℤ) = (k : ℤ) * ((k - 1).factorial : ℤ) := by
    calc
      (k.factorial : ℤ) = (((k - 1) + 1).factorial : ℕ) := by rw [← hkEq]
      _ = (((k - 1) + 1) * (k - 1).factorial : ℕ) := by
        rw [Nat.factorial_succ]
      _ = (k : ℤ) * ((k - 1).factorial : ℤ) := by
        push_cast
        have hkCast : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by
          exact_mod_cast hkEq.symm
        rw [hkCast]
  have hfac1 :
      (((k - 1).factorial : ℕ) : ℤ) =
        ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by
    calc
      (((k - 1).factorial : ℕ) : ℤ) =
          ((((k - 2) + 1).factorial : ℕ) : ℤ) := by rw [← hk1Eq]
      _ = ((((k - 2) + 1) * (k - 2).factorial : ℕ) : ℤ) := by
        rw [Nat.factorial_succ]
      _ = ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by
        push_cast
        rw [Nat.cast_sub (by omega : 2 ≤ k)]
        ring
  rw [hfacK, hfac1]
  simp only [D, A]
  ring

/-- Exact integer value of the layer budget `K_s`. -/
theorem K_cast_affine
    (hk : 5 ≤ k) (s : ℕ) :
    (Numerics.K k s : ℤ) =
      D (k : ℤ) * ((hunterPathBound k : ℤ) + (s : ℤ)) +
        3 * D (k : ℤ) -
          A (k : ℤ) * ((k - 1).factorial : ℤ) +
            ((k : ℤ) - 2) := by
  let c := hunterCorrectionNumerator k ⌈/⌉ Numerics.dNat k
  have hBH :
      (hunterPathBound k : ℤ) =
        (hunterPathBaseNat k : ℤ) + (c : ℤ) := by
    unfold hunterPathBound
    rw [hunterBound_sub_k_eq_rounded hk]
    rfl
  have hq := hunterCorrectionNumerator_cast_int hk
  have hbase := hunterPathBaseNat_cast_int hk
  have hD := dNat_cast_int (by omega : 3 ≤ k)
  have hkappa :
      (Numerics.kappa k : ℤ) =
        D (k : ℤ) * (c : ℤ) -
          (((k - 2).factorial : ℤ) - ((k : ℤ) - 2)) := by
    unfold Numerics.kappa
    change ((Numerics.dNat k * c - hunterCorrectionNumerator k : ℕ) : ℤ) = _
    have hle : hunterCorrectionNumerator k ≤ Numerics.dNat k * c := by
      dsimp [c]
      simpa [nsmul_eq_mul] using
        (le_smul_ceilDiv (a := Numerics.dNat k)
          (b := hunterCorrectionNumerator k)
          (Numerics.dNat_pos (by omega : 3 ≤ k)))
    rw [Nat.cast_sub hle, Nat.cast_mul, hD, hq]
  have hfactor := layer_factorial_identity hk
  unfold Numerics.K
  rw [Nat.cast_add, Nat.cast_mul, hD, hkappa, hBH, hbase]
  push_cast
  nlinarith

end PreimageChain

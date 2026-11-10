import PreimageChain.LayerCorrectionAlgebra

/-!
# Arithmetic extraction of the closed portal lower bound

The component aggregate naturally yields the layer-specific ceiling `zRaw k s`.  This module
proves that the closed expression `zClosed k s = zZero k - (k-1)s` is never larger, so the
paper's stated `Z_s` follows from the exact aggregate without an additional structural input.
-/

namespace PreimageChain

open scoped Classical

/-- The distinguished-component constant changes by an exact denominator multiple per layer. -/
theorem C_layer_shift {k s : ℕ} (hk : 5 ≤ k) :
    Numerics.C k s = Numerics.C k 0 +
      ((k - 2) * Numerics.dNat k) * ((k - 1) * s) := by
  unfold Numerics.C Numerics.K
  rw [Numerics.dNat_add_one (by omega : 3 ≤ k)]
  ring

/-- The layer numerator is the zero-layer numerator with an exact denominator multiple removed. -/
theorem zRaw_numerator_layer_shift {k s : ℕ} (hk : 5 ≤ k) :
    (k - 2) * (k - 1).factorial - Numerics.C k s =
      ((k - 2) * (k - 1).factorial - Numerics.C k 0) -
        ((k - 2) * Numerics.dNat k) * ((k - 1) * s) := by
  rw [C_layer_shift hk, Nat.sub_add_eq]

/-- Removing a denominator multiple before taking a ceiling loses at most the same quotient. -/
theorem ceilDiv_sub_mul_lower
    {n d q : ℕ} (hd : 0 < d) :
    n ⌈/⌉ d - q ≤ (n - d * q) ⌈/⌉ d := by
  let c := n ⌈/⌉ d
  by_cases hq : q < c
  · have hcpos : 0 < c := lt_of_le_of_lt (Nat.zero_le q) hq
    have hlower : d * (c - 1) < n := by
      by_contra hnot
      have hnle : n ≤ d * (c - 1) := by omega
      have hceil : c ≤ c - 1 := by
        dsimp [c]
        exact (ceilDiv_le_iff_le_mul hd).2 hnle
      omega
    have hdqle : d * q ≤ d * (c - 1) :=
      Nat.mul_le_mul_left d (by omega)
    have hdqlt : d * q < n := lt_of_le_of_lt hdqle hlower
    have hreconstruct : n - d * q + d * q = n :=
      Nat.sub_add_cancel (Nat.le_of_lt hdqlt)
    by_contra hnot
    have hceilM : (n - d * q) ⌈/⌉ d ≤ c - q - 1 := by omega
    have hm : n - d * q ≤ d * (c - q - 1) :=
      (ceilDiv_le_iff_le_mul hd).1 hceilM
    have hadd := Nat.add_le_add_right hm (d * q)
    rw [hreconstruct] at hadd
    have hfactor : d * (c - q - 1) + d * q = d * (c - 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [hfactor] at hadd
    omega
  · have hle : c ≤ q := by omega
    dsimp [c] at hle ⊢
    simp [Nat.sub_eq_zero_of_le hle]

/-- The closed portal quantity is bounded by the direct layer ceiling. -/
theorem zClosed_le_zRaw {k s : ℕ} (hk : 5 ≤ k) :
    Numerics.zClosed k s ≤ Numerics.zRaw k s := by
  let n := (k - 2) * (k - 1).factorial - Numerics.C k 0
  let d := (k - 2) * Numerics.dNat k
  let q := (k - 1) * s
  have hd : 0 < d := Nat.mul_pos (by omega) (Numerics.dNat_pos (by omega))
  have hceil := ceilDiv_sub_mul_lower (n := n) (d := d) (q := q) hd
  unfold Numerics.zClosed Numerics.zZero Numerics.zRaw
  rw [zRaw_numerator_layer_shift (k := k) (s := s) hk]
  simpa [n, d, q] using hceil

/-- A natural aggregate inequality implies the paper's closed portal lower bound. -/
theorem zClosed_le_of_aggregate_nat
    {k s z : ℕ} (hk : 5 ≤ k)
    (haggregate :
      (k - 2) * (k - 1).factorial ≤
        Numerics.C k s + ((k - 2) * Numerics.dNat k) * z) :
    Numerics.zClosed k s ≤ z := by
  have hnum :
      (k - 2) * (k - 1).factorial - Numerics.C k s ≤
        ((k - 2) * Numerics.dNat k) * z := by omega
  have hd : 0 < (k - 2) * Numerics.dNat k :=
    Nat.mul_pos (by omega) (Numerics.dNat_pos (by omega))
  have hraw : Numerics.zRaw k s ≤ z := by
    unfold Numerics.zRaw
    exact (ceilDiv_le_iff_le_mul hd).2 hnum
  exact (zClosed_le_zRaw hk).trans hraw

end PreimageChain

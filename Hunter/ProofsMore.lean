/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsConfinement
import Hunter.ProofsReductions

/-!
# Greedy / arithmetic-reduction proofs (Hunter §6.4, §6.2)

This file proves the greedy-construction and recursion-interval arithmetic items of the
Hunter formalization: `prop2`, `prop3`, `thm2_equality` (base region), `greedy_g`, and
supporting items.  See `PROGRESS-more.md`.

It imports `Hunter.ProofsConfinement` and `Hunter.ProofsReductions` (a new file, so the
transitive `import Hunter.Statements` is not a cycle).  It never cites the sorried
`Hunter.<name>` statements — only `Hunter.Proved.*` witnesses and `Proofs*` helpers.
-/

namespace Hunter.ProofsMore

open Hunter
open scoped Classical

/-! ## `j_k` at `ℓ₀`, and the identity `A = a` -/

/-- `⌈ℓ₀/k⌉ = k²-3k+1` (exact, since `ℓ₀ = k(k²-3k+1)`). -/
theorem ceil_ell0_k {k : ℕ} (hk : 3 ≤ k) : (ell0 k) ⌈/⌉ k = k * k - 3 * k + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hdvd : ell0 (m + 3) = (m + 3) * (m * m + 3 * m + 1) := by
    simp only [ell0]
    rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
    have h1 : (m + 3) * (m + 2) * (m + 1) = m * m * m + 6 * m * m + 11 * m + 6 := by ring
    have h2 : (m + 3) * (m * m + 3 * m + 1) = m * m * m + 6 * m * m + 10 * m + 3 := by ring
    rw [h1, h2]; omega
  have hkq : (m + 3) * (m + 3) - 3 * (m + 3) + 1 = m * m + 3 * m + 1 := by
    have : (m + 3) * (m + 3) = m * m + 6 * m + 9 := by ring
    omega
  rw [hdvd, hkq]
  exact Hunter.ProofsReductions.cd_exact (m + 3) (m * m + 3 * m + 1) (by omega)

/-- `⌈ℓ₀/(k(k-1))⌉ = k-2`. -/
theorem ceil_ell0_kk {k : ℕ} (hk : 3 ≤ k) : (ell0 k) ⌈/⌉ (k * (k - 1)) = k - 2 := by
  have hd : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  have hkkk : k * (k - 1) * (k - 2) = (k * (k - 1)) * (k - 2) := by ring
  have hell0 : ell0 k = (k * (k - 1)) * (k - 2) - k := by rw [ell0, hkkk]
  rw [Nat.ceilDiv_eq_add_pred_div, hell0]
  set d := k * (k - 1) with hddef
  have hdk : k + 1 ≤ d := by
    rw [hddef]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 from by omega]
    nlinarith [Nat.zero_le m]
  have hdk2 : k ≤ d * (k - 2) :=
    le_trans (by omega) (Nat.mul_le_mul hdk (show 1 ≤ k - 2 by omega))
  have hrw : d * (k - 2) - k + d - 1 = d * (k - 2) + (d - k - 1) := by omega
  rw [hrw, Nat.mul_add_div (by omega : 0 < d), Nat.div_eq_of_lt (by omega : d - k - 1 < d)]
  omega

/-- `j_k(ℓ₀) = k²(k-2) - k - 4`. -/
theorem j_ell0 {k : ℕ} (hk : 3 ≤ k) : j k (ell0 k) = k ^ 2 * (k - 2) - k - 4 := by
  have hbase : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [ell0]; omega
  rw [j_base (Or.inl hbase), ceil_ell0_k hk, ceil_ell0_kk hk]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hell : ell0 (m + 3) = m * m * m + 6 * (m * m) + 10 * m + 3 := by
    simp only [ell0]
    rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
    have h1 : (m + 3) * (m + 2) * (m + 1) = m * m * m + 6 * (m * m) + 11 * m + 6 := by ring
    rw [h1]; omega
  have hc1 : (m + 3) * (m + 3) - 3 * (m + 3) + 1 = (m * m) + 3 * m + 1 := by
    have : (m + 3) * (m + 3) = (m * m) + 6 * m + 9 := by ring
    omega
  have hrhs : (m + 3) ^ 2 * (m + 1) = m * m * m + 7 * (m * m) + 15 * m + 9 := by ring
  rw [show m + 3 - 2 = m + 1 from by omega, hell, hc1, hrhs]
  omega

/-- The identity `A = a` in `ℝ`: `j_k(ℓ₀) + 3 = j_k(pivot) - k + 2`.  Both sides equal
`k³ - 2k² - k - 1`. -/
theorem A_eq_a {k : ℕ} (hk : 3 ≤ k) :
    (j k (ell0 k) : ℝ) + 3 = (j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2 := by
  rw [j_ell0 hk, Hunter.ProofsReductions.j_pivot hk]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hL : (m + 3) ^ 2 * (m + 3 - 2) - (m + 3) - 4 = m * m * m + 7 * m * m + 14 * m + 2 := by
    have : (m + 3) ^ 2 * (m + 3 - 2) = m * m * m + 7 * m * m + 15 * m + 9 := by
      rw [show m + 3 - 2 = m + 1 from by omega]; ring
    omega
  have hR : (m + 3) ^ 2 * (m + 3 - 2) - 3 = m * m * m + 7 * m * m + 15 * m + 6 := by
    have : (m + 3) ^ 2 * (m + 3 - 2) = m * m * m + 7 * m * m + 15 * m + 9 := by
      rw [show m + 3 - 2 = m + 1 from by omega]; ring
    omega
  rw [hL, hR]
  push_cast
  ring

/-! ## Unfolding the `j_k` recursion over the intervals -/

/-- `k ≤ pivot` (a positivity used to relate `ℓ₀` and `pivot`). -/
theorem k_le_pivot {k : ℕ} (hk : 3 ≤ k) : k ≤ k * (k - 1) * (k - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
  have h : (m + 3) * (m + 2) * (m + 1) = m * m * m + 6 * (m * m) + 11 * m + 6 := by ring
  rw [h]; omega

/-- `ℓ₀ > 0` for `k ≥ 3`. -/
theorem ell0_pos {k : ℕ} (hk : 3 ≤ k) : 0 < ell0 k := by
  rw [ell0]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
  have h : (m + 3) * (m + 2) * (m + 1) = m * m * m + 6 * (m * m) + 11 * m + 6 := by ring
  rw [h]; omega

/-- `ℓ₀ + k = pivot`. -/
theorem ell0_add_k {k : ℕ} (hk : 3 ≤ k) : ell0 k + k = k * (k - 1) * (k - 2) := by
  have h := k_le_pivot hk; rw [ell0]; omega

/-- Unfolding `j_k` over interval `t`: for `t·ℓ₀+k < ℓ ≤ (t+1)·ℓ₀+k`,
`j_k(ℓ) = t·(j_k(ℓ₀)+3) + j_k(ℓ − t·ℓ₀)`. -/
theorem j_unfold {k : ℕ} (hk : 3 ≤ k) (t : ℕ) {ℓ : ℕ}
    (h1 : t * ell0 k + k < ℓ) (h2 : ℓ ≤ (t + 1) * ell0 k + k) :
    j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k) := by
  have hE : 0 < ell0 k := ell0_pos hk
  have hpk : k ≤ k * (k - 1) * (k - 2) := k_le_pivot hk
  have hpiveq : ell0 k + k = k * (k - 1) * (k - 2) := ell0_add_k hk
  induction t generalizing ℓ with
  | zero => simp
  | succ n ih =>
    have hsm : (n + 1) * ell0 k = n * ell0 k + ell0 k := by rw [Nat.succ_mul]
    have hsm2 : (n + 1 + 1) * ell0 k = (n + 1) * ell0 k + ell0 k := by rw [Nat.succ_mul]
    -- the recursion branch applies to ℓ
    have hpiv : k * (k - 1) * (k - 2) < ℓ := by
      have hge : ell0 k ≤ (n + 1) * ell0 k := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hcond : ¬ (ℓ ≤ k * (k - 1) * (k - 2) ∨ k * (k - 1) * (k - 2) - k = 0) := by
      push Not
      refine ⟨by omega, ?_⟩
      have : k * (k - 1) * (k - 2) - k = ell0 k := by rw [ell0]
      omega
    rw [j_rec hcond]
    -- apply ih at ℓ - ell0 k
    have hb1 : n * ell0 k + k < ℓ - ell0 k := by omega
    have hb2 : ℓ - ell0 k ≤ (n + 1) * ell0 k + k := by omega
    have hih := ih (ℓ := ℓ - ell0 k) hb1 hb2
    rw [hih]
    have hsub : ℓ - ell0 k - n * ell0 k = ℓ - (n + 1) * ell0 k := by omega
    rw [hsub]
    ring

/-! ## `prop2` — the recursion-interval ratio minimum -/

/-- **prop2** — over interval `tℓ₀+k < ℓ ≤ (t+1)ℓ₀+k` the ratio `(j_k(ℓ)−k+2)/(ℓ−k)` is
minimized at the right endpoint `ℓ = (t+1)ℓ₀+k`.  Reduces to `prop1` at `ℓ' = ℓ − tℓ₀` via
the `A = a` identity. -/
theorem prop2 {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ} (ht : 1 ≤ t)
    (h1 : t * ell0 k + k < ℓ) (h2 : ℓ ≤ (t + 1) * ell0 k + k) :
    ((j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2) /
        ((((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
  have hE : 0 < ell0 k := ell0_pos hk
  have hsm : (t + 1) * ell0 k = t * ell0 k + ell0 k := by rw [Nat.succ_mul]
  have hpiveq : ell0 k + k = k * (k - 1) * (k - 2) := ell0_add_k hk
  -- ℓ' := ℓ - t·ℓ₀ lies in (k, pivot]
  have hℓ'lb : k < ℓ - t * ell0 k := by omega
  have hℓ'ub : ℓ - t * ell0 k ≤ k * (k - 1) * (k - 2) := by omega
  have hℓeq : ℓ = (ℓ - t * ell0 k) + t * ell0 k := by omega
  -- unfold j at ℓ and at the right endpoint R
  have hjℓ : j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k) := j_unfold hk t h1 h2
  have hR1 : t * ell0 k + k < (t + 1) * ell0 k + k := by omega
  have hjR : j k ((t + 1) * ell0 k + k)
      = t * (j k (ell0 k) + 3) + j k ((t + 1) * ell0 k + k - t * ell0 k) :=
    j_unfold hk t hR1 (le_refl _)
  have hRsub : (t + 1) * ell0 k + k - t * ell0 k = k * (k - 1) * (k - 2) := by omega
  rw [hRsub] at hjR
  -- real positivity
  have hEpos : (0 : ℝ) < (ell0 k : ℝ) := by exact_mod_cast hE
  have hcpos : (0 : ℝ) < ((ℓ - t * ell0 k : ℕ) : ℝ) - (k : ℝ) := by
    have : (k : ℝ) < ((ℓ - t * ell0 k : ℕ) : ℝ) := by exact_mod_cast hℓ'lb
    linarith
  -- pivot − k = ℓ₀ in ℝ
  have hPE : ((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ) = (ell0 k : ℝ) := by
    have hc : ((k * (k - 1) * (k - 2) : ℕ) : ℝ) = (ell0 k : ℝ) + (k : ℝ) := by
      rw [← hpiveq]; push_cast; ring
    rw [hc]; ring
  -- prop1 at ℓ'  ⟹  a·c ≤ b·E
  have hp1 := Hunter.Proved.prop1 hk hℓ'lb hℓ'ub
  rw [hPE] at hp1
  have hac : ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) *
        (((ℓ - t * ell0 k : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k (ℓ - t * ell0 k) : ℝ) - (k : ℝ) + 2) * (ell0 k : ℝ) := by
    rw [div_le_div_iff₀ hEpos hcpos] at hp1
    linarith [hp1]
  have hAa := A_eq_a hk
  -- rewrite the four parts of the goal
  have hnumR : (j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2
      = ((t : ℝ) + 1) * ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) := by
    have hcast : ((j k ((t + 1) * ell0 k + k) : ℕ) : ℝ)
        = (t : ℝ) * (((j k (ell0 k) : ℕ) : ℝ) + 3) + ((j k (k * (k - 1) * (k - 2)) : ℕ) : ℝ) := by
      rw [hjR]; push_cast; ring
    rw [hcast, hAa]; ring
  have hdenR : (((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ) = ((t : ℝ) + 1) * (ell0 k : ℝ) := by
    push_cast; ring
  have hnumℓ : (j k ℓ : ℝ) - (k : ℝ) + 2
      = (t : ℝ) * ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
        + ((j k (ℓ - t * ell0 k) : ℝ) - (k : ℝ) + 2) := by
    have hcast : ((j k ℓ : ℕ) : ℝ)
        = (t : ℝ) * (((j k (ell0 k) : ℕ) : ℝ) + 3) + ((j k (ℓ - t * ell0 k) : ℕ) : ℝ) := by
      rw [hjℓ]; push_cast; ring
    rw [hcast, hAa]; ring
  have hdenℓ : (ℓ : ℝ) - (k : ℝ)
      = (((ℓ - t * ell0 k : ℕ) : ℝ) - (k : ℝ)) + (t : ℝ) * (ell0 k : ℝ) := by
    have hℓcast : ((ℓ : ℕ) : ℝ) = ((ℓ - t * ell0 k : ℕ) : ℝ) + (t : ℝ) * (ell0 k : ℝ) := by
      have hle : t * ell0 k ≤ ℓ := by omega
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hℓcast]; ring
  rw [hnumR, hdenR, hnumℓ, hdenℓ]
  have hden1 : (0 : ℝ) < ((t : ℝ) + 1) * (ell0 k : ℝ) :=
    mul_pos (by positivity) hEpos
  have hden2 : (0 : ℝ) < (((ℓ - t * ell0 k : ℕ) : ℝ) - (k : ℝ)) + (t : ℝ) * (ell0 k : ℝ) :=
    add_pos_of_pos_of_nonneg hcpos (mul_nonneg (Nat.cast_nonneg t) hEpos.le)
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [mul_le_mul_of_nonneg_left hac (show (0 : ℝ) ≤ (t : ℝ) + 1 by positivity)]

/-! ## `prop3` — the ratio is globally minimized at the pivot -/

/-- The ratio at the right endpoint of any interval `t` equals the ratio at the pivot
(constancy of the endpoint ratio). -/
theorem ratio_R_eq_pivot {k : ℕ} (hk : 3 ≤ k) (t : ℕ) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      = ((j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2) /
          ((((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ)) := by
  have hE : 0 < ell0 k := ell0_pos hk
  have hEpos : (0 : ℝ) < (ell0 k : ℝ) := by exact_mod_cast hE
  have hEne : (ell0 k : ℝ) ≠ 0 := hEpos.ne'
  have ht1ne : ((t : ℝ) + 1) ≠ 0 := by positivity
  have hpiveq : ell0 k + k = k * (k - 1) * (k - 2) := ell0_add_k hk
  have hPE : ((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ) = (ell0 k : ℝ) := by
    have hc : ((k * (k - 1) * (k - 2) : ℕ) : ℝ) = (ell0 k : ℝ) + (k : ℝ) := by
      rw [← hpiveq]; push_cast; ring
    rw [hc]; ring
  have hR1 : t * ell0 k + k < (t + 1) * ell0 k + k := by
    have hsm : (t + 1) * ell0 k = t * ell0 k + ell0 k := by rw [Nat.succ_mul]
    omega
  have hRsub : (t + 1) * ell0 k + k - t * ell0 k = k * (k - 1) * (k - 2) := by
    have hsm : (t + 1) * ell0 k = t * ell0 k + ell0 k := by rw [Nat.succ_mul]
    omega
  have hjR : j k ((t + 1) * ell0 k + k)
      = t * (j k (ell0 k) + 3) + j k (k * (k - 1) * (k - 2)) := by
    have hh := j_unfold hk t hR1 (le_refl _)
    rwa [hRsub] at hh
  have hAa := A_eq_a hk
  have hnumR : (j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2
      = ((t : ℝ) + 1) * ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) := by
    have hcast : ((j k ((t + 1) * ell0 k + k) : ℕ) : ℝ)
        = (t : ℝ) * (((j k (ell0 k) : ℕ) : ℝ) + 3) + ((j k (k * (k - 1) * (k - 2)) : ℕ) : ℝ) := by
      rw [hjR]; push_cast; ring
    rw [hcast, hAa]; ring
  have hdenR : (((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ) = ((t : ℝ) + 1) * (ell0 k : ℝ) := by
    push_cast; ring
  rw [hPE, hnumR, hdenR]
  field_simp

/-- **prop3** — the ratio `(j_k(ℓ)−k+2)/(ℓ−k)` over all `ℓ > k` is minimized at the pivot.
For `ℓ ≤ pivot` this is `prop1`; for `ℓ > pivot` we place `ℓ` in interval `t` and combine
`prop2` with the endpoint-constancy `ratio_R_eq_pivot`. -/
theorem prop3 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
  by_cases hle : ℓ ≤ k * (k - 1) * (k - 2)
  · exact Hunter.Proved.prop1 hk h hle
  · push Not at hle
    have hE : 0 < ell0 k := ell0_pos hk
    have hpiveq : ell0 k + k = k * (k - 1) * (k - 2) := ell0_add_k hk
    set t := (ℓ - k - 1) / ell0 k with htdef
    have hcomm : ell0 k * t = t * ell0 k := mul_comm _ _
    have hdm := Nat.div_add_mod (ℓ - k - 1) (ell0 k)
    rw [← htdef] at hdm
    have hml := Nat.mod_lt (ℓ - k - 1) hE
    have h1 : t * ell0 k + k < ℓ := by rw [← hcomm]; omega
    have h2 : ℓ ≤ (t + 1) * ell0 k + k := by
      have hsm : (t + 1) * ell0 k = ell0 k * t + ell0 k := by rw [Nat.succ_mul, hcomm]
      omega
    have ht1 : 1 ≤ t := by
      have hb : ell0 k ≤ ℓ - k - 1 := by omega
      exact (Nat.one_le_div_iff hE).mpr hb
    rw [ratio_R_eq_pivot hk t]
    exact prop2 hk ht1 h1 h2

/-! ## `eq_weak` — factorial-asymptotic form (the core `coeff·k!` bound) -/

/-- The leading `coeff k · k!` dominates the factorial expansion
`k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)!` for `k ≥ 6`.  The gap equals
`(7k−18)·(k−6)!/(k²−3k+1) ≥ 0`; the whole thing reduces to `7k ≥ 18`. -/
theorem coeff_fact_bound {k : ℕ} (hk : 6 ≤ k) :
    (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ)
      ≤ coeff k * (k.factorial : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 from rfl, show m + 6 - 2 = m + 4 from rfl,
    show m + 6 - 4 = m + 2 from rfl, show m + 6 - 5 = m + 1 from rfl]
  have e2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have e3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
  have e4 : (m + 4).factorial = (m + 4) * (m + 3).factorial := Nat.factorial_succ (m + 3)
  have e5 : (m + 5).factorial = (m + 5) * (m + 4).factorial := Nat.factorial_succ (m + 4)
  have e6 : (m + 6).factorial = (m + 6) * (m + 5).factorial := Nat.factorial_succ (m + 5)
  have big4 : (m + 4).factorial = (m + 4) * (m + 3) * (m + 2) * (m + 1).factorial := by
    rw [e4, e3, e2]; ring
  have big5 : (m + 5).factorial = (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1).factorial := by
    rw [e5, e4, e3, e2]; ring
  have big6 : (m + 6).factorial
      = (m + 6) * (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1).factorial := by
    rw [e6, e5, e4, e3, e2]; ring
  have hFpos : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast (m + 1).factorial_pos
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hden : (0 : ℝ) < (m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19 := by positivity
  have h6 : ((m : ℝ) + 6) ≠ 0 := by positivity
  have h51 : ((m : ℝ) + 6 - 1) ≠ 0 := (show (0 : ℝ) < (m : ℝ) + 6 - 1 by nlinarith [hm]).ne'
  have h42 : ((m : ℝ) + 6 - 2) ≠ 0 := (show (0 : ℝ) < (m : ℝ) + 6 - 2 by nlinarith [hm]).ne'
  have hEne : ((m : ℝ) + 6) * ((m : ℝ) + 6 - 1) * ((m : ℝ) + 6 - 2) - ((m : ℝ) + 6) ≠ 0 := by
    have : ((m : ℝ) + 6) * ((m : ℝ) + 6 - 1) * ((m : ℝ) + 6 - 2) - ((m : ℝ) + 6)
        = ((m : ℝ) + 6) * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19) := by ring
    rw [this]; positivity
  have hq : (m : ℝ) ^ 2 + 9 * (m : ℝ) + 19 ≠ 0 := by positivity
  -- decomposition of coeff·k!, multiplied through by (m²+9m+19) to avoid a trailing fraction
  have hcoeffRHS : coeff (m + 6) * ((m + 6).factorial : ℝ)
        * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19)
      = (((m + 6).factorial : ℝ) + ((m + 5).factorial : ℝ) + ((m + 4).factorial : ℝ))
          * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19)
        + ((m + 4) * (m + 3) * (m + 2) : ℝ) * ((m + 1).factorial : ℝ) := by
    rw [coeff, big6, big5, big4]
    push_cast
    rw [show ((m : ℝ) + 6) * ((m : ℝ) + 6 - 1) * ((m : ℝ) + 6 - 2) - ((m : ℝ) + 6)
        = ((m : ℝ) + 6) * ((m : ℝ) ^ 2 + 9 * (m : ℝ) + 19) from by ring]
    field_simp
    ring
  -- prove the goal after multiplying by the positive denominator
  have hmul : (((m + 6).factorial : ℝ) + ((m + 5).factorial : ℝ) + ((m + 4).factorial : ℝ)
        + ((m + 2).factorial : ℝ) - 2 * ((m + 1).factorial : ℝ))
        * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19)
      ≤ coeff (m + 6) * ((m + 6).factorial : ℝ)
        * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19) := by
    rw [hcoeffRHS, e2]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right
      (show (m : ℝ) * ((m : ℝ) * (m : ℝ) + 9 * (m : ℝ) + 19)
          ≤ ((m : ℝ) + 4) * ((m : ℝ) + 3) * ((m : ℝ) + 2) by nlinarith [hm]) hFpos.le, hFpos, hm]
  exact le_of_mul_le_mul_right hmul hden

end Hunter.ProofsMore

/-! ## The `Hunter.Proved` targets (verbatim types from `Statements.lean`) -/

namespace Hunter.Proved

open Hunter

/-- **prop2** — verbatim target. -/
theorem prop2 {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ} (ht : 1 ≤ t)
    (h1 : t * ell0 k + k < ℓ) (h2 : ℓ ≤ (t + 1) * ell0 k + k) :
    ((j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2) /
        ((((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  Hunter.ProofsMore.prop2 hk ht h1 h2

/-- **prop3** — verbatim target. -/
theorem prop3 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  Hunter.ProofsMore.prop3 hk h

/-- **eq_weak** (verbatim target shape), delivered from the `thm1v1`-conclusion as an
explicit hypothesis `hthm1` (there is no unconditional `L*(k)` lower bound available; the
`coeff·k!` bound is the `thm1v1` package proved with-hypotheses on the reductions track).
The factorial-asymptotic content — `coeff·k! ≥ k!+(k−1)!+(k−2)!+(k−4)!−2(k−5)!` — is proved
unconditionally as `ProofsMore.coeff_fact_bound`, so `C = max C₁ 0` (indeed the `(k−6)!`
slack is not even needed beyond absorbing the `+k−C₁` term). -/
theorem eq_weak_of_thm1v1
    (hthm1 : ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) := by
  obtain ⟨C1, k1, hb⟩ := hthm1
  refine ⟨max C1 0, max k1 6, fun k hk => ?_⟩
  have hk1 : k1 ≤ k := le_trans (le_max_left _ _) hk
  have hk6 : 6 ≤ k := le_trans (le_max_right _ _) hk
  have hC0 : (0 : ℝ) ≤ max C1 0 := le_max_right _ _
  have hCge : C1 ≤ max C1 0 := le_max_left _ _
  have hb' := hb k hk1
  have hcf := Hunter.ProofsMore.coeff_fact_bound hk6
  have hfac6 : (1 : ℝ) ≤ ((k - 6).factorial : ℝ) := by exact_mod_cast (k - 6).factorial_pos
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hp : max C1 0 ≤ max C1 0 * ((k - 6).factorial : ℝ) := le_mul_of_one_le_right hC0 hfac6
  linarith [hb', hcf, hp, hCge, hk0]

end Hunter.Proved

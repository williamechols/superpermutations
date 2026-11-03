/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Statements

/-!
# Explicit pointwise consequences of Hunter's bound

The headline theorem is packaged asymptotically, but the completed reduction proves the exact
per-`k` pivot inequality used below.  This module exposes that stronger public interface at the
honest word-level minimum `Ssuper`, then certifies its first four integer consequences.
-/

namespace Hunter

open scoped Classical

/-- The exact pointwise lower bound delivered by the completed reduction, stated for the genuine
minimum superpermutation length.  This is the coefficient term together with its exact pivot
correction, before rounding to an integer. -/
theorem superperm_length_ge_hunterPointwise {k : ℕ} (hk : 3 ≤ k) :
    (Ssuper k : ℝ) ≥
      (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3
        + coeff k *
          ((k.factorial : ℝ) - (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))
        + (k : ℝ) := by
  have hpivot : HasExitlessPath k (k * (k - 1) * (k - 2)) :=
    Proved.hasExitlessPath_pivot k hk
  have hPpos : 0 < k * (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 from by omega,
      show m + 3 - 2 = m + 1 from by omega]
    positivity
  have hi : iExitless k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 := by
    rw [thm2_equality hk hPpos (le_refl _) hpivot,
      ProofsReductions.j_pivot hk]
  have hL := proof_thm1v2 hk hpivot
  rw [hi, ProofsReductions.castI hk, ProofsReductions.castP (by omega),
    ProofsReductions.ratio_eq_coeff hk] at hL
  rw [← Proved.bridge_Lstar_eq_Ssuper (show 1 ≤ k by omega), lstar_eq]
  push_cast
  linarith

/-- The exact reduction recovers the known optimum `S(5) = 153` from below. -/
theorem superperm_length_ge_5_153 : 153 ≤ Ssuper 5 := by
  have h := superperm_length_ge_hunterPointwise (k := 5) (by omega)
  by_contra hnot
  have hn : Ssuper 5 ≤ 152 := by omega
  have hr : (Ssuper 5 : ℝ) ≤ 152 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

/-- Pointwise consequence at six symbols. -/
theorem superperm_length_ge_6_869 : 869 ≤ Ssuper 6 := by
  have h := superperm_length_ge_hunterPointwise (k := 6) (by omega)
  by_contra hnot
  have hn : Ssuper 6 ≤ 868 := by omega
  have hr : (Ssuper 6 : ℝ) ≤ 868 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

/-- Pointwise consequence at seven symbols. -/
theorem superperm_length_ge_7_5888 : 5888 ≤ Ssuper 7 := by
  have h := superperm_length_ge_hunterPointwise (k := 7) (by omega)
  by_contra hnot
  have hn : Ssuper 7 ≤ 5887 := by omega
  have hr : (Ssuper 7 : ℝ) ≤ 5887 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

/-- Pointwise consequence at eight symbols. -/
theorem superperm_length_ge_8_46103 : 46103 ≤ Ssuper 8 := by
  have h := superperm_length_ge_hunterPointwise (k := 8) (by omega)
  by_contra hnot
  have hn : Ssuper 8 ≤ 46102 := by omega
  have hr : (Ssuper 8 : ℝ) ≤ 46102 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

end Hunter

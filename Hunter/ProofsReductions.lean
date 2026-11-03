/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Defs
import Hunter.Appendix

/-!
# Proofs — Reductions / arithmetic track (Hunter §6.2–§6.4 + headline forms)

Proofs of the reductions/arithmetic targets of `Hunter/Statements.lean`, proved here as
`Hunter.Proved.<name>`.  Cross-track dependencies (the graph-theoretic spine: `b1`, `b2`,
`red_pstar`, `red_R`, `prp_Xkcomps`, `thm2`, `greedy_g`, …) are taken as **explicit
hypotheses** with the exact `Statements.lean` types, never citing the sorried theorems (so
the axiom audit stays clean).  See `PROGRESS-reductions.md` for the per-target status and the
full hypothesis graph.
-/

namespace Hunter.ProofsReductions

open List
open scoped Classical
open Hunter

/-! ## ℕ arithmetic helpers -/

/-- Exact ceiling-division: `(d * q) ⌈/⌉ d = q` for `d > 0`. -/
theorem cd_exact (d q : ℕ) (hd : 0 < d) : (d * q) ⌈/⌉ d = q := by
  rw [Nat.ceilDiv_eq_add_pred_div, show d * q + d - 1 = (d - 1) + d * q from by omega,
    Nat.add_mul_div_left (d - 1) q hd, Nat.div_eq_of_lt (by omega : d - 1 < d), Nat.zero_add]

/-- Ceiling-division real lower bound (multiplied form): `n ≤ d · ⌈n/d⌉` cast to ℝ. -/
theorem ceilDiv_ge_mul (n d : ℕ) (hd : 0 < d) : (n : ℝ) ≤ (d : ℝ) * ((n ⌈/⌉ d : ℕ) : ℝ) := by
  have h : n ≤ d * (n ⌈/⌉ d) := by
    have h0 := (ceilDiv_le_iff_le_smul hd).mp (le_refl (n ⌈/⌉ d))
    simpa [smul_eq_mul] using h0
  calc (n : ℝ) ≤ ((d * (n ⌈/⌉ d) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (d : ℝ) * ((n ⌈/⌉ d : ℕ) : ℝ) := by push_cast; ring

/-- `j_k` at the pivot `ℓ = k(k−1)(k−2)` equals `k²(k−2) − 3` (the exact optimum value).
This is the arithmetic content of the display fact `j-at-pivot`; reproved here as a helper
for the headline packaging (the target `j_at_pivot` itself is owned by the exitless track). -/
theorem j_pivot {k : ℕ} (hk : 3 ≤ k) :
    j k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 := by
  have hc1 : (k * (k - 1) * (k - 2)) ⌈/⌉ k = (k - 1) * (k - 2) := by
    rw [mul_assoc]; exact cd_exact k ((k - 1) * (k - 2)) (by omega)
  have hc2 : (k * (k - 1) * (k - 2)) ⌈/⌉ (k * (k - 1)) = (k - 2) :=
    cd_exact (k * (k - 1)) (k - 2) (Nat.mul_pos (by omega) (by omega))
  have hsum : k * (k - 1) * (k - 2) + (k - 1) * (k - 2) + (k - 2) = k ^ 2 * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 2 = m + 1 := by omega
    rw [e1, e2]; ring
  rw [j_base (Or.inl (le_refl _)), hc1, hc2, hsum]

/-! ## Real cast helpers (kill ℕ truncated subtraction) -/

/-- Cast of the pivot `k(k−1)(k−2)` into ℝ (for `k ≥ 2`). -/
theorem castP {k : ℕ} (hk : 2 ≤ k) :
    ((k * (k - 1) * (k - 2) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
  push_cast; ring

/-- Cast of the optimum value `k²(k−2) − 3` into ℝ (for `k ≥ 3`). -/
theorem castI {k : ℕ} (hk : 3 ≤ k) :
    ((k ^ 2 * (k - 2) - 3 : ℕ) : ℝ) = (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [show m + 3 - 2 = m + 1 from by omega]
  have hge : 3 ≤ (m + 3) ^ 2 * (m + 1) := by nlinarith [Nat.zero_le m]
  rw [Nat.cast_sub hge]; push_cast; ring

/-! ## Real arithmetic core: the pivot ratio equals `coeff k`, and the O(1) tail -/

/-- Positivity of the denominator `D = k(k−1)(k−2) − k` (`= k(k²−3k+1)`) for `k ≥ 3`. -/
theorem D_pos {k : ℕ} (hk : 3 ≤ k) :
    (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  push_cast
  nlinarith [hm, mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hm]

/-- **Key identity**: the pivot cost-ratio `(i_k(P)−k+2)/(P−k)` — with the exact value
`i_k(P) = k²(k−2)−3` and `P = k(k−1)(k−2)` — equals the leading coefficient `coeff k`
of the main theorem.  (Verified: `(k³−2k²−k−1)(k−1) = k⁴−3k³+k²+1`.)

Proof pattern: `set D` keeps `field_simp` from factoring the denominator; we clear the
fractions with `D` atomic, then `rw` in `D`'s value and finish with `ring`. -/
theorem ratio_eq_coeff {k : ℕ} (hk : 3 ≤ k) :
    ((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2) /
        ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ)) = coeff k := by
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) - 1 ≠ 0 := by nlinarith
  have hDne : (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) ≠ 0 := (D_pos hk).ne'
  rw [coeff]
  set D := (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) with hDdef
  field_simp
  rw [hDdef]
  ring

/-- **The O(1) tail**: `i_k(P) − ratio·P ≥ −4`, i.e. the additive slack in
proof-thm1v2's bound is bounded.  (Reduces to `k(k−1)(k−3) ≥ 0`.) -/
theorem tail_ge {k : ℕ} (hk : 3 ≤ k) :
    ((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3) -
        (((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2) /
          ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ))) *
          ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) ≥ -4 := by
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hDpos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) := D_pos hk
  rw [ge_iff_le, ← sub_nonneg]
  set D := (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) with hDdef
  have hDne : D ≠ 0 := hDpos.ne'
  have hEq : (((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3) -
        (((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2) / D) *
          ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))) - (-4)
      = (((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 + 4) * D
          - ((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2)
            * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))) / D := by
    field_simp
    ring
  rw [hEq]
  apply div_nonneg _ (le_of_lt hDpos)
  rw [hDdef]
  nlinarith [hk3, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ))
    (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)) (by linarith : (0:ℝ) ≤ (k:ℝ) - 3)]

/-- **Packaging lemma**: from proof-thm1v2's exact per-`k` bound (`hL`) plus the pivot value
`i_k(P) = k²(k−2)−3` (`hi`, from thm2-equality + `j_pivot`), obtain `L(k) ≥ coeff k · k! − 4`. -/
theorem bound_pack {k : ℕ} (hk : 3 ≤ k)
    (hi : iExitless k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3)
    (hL : (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
      + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - 4 := by
  rw [hi, castI hk, castP (by omega)] at hL
  apply le_trans _ hL
  rw [ratio_eq_coeff hk]
  have htl := tail_ge hk
  rw [ratio_eq_coeff hk] at htl
  have hexp : ((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3)
      + coeff k * ((k.factorial : ℝ) - (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))
      = coeff k * (k.factorial : ℝ)
        + (((k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3)
          - coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))) := by ring
  rw [hexp]
  linarith [htl]

end Hunter.ProofsReductions

/-! ## The `Hunter.Proved` targets (headline forms, packaged from the spine) -/

namespace Hunter.Proved

open Hunter
open Hunter.ProofsReductions

/-- **thm2 → thm1v2** (conditional main theorem), delivered as a **hypothesis chain**: on top
of Theorem 2 (`hthm2`, `hthm2eq`) it consumes proof-thm1v2's exact per-`k` bound (`hproof`,
the §6.4 reduction output, owned as a chain by `Hunter.Proved.proof_thm1v2`) and the pivot
existence guard (`hexists`, from `greedy_g`).  Conclusion is `thm1v2` verbatim. -/
theorem thm2_imp_thm1v2
    (_hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C := by
  refine ⟨4, 3, fun k hk => ?_⟩
  have hex := hexists k hk
  have hL := hproof k hk hex
  have hpos : 0 < k * (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]; positivity
  have hi : iExitless k (k * (k - 1) * (k - 2)) = j k (k * (k - 1) * (k - 2)) :=
    hthm2eq k _ hk hpos (le_refl _) hex
  rw [j_pivot hk] at hi
  exact bound_pack hk hi hL

/-- **thm1v2** — the real theorem, delivered as the same hypothesis chain as
`thm2_imp_thm1v2`. -/
theorem thm1v2
    (hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  thm2_imp_thm1v2 hthm2 hthm2eq hproof hexists

/-- **thm1v1** — the superpermutation form, from `thm1v2` via `L*(k) = L(k) + k`. -/
theorem thm1v1
    (hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C := by
  obtain ⟨C, k₀, h⟩ := thm2_imp_thm1v2 hthm2 hthm2eq hproof hexists
  refine ⟨C, k₀, fun k hk => ?_⟩
  have hb := h k hk
  have hls : (Lstar k : ℝ) = (L k : ℝ) + (k : ℝ) := by rw [lstar_eq]; push_cast; ring
  rw [hls]; linarith

/-- **subprob2-comp** — `main_version.tex` §6.4 l.802.  The subproblem-2 quantity splits
along the `j_k` recursion.  Pure algebra given the recursion unfolding `hjrec`. -/
theorem subprob2_comp {k : ℕ} (_hk : 3 ≤ k) {t ℓ : ℕ} (R : ℝ) (hle : t * ell0 k ≤ ℓ)
    (hjrec : j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k)) :
    (j k ℓ : ℝ) - R * (ℓ : ℝ)
      = ((t : ℝ) * ((j k (ell0 k) : ℝ) + 3) - R * (t : ℝ) * (ell0 k : ℝ))
        + ((j k (ℓ - t * ell0 k) : ℝ) - R * (((ℓ - t * ell0 k : ℕ) : ℝ))) := by
  have hcast : ((ℓ - t * ell0 k : ℕ) : ℝ) = (ℓ : ℝ) - (t : ℝ) * (ell0 k : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [hjrec]
  push_cast
  rw [hcast]
  ring

/-- **proof-thm1v2** — `main_version.tex` §6.4 l.821.  The §6.2–§6.4 reduction assembly,
delivered as a **hypothesis chain**.  The abstract `gInner : ℝ → ℝ` stands for the inner
minimum `min_ℓ{ i_k(ℓ) − r·ℓ }`; the hypotheses encode the Statements-level facts:

* `hb2red` — `L(k) ≥ R_k·k! + gInner(R_k)`  (from `b2` + `red_pstar`);
* `hg_mono` — `r ↦ r·k! + gInner(r)` is nondecreasing  (each affine term has slope
  `k!−ℓ ≥ 0`; this is the monotonicity of `g` that makes the take23 `≥`-reductions suffice,
  `DIGEST.md` §5.2);
* `hgInner_eval` — at the pivot ratio `r_P`, the inner min is attained at `ℓ = P`, i.e.
  `gInner(r_P) = i_k(P) − r_P·P`  (from `prop4`/`subprob*`);
* `hRk_ge` — `r_P ≤ R_k`  (from `red_R` + `prop4`).

Then `L ≥ g(R_k) ≥ g(r_P) = i_k(P) + r_P·(k!−P)`, which is the claimed bound. -/
theorem proof_thm1v2 {k : ℕ} (_hk : 3 ≤ k)
    (_hpivot : HasExitlessPath k (k * (k - 1) * (k - 2)))
    (gInner : ℝ → ℝ)
    (hb2red : (L k : ℝ) ≥ Rk k * (k.factorial : ℝ) + gInner (Rk k))
    (hg_mono : ∀ r s : ℝ, r ≤ s →
        r * (k.factorial : ℝ) + gInner r ≤ s * (k.factorial : ℝ) + gInner s)
    (hgInner_eval : gInner (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
          / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        = (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          - (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
              / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k * (k - 1) * (k - 2) : ℕ) : ℝ))
    (hRk_ge : ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
          / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)) ≤ Rk k) :
    (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
      + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) := by
  set rP : ℝ := ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
      / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)) with hrP
  calc (L k : ℝ) ≥ Rk k * (k.factorial : ℝ) + gInner (Rk k) := hb2red
    _ ≥ rP * (k.factorial : ℝ) + gInner rP := hg_mono rP (Rk k) hRk_ge
    _ = (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + rP * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) := by
        rw [hgInner_eval]; ring

/-- **red-p\*** — take23 l.736 (`≥` form).  Delivered as a **hypothesis chain**: `hXk` is
`prp_Xkcomps` (`𝒳'_k` = all strongly exitless paths) and `hne` is nonemptiness of `𝒳'_k`
(from `greedy_g`).  Proof: every `p ∈ 𝒳'_k` is exitless with `w(p) ≥ i_k(|p|)`, so
`w(p) − r|p| ≥ i_k(|p|) − r|p| ≥ sInf(RHS)`; the RHS set is bounded below because exitless
paths have `≤ |V(𝒮_k)|` vertices. -/
theorem red_pstar {k : ℕ} {r : ℝ} (hr : 1 < r)
    (hXk : Xk' k = {p : HPath k | p.StronglyExitless}) (hne : (Xk' k).Nonempty) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hN : ∀ ℓ, HasExitlessPath k ℓ → ℓ ≤ Fintype.card (Vtx k) := by
    rintro ℓ ⟨p, _, hpℓ⟩
    rw [← hpℓ]; exact p.nodup.length_le_card
  have hBbb : BddBelow {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} := by
    refine ⟨-r * (Fintype.card (Vtx k) : ℝ), ?_⟩
    rintro q ⟨ℓ, hℓ, rfl⟩
    have hcard : (ℓ : ℝ) ≤ (Fintype.card (Vtx k) : ℝ) := by exact_mod_cast hN ℓ hℓ
    have hi : (0 : ℝ) ≤ (iExitless k ℓ : ℝ) := Nat.cast_nonneg _
    nlinarith [hcard, hi, hr0]
  rw [ge_iff_le]
  apply le_csInf
  · obtain ⟨p, hp⟩ := hne
    exact ⟨(p.wtP : ℝ) - r * (p.numVerts : ℝ), p, hp, rfl⟩
  · rintro a ⟨p, hp, rfl⟩
    have hse : p.StronglyExitless := by rw [hXk] at hp; exact hp
    have hex : p.Exitless := hse.1
    have hmem : ((iExitless k p.numVerts : ℝ) - r * (p.numVerts : ℝ)) ∈
        {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
      ⟨p.numVerts, ⟨p, hex, rfl⟩, rfl⟩
    have hle_i : iExitless k p.numVerts ≤ p.wtP := Nat.sInf_le ⟨p, hex, rfl, rfl⟩
    have hicast : (iExitless k p.numVerts : ℝ) ≤ (p.wtP : ℝ) := by exact_mod_cast hle_i
    calc sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)}
          ≤ (iExitless k p.numVerts : ℝ) - r * (p.numVerts : ℝ) := csInf_le hBbb hmem
      _ ≤ (p.wtP : ℝ) - r * (p.numVerts : ℝ) := by linarith

/-- **prop4** — `main_version.tex` §6.4 l.740.  Delivered as a **hypothesis chain** from
`prop3` (`hprop3`, the `j_k`-ratio minimum at the pivot), `thm2` (`hthm2`, `j_k ≤ i_k`) and
`thm2_equality` at the pivot (`hthm2eq`).  Transfers the ratio-minimum from `j_k` to `i_k`:
`ratio_i(P) = ratio_j(P) ≤ ratio_j(ℓ) ≤ ratio_i(ℓ)`. -/
theorem prop4 {k : ℕ} (_hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) (hex : HasExitlessPath k ℓ)
    (_hpivot : HasExitlessPath k (k * (k - 1) * (k - 2)))
    (hprop3 : ∀ m, k < m →
        ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
            (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
          ≤ ((j k m : ℝ) - (k : ℝ) + 2) / ((m : ℝ) - (k : ℝ)))
    (hthm2 : ∀ m, HasExitlessPath k m → j k m ≤ iExitless k m)
    (hthm2eq : iExitless k (k * (k - 1) * (k - 2)) = j k (k * (k - 1) * (k - 2))) :
    ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
  have hd : (0 : ℝ) < (ℓ : ℝ) - (k : ℝ) := by
    have : (k : ℝ) < (ℓ : ℝ) := by exact_mod_cast h
    linarith
  have hji : (j k ℓ : ℝ) ≤ (iExitless k ℓ : ℝ) := by exact_mod_cast hthm2 ℓ hex
  have step1 : ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))
      ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
    (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  have step2 := hprop3 ℓ h
  have step3 : ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      = ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)) := by rw [hthm2eq]
  rw [step3]
  linarith [step1, step2]

/-- **prop1** — `main_version.tex` §6.4 l.734.  Over the base interval `k < ℓ ≤ P`, the
`j_k`-ratio `(j_k(ℓ)−k+2)/(ℓ−k)` is minimized at the right endpoint `ℓ = P`.  **Proved
outright.**  Key: on the base interval `ratio(ℓ) = 1 + (⌈ℓ/k⌉+⌈ℓ/(k(k−1))⌉−1)/(ℓ−k)`, and
the floor bound `⌈ℓ/k⌉+⌈ℓ/(k(k−1))⌉ ≥ ℓ/(k−1)` (both ceilings exact at `ℓ=P`) makes the
whole thing reduce to `ℓ ≤ P`. -/
theorem prop1 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h1 : k < ℓ) (h2 : ℓ ≤ k * (k - 1) * (k - 2)) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) := by linarith
  have hPk : (0 : ℝ) < ((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ) := by
    rw [castP (by omega)]; exact D_pos hk
  have hℓk : (0 : ℝ) < (ℓ : ℝ) - (k : ℝ) := by
    have : (k : ℝ) < (ℓ : ℝ) := by exact_mod_cast h1
    linarith
  have hjP : (j k (k * (k - 1) * (k - 2)) : ℝ) = (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 := by
    rw [j_pivot hk, castI hk]
  have hjℓnat : j k ℓ = ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3 := j_base (Or.inl h2)
  have hsum3 : 3 ≤ ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) := by omega
  have hjℓ : (j k ℓ : ℝ)
      = (ℓ : ℝ) + ((ℓ ⌈/⌉ k : ℕ) : ℝ) + ((ℓ ⌈/⌉ (k * (k - 1)) : ℕ) : ℝ) - 3 := by
    rw [hjℓnat, Nat.cast_sub hsum3]; push_cast; ring
  have hc1 : (ℓ : ℝ) ≤ (k : ℝ) * ((ℓ ⌈/⌉ k : ℕ) : ℝ) := ceilDiv_ge_mul ℓ k (by omega)
  have hc2 : (ℓ : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) * ((ℓ ⌈/⌉ (k * (k - 1)) : ℕ) : ℝ) := by
    have hh := ceilDiv_ge_mul ℓ (k * (k - 1)) (Nat.mul_pos (by omega) (by omega))
    rwa [show ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) from by
      push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring] at hh
  -- combine the two ceiling bounds: ℓ ≤ (k-1)·(⌈ℓ/k⌉ + ⌈ℓ/(k(k-1))⌉)
  have hC : (ℓ : ℝ) ≤ ((k : ℝ) - 1) *
      (((ℓ ⌈/⌉ k : ℕ) : ℝ) + ((ℓ ⌈/⌉ (k * (k - 1)) : ℕ) : ℝ)) := by
    have e1 : ((k : ℝ) - 1) * (ℓ : ℝ) ≤ ((k : ℝ) - 1) * ((k : ℝ) * ((ℓ ⌈/⌉ k : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hc1 (by linarith)
    nlinarith [e1, hc2, hk1]
  have hℓP : (ℓ : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) := by
    rw [← castP (by omega)]; exact_mod_cast h2
  rw [div_le_div_iff₀ hPk hℓk, hjP, hjℓ, castP (by omega)]
  nlinarith [hC, hℓP, hPk, hℓk, mul_pos hPk (show (0 : ℝ) < (k : ℝ) - 1 by linarith),
    mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith) (sub_nonneg.mpr hC),
    mul_nonneg (le_of_lt hPk) (sub_nonneg.mpr hℓP),
    mul_nonneg (sub_nonneg.mpr hℓP) (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith)]

/-- **red-R** — take23 l.744 (`≥` form).  Delivered as a **hypothesis chain**: `hkey`
encodes the `p_u`-extension (each non-spanning `𝒳'_k` cost-ratio dominates the `i_k`-ratio at
`ℓ = |p|+k`), `hne` is nonemptiness of the `R_k` value set, and `hBddR` is the (finite-regime)
lower-boundedness of the `i_k`-ratio set.  Proof is the `sInf`-monotone comparison, exactly as
for `red_pstar`. -/
theorem red_R {k : ℕ}
    (hkey : ∀ p, p ∈ Xk' k → p.numVerts ≤ k.factorial - k →
        k < p.numVerts + k ∧ HasExitlessPath k (p.numVerts + k) ∧
          ((iExitless k (p.numVerts + k) : ℝ) - (k : ℝ) + 2) /
              (((p.numVerts + k : ℕ) : ℝ) - (k : ℝ))
            ≤ (pValue p : ℝ) / (p.numVerts : ℝ))
    (hne : ∃ p, p ∈ Xk' k ∧ p.numVerts ≤ k.factorial - k)
    (hBddR : BddBelow {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
        q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))}) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} := by
  rw [ge_iff_le, Rk]
  apply le_csInf
  · obtain ⟨p, hp, hle⟩ := hne
    exact ⟨(pValue p : ℝ) / (p.numVerts : ℝ), p, hp, hle, rfl⟩
  · rintro a ⟨p, hp, hle, rfl⟩
    obtain ⟨hklt, hHEP, hbound⟩ := hkey p hp hle
    have hmem : ((iExitless k (p.numVerts + k) : ℝ) - (k : ℝ) + 2) /
          (((p.numVerts + k : ℕ) : ℝ) - (k : ℝ)) ∈
        {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
          q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} :=
      ⟨p.numVerts + k, hklt, hHEP, by push_cast; ring_nf⟩
    exact le_trans (csInf_le hBddR hmem) hbound

end Hunter.Proved

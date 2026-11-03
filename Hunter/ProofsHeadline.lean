/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLink2
import Hunter.ProofsReductions
import Hunter.ProofsHrev
import Hunter.ProofsGB2
import Hunter.ProofsGreedy2
import Hunter.ProofsMore
import Hunter.ProofsB2
import Hunter.ProofsExitless

/-!
# The headline superpermutation lower bound — UNCONDITIONAL (`Hunter/ProofsHeadline.lean`)

With Theorem 2 now proved unconditionally (`Hunter.Proved.thm2_unconditional`, via the
rigidity/chart route of `ProofsLink2`, and the residual `ProofsEndgame.TightJumpFreeAll`
discharged as `Hunter.Proved.tightJumpFree`), this file closes the **last remaining leaf** of
the headline theorems `thm1v1` / `thm1v2` / `eq_weak`: the §6.4 analytic `L`-bound `hproof`
(the concrete `proof_thm1v2` conclusion).

## The last leaf, assembled

Every downstream endgame chain (`ProofsQED.thm1v1_final`, …) consumed **two** leaves:
`ProofsEndgame.TightJumpFreeAll` (Theorem 2's recursion-region content — now proved) and
`hproof` (the reduction output).  Prior passes carried `hproof` as a hypothesis with the note
"no in-tree discharger exists".  That note is now obsolete: with `red_R` closed
(`Proved.red_R_closed`, via the `p_u`-extension `pu_key`), `red_p*` closed
(`Proved.red_pstar_closed`), `b2` in `gInner` form (`Proved.b2_gInner`), `gInner`-monotonicity
(`Proved.gInner_mono`), Theorem 2 (`Proved.thm2_unconditional`), the base-region equality
(`Proved.thm2_equality`) and the ratio-minimum `prop3`/`prop4`, `hproof` **is** now in-tree.

`proof_thm1v2_all` assembles it.  We do **not** route through `proof_thm1v2_tightened`'s
`hgInner_eval` *equality* leaf (which would need a strongly-exitless witness realizing `i_k(P)`
— a harder, unneeded fact).  Instead we bound the concrete inner min
`gInner k r_P = min_{p*∈𝒳'_k}{ w(p*) − r_P|p*| }` from **below** by `i_k(P) − r_P·P` directly:

* every `p* ∈ 𝒳'_k` is strongly exitless, so `k ∣ |p*|` and `|p*| ≥ k`;
* if `|p*| > k`: `w(p*) ≥ i_k(|p*|)` and `prop4` gives `i_k(|p*|) − r_P|p*| ≥ i_k(P) − r_P·P`;
* if `|p*| = k`: `w(p*) ≥ |p*| − 1 = k − 1`, and `i_k(P) − r_P·P = k − 2 − r_P·k ≤ (k−1) − r_P·k`.

Then `L ≥ R_k·k! + gInner(R_k) ≥ r_P·k! + gInner(r_P) ≥ r_P·k! + (i_k(P) − r_P·P)`, which is
exactly the `proof_thm1v2` bound.  Feeding it, together with `Proved.tightJumpFree`, into the
`ProofsQED` capstones yields `thm1v1` / `thm1v2` / `eq_weak` **unconditionally** (numeric guards
only).

Namespace `Hunter.ProofsHeadline`.  **Zero `sorry`, zero new axioms.**  Does not import
`Hunter.Statements`, so `Statements` can wire these terms in.
-/

namespace Hunter

open scoped Classical

namespace ProofsHeadline

variable {k : ℕ}

/-- Every exitless path has weight `≥ |p| − 1` (each of its `|p|−1` edges has weight `≥ 1`). -/
theorem wtP_ge_numVerts_sub_one (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    p.numVerts - 1 ≤ p.wtP := by
  have h1 := Hunter.Proved.prp_1edgebound hk hp
  have hsum := Hunter.Proved.wtP_ge_edgeCounts hk (p := p)
  omega

/-- `i_k(|p|) ≤ w(p)` for any exitless path `p` (the minimum weight is `≤` this witness). -/
theorem iExitless_le_wtP {p : HPath k} (hp : p.Exitless) :
    iExitless k p.numVerts ≤ p.wtP :=
  Nat.sInf_le ⟨p, hp, rfl, rfl⟩

/-- **The last leaf, assembled** — the concrete `proof_thm1v2` conclusion (`hproof`), proved
in-tree for every `k ≥ 3` and every pivot existence witness.  This is the §6.4 analytic
`L`-bound, no longer a carried hypothesis. -/
theorem proof_thm1v2_all :
    ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
      (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
        + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
            (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
          * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) := by
  intro k hk hpivot
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  set P : ℕ := k * (k - 1) * (k - 2) with hPdef
  -- real casts / positivity of `P − k`.
  have hPR : ((P : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) := ProofsReductions.castP hk2
  have hPk_pos : (0 : ℝ) < ((P : ℕ) : ℝ) - (k : ℝ) := by
    rw [hPR]; exact ProofsReductions.D_pos hk
  have hPpos : 0 < P := by
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hR : (0 : ℝ) < ((P : ℕ) : ℝ) := by linarith [hPk_pos]
    exact_mod_cast hR
  -- abbreviations for the pivot value and the pivot cost-ratio `r_P`.
  set iP : ℝ := (iExitless k P : ℝ) with hiPdef
  set rP : ℝ := (iP - (k : ℝ) + 2) / (((P : ℕ) : ℝ) - (k : ℝ)) with hrPdef
  -- `r_P · (P − k) = i_k(P) − k + 2`.
  have hrP_key : rP * (((P : ℕ) : ℝ) - (k : ℝ)) = iP - (k : ℝ) + 2 := by
    rw [hrPdef]; field_simp
  -- `i_k(P) = j_k(P)`  (base-region equality at the pivot; needs Theorem 2 both ways).
  have hthm2eq : iExitless k P = j k P :=
    Hunter.Proved.thm2_equality hk hPpos (le_refl _) hpivot
  -- `prop4`: the `i_k`-ratio over `ℓ > k` is minimized at the pivot — i.e. `r_P ≤ ratio_i(ℓ)`.
  have hprop4 : ∀ ℓ, k < ℓ → HasExitlessPath k ℓ →
      rP ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
    intro ℓ hℓ hex
    exact Hunter.Proved.prop4 hk hℓ hex hpivot
      (fun m hm => Hunter.Proved.prop3 hk hm)
      (fun m hm => Hunter.Proved.thm2_unconditional k m hk hm)
      hthm2eq
  -- `hRk_ge`: `r_P ≤ R_k`  (from `red_R` + `prop4`).
  have hSR_ne : {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))}.Nonempty := by
    refine ⟨rP, P, ?_, hpivot, ?_⟩
    · -- `k < P`
      have : (k : ℝ) < ((P : ℕ) : ℝ) := by linarith [hPk_pos]
      exact_mod_cast this
    · rw [hrPdef]
  have hRk_ge : rP ≤ Rk k := by
    have hle : rP ≤ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
        q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} := by
      apply le_csInf hSR_ne
      rintro q ⟨ℓ, hℓ, hex, rfl⟩
      exact hprop4 ℓ hℓ hex
    exact le_trans hle (Hunter.Proved.red_R_closed hk)
  -- lower bound the concrete inner min `gInner k r_P ≥ i_k(P) − r_P·P`.
  have hXk'_ne : (Xk' k).Nonempty :=
    ProofsB2.Xk'_nonempty_of_Xk_nonempty hk2 (Hunter.Proved.Xk_nonempty k)
  have hSE : Xk' k = {p : HPath k | p.StronglyExitless} := Hunter.Proved.prp_Xkcomps_closed hk2
  have hgInner_ge : iP - rP * ((P : ℕ) : ℝ) ≤ ProofsGB2.gInner k rP := by
    rw [ProofsGB2.gInner]
    apply le_csInf
    · obtain ⟨p, hp⟩ := hXk'_ne; exact ⟨_, p, hp, rfl⟩
    rintro q ⟨p, hp, rfl⟩
    have hse : p.StronglyExitless := by rw [hSE] at hp; exact hp
    have hexit : p.Exitless := hse.1
    have hdvd : k ∣ p.numVerts := Hunter.Proved.dvd_numVerts_of_stronglyExitless hk1 hse
    have hge_k : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
    rcases eq_or_lt_of_le hge_k with heq | hlt
    · -- `|p| = k` boundary: `w(p) ≥ k − 1` and `i_k(P) − r_P·P = k − 2 − r_P·k`.
      have hnv : (p.numVerts : ℝ) = (k : ℝ) := by rw [← heq]
      have hw : (k : ℝ) - 1 ≤ (p.wtP : ℝ) := by
        have := wtP_ge_numVerts_sub_one hk1 hexit
        rw [← heq] at this
        have hcast : ((k - 1 : ℕ) : ℝ) ≤ (p.wtP : ℝ) := by exact_mod_cast this
        rwa [Nat.cast_sub hk1, Nat.cast_one] at hcast
      rw [hnv]
      nlinarith [hrP_key, hw]
    · -- `|p| > k`: `w(p) ≥ i_k(|p|)` and `prop4` at `ℓ = |p|`.
      have hexP : HasExitlessPath k p.numVerts := ⟨p, hexit, rfl⟩
      have hiw : (iExitless k p.numVerts : ℝ) ≤ (p.wtP : ℝ) := by
        exact_mod_cast iExitless_le_wtP hexit
      have hr4 := hprop4 p.numVerts hlt hexP
      have hd : (0 : ℝ) < (p.numVerts : ℝ) - (k : ℝ) := by
        have : (k : ℝ) < (p.numVerts : ℝ) := by exact_mod_cast hlt
        linarith
      have hmul : rP * ((p.numVerts : ℝ) - (k : ℝ))
          ≤ (iExitless k p.numVerts : ℝ) - (k : ℝ) + 2 := by
        rw [le_div_iff₀ hd] at hr4; linarith [hr4]
      nlinarith [hrP_key, hmul, hiw]
  -- assemble via `b2_gInner` and `gInner_mono`.
  have hb2 : (L k : ℝ) ≥ Rk k * (k.factorial : ℝ) + ProofsGB2.gInner k (Rk k) :=
    Hunter.Proved.b2_gInner hk2
  have hmono : rP * (k.factorial : ℝ) + ProofsGB2.gInner k rP
      ≤ Rk k * (k.factorial : ℝ) + ProofsGB2.gInner k (Rk k) :=
    Hunter.Proved.gInner_mono hk2 rP (Rk k) hRk_ge
  -- final chain.
  have hfin : (L k : ℝ) ≥ rP * (k.factorial : ℝ) + (iP - rP * ((P : ℕ) : ℝ)) := by
    calc (L k : ℝ) ≥ Rk k * (k.factorial : ℝ) + ProofsGB2.gInner k (Rk k) := hb2
      _ ≥ rP * (k.factorial : ℝ) + ProofsGB2.gInner k rP := hmono
      _ ≥ rP * (k.factorial : ℝ) + (iP - rP * ((P : ℕ) : ℝ)) := by linarith [hgInner_ge]
  -- rearrange to the stated form `i_k(P) + r_P·(k! − P)`.
  rw [ge_iff_le]
  calc (iExitless k P : ℝ) + rP * ((k.factorial : ℝ) - ((P : ℕ) : ℝ))
      = rP * (k.factorial : ℝ) + (iP - rP * ((P : ℕ) : ℝ)) := by rw [hiPdef]; ring
    _ ≤ (L k : ℝ) := hfin

/-- **prop4** (closed) — the `i_k`-ratio `(i_k(ℓ)−k+2)/(ℓ−k)` over `ℓ > k` is minimized at the
pivot, **UNCONDITIONAL** for `3 ≤ k`.  All three inputs of `Proved.prop4` are now discharged:
`prop3` (the `j_k`-ratio minimum), `thm2` (`Proved.thm2_unconditional`) and the base-region
equality at the pivot (`Proved.thm2_equality`). -/
theorem prop4_closed (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) (hex : HasExitlessPath k ℓ)
    (hpivot : HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) := by
  have hPpos : 0 < k * (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]; positivity
  exact Hunter.Proved.prop4 hk h hex hpivot
    (fun m hm => Hunter.Proved.prop3 hk hm)
    (fun m hm => Hunter.Proved.thm2_unconditional k m hk hm)
    (Hunter.Proved.thm2_equality hk hPpos (le_refl _) hpivot)

/-! ## The headline theorems — UNCONDITIONAL (numeric guards only) -/

/-- **thm1v1** — the superpermutation lower bound `L*(k) ≥ coeff(k)·k! + k − C`,
**UNCONDITIONAL**.  Theorem 2 (`Proved.tightJumpFree`) and the reduction leaf
(`proof_thm1v2_all`) are both discharged. -/
theorem thm1v1_unconditional :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsQED.thm1v1_final Hunter.Proved.tightJumpFree proof_thm1v2_all

/-- **thm1v2** — the coefficient lower bound `L(k) ≥ coeff(k)·k! − C`, **UNCONDITIONAL**. -/
theorem thm1v2_unconditional :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsQED.thm1v2_final Hunter.Proved.tightJumpFree proof_thm1v2_all

/-- **eq-weak** — the comparable-factorial form, **UNCONDITIONAL**. -/
theorem eq_weak_unconditional :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsQED.eq_weak_final Hunter.Proved.tightJumpFree proof_thm1v2_all

end ProofsHeadline

end Hunter

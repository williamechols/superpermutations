/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsRigid
import Hunter.ProofsPotential

/-!
# The graph-level ENDGAME of Hunter's Theorem 2 — assembly on the single sharp kernel

**Current repository status.** This module deliberately isolates a residual. The later
`Hunter.ProofsLink2` chart-profile argument discharges it and proves Theorem 2 unconditionally;
the calibrated verdict below records the boundary reached at this development stage.

This file is the terminal assembly of Theorem 2's recursion-region argument.  Two prior deep
passes (`PROGRESS-rigid`, `PROGRESS-tail`) pinned the *entire* open content of Theorem 2 in the
recursion region to one crisp block inequality, `ProofsRigid.ExcessBlockCeil k`
(`excess ≥ Dfr(⌈|p|/k⌉)` — the opened-block demand).  Here we:

1. **Sharpen the residual to its exact jump-tightness kernel** (`TightJumpFree`) and prove the
   *case-reduction* `TightJumpFree k → ExcessBlockCeil k`, k-uniform and sorry-free, from the
   repository's unconditional block bound (`ProofsRigid.blockCeil_pred_le_G`, one block short) plus
   the proved single-step increment `Dfr(T+1) ≤ Dfr(T)+1` (`Dfr_succ_le`).  This isolates the
   irreducible content to a *single* case: an exitless path whose excess is *exactly* `Dfr(T)` at a
   length where the block demand *jumps* (`Dfr(T+1) = Dfr(T)+1`).

2. **Assemble the full downstream chain** from the residual to the headline statements — Theorem 2
   verbatim (`k ≥ 3`) and the superpermutation lower bounds `thm1v1`/`thm1v2`/`eq_weak` — with
   *every* other hypothesis discharged (the base leaf `M1WalkBound 3`, G1, G2
   `DefectiveDeepExitAll`, and the existence leaf `hasExitlessPath_pivot`), leaving exactly
   `{ExcessBlockCeilAll}` (Theorem 2) resp. `{ExcessBlockCeilAll, hproof}` (Theorem 1).

## Development-stage verdict (calibrated at `k = 5,6,7,9` before any Lean)

The endgame did **NOT** close unconditionally.  The kernel `TightJumpFree`
(≡ `ExcessBlockCeil`) is **true** — verified with `0` violations for every realizable length,
and the feared tight-jump configuration provably **never occurs** on real paths
(`campaign/rigid/inv3.py`: *tight-jump lengths = ∅*) — but its truth is a **reachability** fact
(the saturated zero-potential state cannot sit at a demand-jump terminal), *pointwise-false* in the
per-block LP.  The structural closure that would prove it (PROOF.md §2 rigidity + §3 τ₃-closure)
is verified only `k ≤ 9` with **no** `k`-uniform symbolic proof; the alternative (banked-surplus
walk invariant) lives in `ProofsWalk`/`ProofsTheorem`, out of this file's scope.  The task's
STEP-3 "partial-block entry edge has weight ≥ 4" route is moreover *refuted* in the Lean geometry:
every terminal-tail edge is a forced weight-1 σ-step (`ProofsWindow.heavy_is_boundary`,
`PROGRESS-tail §1`).  So the endgame is delivered as the single named residual, never forced.

Namespace `Hunter.ProofsEndgame`.  **Zero `sorry`, zero new axioms.**
-/

namespace Hunter

open scoped Classical

namespace ProofsEndgame

open ProofsPotential ProofsRecursion ProofsRigid ProofsInduction ProofsClose Proved HPath

variable {k : ℕ}

/-! ## §1. The sharp kernel and the case-reduction (STEP 4's `{0,1}`-jump reduction) -/

/-- **The jump-tightness kernel.**  The sole irreducible content of `ExcessBlockCeil`: an
exitless path can never be *tight* (`excess = Dfr(T)`, `T = (|p|−1)/k` the last full block) at a
length where the block demand *jumps* (`Dfr(T+1) = Dfr(T)+1`).  Verified `0` occurrences for all
realizable lengths (`campaign/rigid/inv3.py`), but pointwise-false in the per-block LP — the
genuine reachability kernel of Theorem 2. -/
def TightJumpFree (k : ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → 0 < p.numVerts →
    Dfr k ((p.numVerts - 1) / k + 1) = Dfr k ((p.numVerts - 1) / k) + 1 →
    Dfr k ((p.numVerts - 1) / k) < excess p

/-- **The case-reduction (PROVED, k-uniform).**  `ExcessBlockCeil k` follows from the jump
kernel `TightJumpFree k`.  Mechanism: the repository's unconditional bound gives `Dfr(T) ≤ excess`
at the last *full* block `T = (|p|−1)/k` (via `blockCeil_pred_le_G`, one block short of the goal);
the opened-block count is `⌈|p|/k⌉ = T+1` (`ceilDiv_succ_pred`); and the single-step increment
`Dfr(T+1) ≤ Dfr(T)+1` (`Dfr_succ_le`) splits the goal into the *non-jump* case (`Dfr(T+1) = Dfr(T)`,
immediate) and the *jump* case (`Dfr(T+1) = Dfr(T)+1`), the latter paid exactly by
`TightJumpFree`. -/
theorem excessBlockCeil_of_tightJumpFree (hk : 4 ≤ k) (h : TightJumpFree k) :
    ProofsRigid.ExcessBlockCeil k := by
  intro p hp h0
  set T := (p.numVerts - 1) / k with hT
  have hceil : p.numVerts ⌈/⌉ k = T + 1 := ceilDiv_succ_pred h0 (by omega)
  rw [hceil]
  -- `Dfr T ≤ excess p` from the unconditional one-block-short bound
  have hpred : T ≤ ProofsInduction.G k (excess p) := by
    have hbp := ProofsRigid.blockCeil_pred_le_G hk hp h0
    rwa [hceil, Nat.add_sub_cancel] at hbp
  have hDfrT : Dfr k T ≤ excess p := by
    rcases Nat.eq_zero_or_pos T with hz | hpos
    · rw [hz, Dfr_zero]; exact Nat.zero_le _
    · exact (ProofsInduction.Dfr_le_iff_le_G hk T hpos (excess p)).mpr hpred
  have hinc : Dfr k (T + 1) ≤ Dfr k T + 1 := Dfr_succ_le hk T
  by_cases hjump : Dfr k (T + 1) = Dfr k T + 1
  · have hstrict : Dfr k T < excess p := h p hp h0 hjump
    omega
  · -- non-jump: `Dfr(T+1) ≤ Dfr(T) ≤ excess`
    omega

/-! ## §2. The global forms and the residual bridges -/

/-- Global form of the crisp block residual: `ExcessBlockCeil` at every `k ≥ 4`. -/
def ExcessBlockCeilAll : Prop := ∀ k, 4 ≤ k → ProofsRigid.ExcessBlockCeil k

/-- Global form of the jump kernel. -/
def TightJumpFreeAll : Prop := ∀ k, 4 ≤ k → TightJumpFree k

/-- **`ExcessBlockCeilAll` from the jump kernel** (global case-reduction). -/
theorem excessBlockCeilAll_of_tightJumpFreeAll (h : TightJumpFreeAll) : ExcessBlockCeilAll :=
  fun k hk => excessBlockCeil_of_tightJumpFree hk (h k hk)

/-- **The terminal-tail residual from the crisp block residual** (arithmetic half, via
`ProofsRigid.terminalFrontierTail_of_blockCeil`). -/
theorem terminalFrontierTailAll_of_blockCeilAll (h : ExcessBlockCeilAll) :
    TerminalFrontierTailAll :=
  fun k hk => ProofsRigid.terminalFrontierTail_of_blockCeil hk (h k hk)

/-- **The global M1 slab bound from the crisp block residual.**  Composes the residual bridge with
the repository's `Proved.m1WalkBoundAll_of_tail` (base `M1WalkBound 3` and G2 `DefectiveDeepExitAll`
already discharged). -/
theorem m1WalkBoundAll_of_blockCeilAll (h : ExcessBlockCeilAll) : Proved.M1WalkBoundAll :=
  Proved.m1WalkBoundAll_of_tail ProofsTail.m1WalkBound_three
    (terminalFrontierTailAll_of_blockCeilAll h)

/-- The existence leaf, discharged (`Proved.hasExitlessPath_pivot`, ProofsGreedy2). -/
theorem hexists_pivot :
    ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) :=
  fun k hk => Proved.hasExitlessPath_pivot k hk

/-! ## §3. The headline capstones on the single residual `ExcessBlockCeilAll`

Every hypothesis other than the crisp block residual (and, for Theorem 1, the analytic input
`hproof`) is discharged: the base leaf `M1WalkBound 3` (`ProofsTail.m1WalkBound_three`), G1
(`runCap_discharged`), G2 (`Proved.defectiveDeepExitAll`), and existence
(`Proved.hasExitlessPath_pivot`). -/

/-- **Theorem 2 (verbatim `Statements.thm2` conclusion), whole range `k ≥ 3`, from the residual.**
`k = 3,4` unconditional (`thm2_small`); `k ≥ 5` carries exactly `ExcessBlockCeil k`. -/
theorem thm2_of_blockCeilAll (h : ExcessBlockCeilAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  ProofsTail.thm2All_of_tail (terminalFrontierTailAll_of_blockCeilAll h)

/-- **thm1v1** (superpermutation lower bound) from the residual + `hproof` only. -/
theorem thm1v1_of_blockCeilAll (h : ExcessBlockCeilAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_final (m1WalkBoundAll_of_blockCeilAll h) hproof hexists_pivot

/-- **thm1v2** (`L(k) ≥ coeff(k)·k! − O(1)`) from the residual + `hproof` only. -/
theorem thm1v2_of_blockCeilAll (h : ExcessBlockCeilAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_final (m1WalkBoundAll_of_blockCeilAll h) hproof hexists_pivot

/-- **eq-weak** (comparable-factorial form) from the residual + `hproof` only. -/
theorem eq_weak_of_blockCeilAll (h : ExcessBlockCeilAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  Proved.eq_weak_final (m1WalkBoundAll_of_blockCeilAll h) hproof hexists_pivot

/-! ## §4. Same capstones on the *sharpest* kernel `TightJumpFreeAll` (via the case-reduction) -/

/-- **Theorem 2 from the sharp jump kernel.** -/
theorem thm2_of_tightJumpFreeAll (h : TightJumpFreeAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  thm2_of_blockCeilAll (excessBlockCeilAll_of_tightJumpFreeAll h)

/-- **thm1v1 from the sharp jump kernel + `hproof`.** -/
theorem thm1v1_of_tightJumpFreeAll (h : TightJumpFreeAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  thm1v1_of_blockCeilAll (excessBlockCeilAll_of_tightJumpFreeAll h) hproof

end ProofsEndgame

end Hunter

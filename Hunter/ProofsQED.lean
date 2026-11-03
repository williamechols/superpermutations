/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsEndgame
import Hunter.ProofsRigidity2
import Hunter.ProofsClosure3

/-!
# FINAL ASSEMBLY of Hunter's Theorem 2 (`Hunter/ProofsQED.lean`)

**Current repository status.** This is an intermediate, residual-parameterized assembly.
`Hunter.ProofsLink2` later discharges the residual through the chart-profile proof and exports
the unconditional theorem. The development-stage audit below describes what this module alone
establishes; it is not the final project verdict.

This file is the terminal cross-file wiring pass.  It collects, in one place and on a **single
named residual**, the complete downstream chain from the recursion-region kernel to every headline
statement — Theorem 2 verbatim (`k ≥ 3`) and the three superpermutation lower bounds
(`thm1v1`/`thm1v2`/`eq_weak`) — with *every other* leaf discharged, and records the axiom audit.

## Boundary of this intermediate module

The residual is `ProofsEndgame.TightJumpFreeAll` (≡ `ProofsRigid.ExcessBlockCeilAll`, the
demand-jump reachability kernel).  This pass **verified** — against the in-tree `Dfr`/`G`
definitions, `k = 5..9` (`campaign/qed/calib_split.py`) — that:

* at the tight chart end `T = (k−1)(k−2)` the completed deterministic τ₂/τ₃ chart has
  `excess = k−3 = Dfr k T` **exactly**, and `T` is a genuine demand **jump** (`Dfr k (T+1) =
  Dfr k T + 1`).  So the tight-at-jump configuration `TightJumpFree` rules out is arithmetically
  *real*: nothing numeric forbids it.
* the resolution route is **arithmetically sound**: the `(T+1)`-st block's entry is a *fresh*
  continuation of the completed chart, forced to weight `≥ 4` by `ProofsClosure3.chart_closure`,
  contributing `≥ 2` extra excess, so a real path there has `excess ≥ (k−3) + 2 ≥ Dfr k (T+1)` —
  `ExcessBlockCeil` holds.  (This corrects the earlier "STEP-3 refuted" reading: the chargeable
  edge is the **block-boundary** edge `k·T → block (T+1)`, which *is* payable — `bw ≥ 2` — not the
  in-block σ-tail, which `ProofsWindow.heavy_is_boundary` forces to weight 1.)

## What genuinely blocks closure (named precisely, never forced)

The route needs the completed `T = (k−1)(k−2)`-block exitless prefix to **equal the deterministic
chart** (as rotation classes, in `ProofsClosure3.chartWord` coordinates), so that
`chart_closure`'s `finalExit`/`VisitedByChart` apply.  Every *abstract* ingredient of that
rigidity is proved sorry-free in-tree — `ProofsRigidity2.run_forced` (intra-run determinism),
`ProofsRigidity2.forced_step` (only τ₃ survives a run boundary), `ProofsRigidity2.runlen_pigeonhole`
(the counting collapse), `ProofsClosure3.chart_closure` (the weight-≥4 punchline) — but the
**concrete instantiation onto an `HPath`** is *not* in-tree and is genuine remaining work, not
plumbing:

1. **Block extraction packaging** `q t := word of p.vert (k·t)` with its weight-2 profile read off
   the run decomposition (`ProofsRunExtract.runStart`/`metaDepth`/`doorDepth` deliver only the
   *unconditional* `metaDepth_le`, not a chart-equality).
2. **Discharging `forced_step`'s freshness hypotheses globally** (`hvfresh`, `hlast`) from path
   `Nodup` + the counting collapse, and **iterating it over the `k−3` run boundaries** — the
   run-to-run **orbit closure** (`PROOF_S2 §4`/`PROOF_S3` STEP 2) for which the prior calibrated
   passes found **no `k`-uniform symbolic proof** (verified `k ≤ 9` only).

Hence `Hunter.Proved.tightJumpFree : TightJumpFree k` is **not** provided here; forcing it would
require a `sorry` or a new axiom, which this pass refuses.  It is delivered as
the single named leaf.

Namespace `Hunter.ProofsQED`.  **Zero `sorry`, zero new axioms.**
-/

namespace Hunter

open scoped Classical

namespace ProofsQED

/-! ## §1. The single named residual (all interderivable in-tree)

`TightJumpFreeAll` (the sharpest form — a lone tight-at-jump statement) ≡ `ExcessBlockCeilAll`
(`ProofsEndgame.excessBlockCeilAll_of_tightJumpFreeAll`) ≡ `TerminalFrontierTailAll` ≡
`∀ k ≥ 4, M1WalkBound k`.  It is the entire open content of Theorem 2 in the recursion region. -/

/-- The single non-numeric residual carrying Theorem 2 (and, with `hproof`, Theorem 1). -/
abbrev TheResidual : Prop := ProofsEndgame.TightJumpFreeAll

/-! ## §2. Theorem 2 verbatim (`k ≥ 3`) on the residual — every other leaf discharged -/

/-- **Theorem 2** (the `Statements.thm2` conclusion, whole range `k ≥ 3`), from the residual.
Base leaf `M1WalkBound 3`, G1 run cap, G2 `DefectiveDeepExitAll`, and existence
`hasExitlessPath_pivot` are all discharged upstream; `k = 3,4` are unconditional. -/
theorem thm2_final (h : TheResidual) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  ProofsEndgame.thm2_of_tightJumpFreeAll h

/-! ## §3. The three superpermutation lower bounds on the residual + `hproof`

`hproof` is the analytic `L`-bound leaf (`ProofsMF`), carried not proved — no in-tree discharger
exists (`PROGRESS-mf`/`PROGRESS-tail §4`).  It is the sole additional leaf for Theorem 1. -/

/-- **thm1v1** — `Lstar k ≥ coeff k · k! + k − C`, from the residual + `hproof`. -/
theorem thm1v1_final (h : TheResidual)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsEndgame.thm1v1_of_tightJumpFreeAll h hproof

/-- **thm1v2** — `L k ≥ coeff k · k! − C`, from the residual + `hproof`. -/
theorem thm1v2_final (h : TheResidual)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsEndgame.thm1v2_of_blockCeilAll
    (ProofsEndgame.excessBlockCeilAll_of_tightJumpFreeAll h) hproof

/-- **eq-weak** — comparable-factorial form, from the residual + `hproof`. -/
theorem eq_weak_final (h : TheResidual)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsEndgame.eq_weak_of_blockCeilAll
    (ProofsEndgame.excessBlockCeilAll_of_tightJumpFreeAll h) hproof

/-! ## §4. The residual reduces to the crisp block form (interderivability, PROVED) -/

/-- The sharp jump kernel yields the crisp opened-block bound (`ProofsEndgame` case-reduction). -/
theorem excessBlockCeilAll_of_residual (h : TheResidual) : ProofsEndgame.ExcessBlockCeilAll :=
  ProofsEndgame.excessBlockCeilAll_of_tightJumpFreeAll h

end ProofsQED

end Hunter

/-! ## §5. Axiom audit — every capstone depends on exactly `{propext, Classical.choice, Quot.sound}`

The rigidity/closure kernels the route rests on are audited too, to certify the abstract
mathematics is itself sorry-free and axiom-clean. -/

-- Headline capstones (Theorem 2 verbatim + the three superperm bounds), on the residual.
#print axioms Hunter.ProofsQED.thm2_final
#print axioms Hunter.ProofsQED.thm1v1_final
#print axioms Hunter.ProofsQED.thm1v2_final
#print axioms Hunter.ProofsQED.eq_weak_final
#print axioms Hunter.ProofsQED.excessBlockCeilAll_of_residual

-- The case-reduction that sharpened the residual (k-uniform, PROVED).
#print axioms Hunter.ProofsEndgame.excessBlockCeil_of_tightJumpFree

-- The §2 rigidity kernels (word-level, PROVED sorry-free).
#print axioms Hunter.Proved.tau2_forced
#print axioms Hunter.Proved.tau3_forced
#print axioms Hunter.Proved.run_forced
#print axioms Hunter.Proved.runlen_pigeonhole

-- The §3 closure kernel (weight-≥4 punchline, PROVED sorry-free).
#print axioms Hunter.Proved.chart_closure

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLast

/-!
# Theorem 2 — the terminal-tail residual, pinned to the full open content (`Hunter.ProofsTail`)

This pass settles, rigorously and sorry-free, *what* the last residual `TerminalFrontierTail k`
actually is.  The question posed to this pass was whether `TerminalFrontierTail` is a **convention
mismatch** (the block-scale hypothesis `Dfr k T ≤ excess` merely needing to be threaded to the exact
vertex-level frontier through the walk machinery) or **genuine mathematics** (the irreducible
demand-phase ↔ potential-phase alignment).  The answer, proved below as a Lean equivalence:

> **`TerminalFrontierTail k ↔ M1WalkBound k`  (for `k ≥ 4`).**

Since `M1WalkBound k ↔ ExcessFrontier k` (`ProofsM1.m1WalkBound_iff_excessFrontier`, `Iff.rfl`) is the
*entire* open content of Theorem 2 in the recursion region, closing `TerminalFrontierTail` is exactly
as hard as closing Theorem 2 itself.  It is **not** a convention artifact.

## Why the equivalence holds (both directions sorry-free)

* **`M1WalkBound → TerminalFrontierTail`** (`terminalFrontierTail_of_excessFrontier`): trivial — the
  conclusion of `TerminalFrontierTail p` is *verbatim* the `M1WalkBound`/`ExcessFrontier` inequality
  at `p`; the extra hypothesis `Dfr k T ≤ excess p` is simply dropped.

* **`TerminalFrontierTail → M1WalkBound`** (`excessFrontier_of_terminalFrontierTail`): the extended
  walk invariant supplies the hypothesis `Dfr k ((numVerts−1)/k) ≤ excess p` for **every** exitless
  path, *unconditionally* — `ProofsTheorem.ext_excess_ge_Dfr_block` needs only
  `DefectiveDeepExit k`, which is now the proved theorem `ProofsLast.defectiveDeepExit`.  So the
  hypothesis is never a real restriction: the set of paths satisfying it is all exitless paths.

## The convention truth (the derivation this pass was asked to verify was refuted)

The proposed closure routed the terminal partial-block demand jump `Dfrontier(N) − Dfr(T) = 1`
through an "entry edge `e` of the partial block" paid via `tail_pays` (`cost e + Hext(T) ≥ δ = 1`).
Two structural facts of the Lean model defeat it:

1. **`ProofsWindow.heavy_is_boundary`** — every weight-`≥2` edge of an exitless path sits at a block
   boundary `k ∣ (i+1)`; block interiors are forced weight-`1` σ-steps.  The terminal partial block
   `(k·T, N]` with `k·T < N ≤ k·(T+1)` contains **no** boundary index (the next one is `k·(T+1) > N−1`),
   so **every tail edge contributes `0` to excess**: `excess p = PE p T` exactly, for every remainder
   `r = N − k·T ∈ {1,…,k}`.  There is no "extra payable entry edge".

2. **`tail_pays` cannot be invoked at `t = T`.**  It requires `k·(T+1) < numVerts` (the block-`T+1`
   boundary edge, index `k·(T+1)−1`, to lie inside the path), but `numVerts ≤ k·(T+1)` always.  The
   very boundary that would "pay" block `T+1`'s demand jump is beyond the last vertex.

Hence the `+1` at a jump length must come **entirely** from the banked potential `Hext p T`
(`excess = PE T ≥ Dfr T + Hext T`, so the goal `excess ≥ Dfr T + 1` is `Hext T ≥ 1`).  And
`Hext p T ≥ 1` at a demand-jump phase is *false pointwise* — the saturated state `(doorDepth = k−2,
metaDepth = k−3)` has `Hext = hpot k (k−2) (k−3) T = 0` yet `Dfr(T+1) = Dfr(T)+1` is possible — so it
holds only by a **reachability** constraint (that this state cannot occur at a jump-phase terminal
block).  That reachability constraint is precisely `ProofsFinal.JumpLoopEntryFree` / Hunter's
`HPath(k−1)` meta-lift: genuinely path-global, no known `k`-uniform symbolic proof, and not among the
proved leaves.  This matches every prior ledger.

Namespace `Hunter.ProofsTail`.  **Zero `sorry`, zero new axioms.**  Theorem 2 does **not** close
unconditionally; the residual set for `k ≥ 5` is the single, sharp, equivalent
`TerminalFrontierTail`.
-/

namespace Hunter

open scoped Classical

namespace ProofsTail

open ProofsPotential ProofsWalk ProofsClose ProofsTheorem ProofsRecursion ProofsM1 HPath

variable {k : ℕ}

/-! ## The equivalence `TerminalFrontierTail k ↔ M1WalkBound k` -/

/-- **`ExcessFrontier k → TerminalFrontierTail k`** (drop the block-scale hypothesis).  The
conclusion of `TerminalFrontierTail` at `p` is verbatim the `ExcessFrontier`/`M1WalkBound`
inequality at `p`, so the extra hypothesis is unused. -/
theorem terminalFrontierTail_of_excessFrontier (hfr : ExcessFrontier k) :
    TerminalFrontierTail k :=
  fun p hp h0 _ => hfr p hp h0

/-- **`TerminalFrontierTail k → ExcessFrontier k`.**  The extended walk invariant provides the
block-scale hypothesis `Dfr k ((numVerts−1)/k) ≤ excess p` for **every** exitless path
unconditionally (`ext_excess_ge_Dfr_block`, carrying only the now-proved
`ProofsLast.defectiveDeepExit`), so `TerminalFrontierTail` — quantified over all exitless paths —
already covers all of them. -/
theorem excessFrontier_of_terminalFrontierTail (hk : 4 ≤ k) (hG3 : TerminalFrontierTail k) :
    ExcessFrontier k := by
  intro p hp h0
  exact hG3 p hp h0 (ext_excess_ge_Dfr_block hk hp h0 (ProofsLast.defectiveDeepExit hk))

/-- **The equivalence.**  For `k ≥ 4`, the terminal-tail residual is logically equivalent to the
M1 slab bound (`= ExcessFrontier k`, the whole open content of Theorem 2): closing
`TerminalFrontierTail` closes Theorem 2, and vice versa.  It is **not** a convention artifact. -/
theorem terminalFrontierTail_iff_m1WalkBound (hk : 4 ≤ k) :
    TerminalFrontierTail k ↔ M1WalkBound k :=
  ⟨fun hG3 => m1WalkBound_iff_excessFrontier.mpr (excessFrontier_of_terminalFrontierTail hk hG3),
   fun hM1 => terminalFrontierTail_of_excessFrontier (m1WalkBound_iff_excessFrontier.mp hM1)⟩

/-- Same equivalence phrased against `ExcessFrontier` directly. -/
theorem terminalFrontierTail_iff_excessFrontier (hk : 4 ≤ k) :
    TerminalFrontierTail k ↔ ExcessFrontier k :=
  ⟨excessFrontier_of_terminalFrontierTail hk, terminalFrontierTail_of_excessFrontier⟩

/-! ## The `k = 3` base leaf, discharged -/

/-- **`M1WalkBound 3` — discharged.**  For `k = 3` the recursion region is vacuous: every exitless
path has `numVerts ≤ 3! = 3·2·1 = k(k−1)(k−2)` (a duplicate-free word over the `k!` vertices), so it
lies entirely in the base region and `ProofsRecursion.excess_frontier_base` gives the frontier bound
directly.  This removes the `M1WalkBound 3` base value from the `…All` capstones' hypothesis lists. -/
theorem m1WalkBound_three : M1WalkBound 3 := by
  intro q hqe h0
  have hcard : q.numVerts ≤ Fintype.card (Vtx 3) := q.nodup.length_le_card
  rw [ProofsRecursion.card_Vtx] at hcard
  have hle : q.numVerts ≤ 3 * (3 - 1) * (3 - 2) := by
    simp only [Nat.factorial] at hcard; omega
  exact ProofsRecursion.excess_frontier_base (by norm_num) hqe h0 hle

/-! ## Global form -/

/-- **Global equivalence.**  `TerminalFrontierTailAll ↔ ∀ k, 4 ≤ k → M1WalkBound k`.  (`M1WalkBoundAll`
additionally fixes the `k = 3` base value, which is a separate leaf.) -/
theorem terminalFrontierTailAll_iff : TerminalFrontierTailAll ↔ (∀ k, 4 ≤ k → M1WalkBound k) :=
  ⟨fun hAll k hk => (terminalFrontierTail_iff_m1WalkBound hk).mp (hAll k hk),
   fun hAll k hk => (terminalFrontierTail_iff_m1WalkBound hk).mpr (hAll k hk)⟩

/-! ## The sharpest honest headline capstones (base + existence leaves discharged)

With `M1WalkBound 3` (`m1WalkBound_three`) and the pivot existence
(`Proved.hasExitlessPath_pivot`) both proved, the Theorem-1 / Theorem-2 capstones carry a strictly
shorter hypothesis list than `ProofsLast`: the sole remaining non-numeric leaves are the single
open residual `TerminalFrontierTailAll` (G3, equivalent to all of Theorem 2) and, for `thm1`, the
analytic input `hproof` (no in-tree discharger). -/

/-- **Theorem 2 over the whole range `k ≥ 3`, from the single residual `TerminalFrontierTailAll`.**
`k = 3, 4` are the unconditional base (`thm2_small`); `k ≥ 5` carries only `TerminalFrontierTail k`. -/
theorem thm2All_of_tail (hG3 : TerminalFrontierTailAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  fun k _ℓ hk hℓ => Proved.thm2_ge3_of_tail hk (fun h5 => hG3 k (by omega)) hℓ

/-- **thm1v1 from `TerminalFrontierTailAll` + `hproof` only** — the base value `M1WalkBound 3`
(`m1WalkBound_three`), G2 (`Proved.defectiveDeepExitAll`) and the existence leaf
(`Proved.hasExitlessPath_pivot`) are discharged here. -/
theorem thm1v1_of_tail_sharp (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_of_tail m1WalkBound_three hG3 hproof
    (fun k hk => Proved.hasExitlessPath_pivot k hk)

/-- **thm1v2 from `TerminalFrontierTailAll` + `hproof` only** (base / G2 / existence discharged). -/
theorem thm1v2_of_tail_sharp (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_of_tail m1WalkBound_three hG3 hproof
    (fun k hk => Proved.hasExitlessPath_pivot k hk)

end ProofsTail

end Hunter

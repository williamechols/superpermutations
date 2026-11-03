/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsCascade

/-!
# Theorem 2 — the M1 SLAB CERTIFICATE (closing arithmetic)

This file assembles the **M1 slab certificate** — the min-excess "slab" dynamic program
(dichotomy + the proved α-run cap `k − 2`) that reproduces the frontier demand `Dfr` exactly at
every recursion corner (`k = 6`: 121/121; `k = 7`: 716/716; valid at `k = 5` against
proven-optimal ground truth; robust to the omitted `mmC` adversary move).  See `PROGRESS-m1.md`
and `scratchpad/campaign/m1/` for the full computational certificate: the bounded state-and-phase
bonus `g*(state,φ) ∈ [0,2]`, `g* ≥ 0`, and the **per-transition potential inequalities**

  `cost + g*(s,φ) − g*(s',φ') ≥ Dfr(b+1) − Dfr(b)`

verified with **0 failures** across all four transition kinds (door / α-under-cap / reset / heavy)
at `k = 5,6,7,8` (`certify2.py`).  That certificate is the honest core: M1's exactness is a genuine
per-transition potential fact, not a numerical coincidence.

## What is proved here (sorry-free, axiom-clean)

* `demand_plateau_block` — the demand side of the certificate: in the recursion region the frontier
  demand does not increase across a block-interior vertex (`ℓ % k ≠ 1`).  A repackaging of the
  proved `ProofsCascade.dfr_plateau` under its M1 (per-block) reading.
* `alphaCap` — the **α-run cap** the certificate's α-transition consumes: `metaDepth p t ≤ k − 2`
  for every exitless path, discharged from the proved unconditional `ProofsRunExtract.metaDepth_le`.
  This is the M1 transition constraint that forbids the cheap infinite α-chain (the M0-telescope
  dips) and whose absence is exactly why the loose telescope undershoots `Dfr`.
* `M1WalkBound k` — the abstract slab bound (`excess ≥ Dfr` for every exitless path), stated in the
  additive frontier form; **it is `↔ ExcessFrontier k`** (`m1WalkBound_iff_excessFrontier`), the
  §3 residual that the computational certificate establishes for every tested `k`.
* `excessFrontier_of_m1` / `thm2_of_m1` / the `thm1v1 / thm1v2` capstones — the reduction from the
  M1 bound through the existing `thm2_of_frontier` / `ProofsMF` chains.

## The residual (see `PROGRESS-m1.md` §5)

The one piece not delivered *k-uniformly in Lean* is a symbolic form of the bonus `g*`: it has no
separable/closed form and its per-transition check is currently per-fixed-`k`.  `M1WalkBound k` is
therefore carried as the (computationally certified) hypothesis of the capstones — strictly finer
than, and independent of, the `JumpLoopEntryFreeRes1` graph-realizability residual
(`ProofsCascade`), which is *window-local* and ledger-consistent whereas the M1 bound is *global*
(the bonus `g*` carries credit across windows; `PROGRESS-m1.md` §4).  The soundness bridge (every
exitless path induces an M1-legal block walk) is already carried at path level by the Lean ledger:
`ProofsLedger.boundary_classify` (the five boundary kinds), `alphaCap` (this file), and — for the
reset-only-from-complete exclusion — the FILL lemma `ProofsFill.markerMove_from_complete_fill_le`
(a hypothesis until it lands).

Namespace `Hunter.ProofsM1`; the capstones live in `Hunter.Proved`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsM1

open ProofsLedger ProofsRecursion ProofsRunExtract ProofsCascade ProofsFinal
open HPath

variable {k : ℕ}

/-! ## §1. The demand side — per-block plateau

The M1 certificate's demand increment `δ(b) = Dfr(b) − Dfr(b−1)` is `∈ {0,1}` and jumps only at the
block-opening vertex.  In Lean's vertex indexing this is exactly `ProofsCascade.dfr_plateau`: in the
recursion region (and, via the closed form, everywhere) the additive frontier value is unchanged
across any vertex `ℓ` with `ℓ % k ≠ 1`.  We restate it under the M1 name it plays in the certificate
(the *door step carries no demand* half of the per-transition table). -/

/-- **Per-block demand plateau** (M1 demand side).  For every `ℓ ≥ 2` with `ℓ % k ≠ 1` the frontier
demand does not increase from `ℓ − 1` to `ℓ`: additively,
`j_k(ℓ) + (ℓ−2) + (⌈(ℓ−1)/k⌉−1) = j_k(ℓ−1) + (ℓ−1) + (⌈ℓ/k⌉−1)`.  This is the demand half of the
`door` per-transition inequality (cost `0`, `δ = 0`).  Repackaging of `ProofsCascade.dfr_plateau`. -/
theorem demand_plateau_block (hk : 3 ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hmod : ℓ % k ≠ 1) :
    j k ℓ + (ℓ - 2) + ((ℓ - 1) ⌈/⌉ k - 1) = j k (ℓ - 1) + (ℓ - 1) + (ℓ ⌈/⌉ k - 1) :=
  ProofsCascade.dfr_plateau hk ℓ hℓ hmod

/-- **Per-window demand shift** (M1 demand side).  One `ℓ₀`-window carries exactly `k − 2` units of
demand: `Dfr(m) = Dfr(m − ℓ₀) + (k − 2)` (additive).  This is the aggregate the α-run + its
terminator must pay in the certificate.  Repackaging of `ProofsCascade.dfr_shift`. -/
theorem demand_window_shift (hk : 3 ≤ k) (m : ℕ) (hm : k * (k - 1) * (k - 2) < m) :
    j k m + (m - ell0 k - 1) + ((m - ell0 k) ⌈/⌉ k - 1)
      = j k (m - ell0 k) + (m - 1) + (m ⌈/⌉ k - 1) + (k - 2) :=
  ProofsCascade.dfr_shift hk m hm

/-! ## §2. The α-run cap — the M1 transition constraint, discharged

The certificate's α-transition (cost `1`, from a *complete* 2-loop, continuing the run) is legal
only while the run has `< k − 2` completed 2-loops behind it — the cap `metaDepth ≤ k − 2`.  This is
the constraint that forbids the cheap infinite α-chain undercutting `Dfr` (the M0-telescope's dips).
It is the proved unconditional `ProofsRunExtract.metaDepth_le`; we expose it under the M1 name. -/

/-- **The α-run cap** consumed by the M1 α-transition: for every exitless path and every block `t`
in range, the meta-depth (complete 2-loops chained by α since the last meta-heavy) is `≤ k − 2`.
Discharged from the proved `metaDepth_le` — no residual. -/
theorem alphaCap (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) : metaDepth p t ≤ k - 2 :=
  metaDepth_le hk hp t hN

/-- **Each run-internal α banks one unit of excess.**  Along the extracted run every α boundary is
weight-3 (`bw = 3`), contributing exactly `bw − 2 = 1` to the excess, and the run has `≤ k − 2`
completed 2-loops.  This is the α column of the per-transition table (cost `1`), read straight off
`ProofsRunExtract.run_payment`. -/
theorem alpha_banks_one (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) :
    metaDepth p t ≤ k - 2 ∧
    ∀ c, 1 ≤ c → c ≤ metaDepth p t → bw p (runStart p t + c * (k - 1)) = 3 :=
  run_payment hk hp t hN

/-! ## §3. The abstract M1 slab bound and the reduction to `ExcessFrontier`

`M1WalkBound k` is the abstract slab bound: every exitless path spends excess at least the frontier
demand `Dfr` — the statement the min-excess slab DP establishes (0 dips at every recursion corner,
`k = 5,6,7,8`, via the bounded potential `g*`; `PROGRESS-m1.md` §3).  It is stated in the additive
frontier form, and is **definitionally the `ExcessFrontier` inequality** — the M1 program's content
is the *proof that it holds* (the per-transition potential certificate), carried computationally.
Here we record the interface and thread it to all Theorem-2 / Theorem-1 capstones. -/

/-- **The abstract M1 slab bound.**  Every exitless path spends excess at least the frontier demand:
`j_k(ℓ) ≤ (ℓ−1) + (⌈ℓ/k⌉−1) + excess q`.  Established by the min-excess slab DP (the potential
certificate of `PROGRESS-m1.md` §3, 0 failures at `k = 5,6,7,8`), strictly finer than the
`JumpLoopEntryFreeRes1` graph residual (`PROGRESS-m1.md` §4). -/
def M1WalkBound (k : ℕ) : Prop :=
  ∀ q : HPath k, q.Exitless → 0 < q.numVerts →
    j k q.numVerts ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q

/-- **`M1WalkBound k ↔ ExcessFrontier k`.**  The M1 slab bound *is* the frontier bound: the slab DP
targets exactly the frontier demand.  The equivalence makes the M1 route a genuine substitute for
the `Res1`/`JumpLoopEntryFree` routes into `ExcessFrontier`. -/
theorem m1WalkBound_iff_excessFrontier : M1WalkBound k ↔ ExcessFrontier k := Iff.rfl

/-- **`ExcessFrontier` from the M1 slab bound.** -/
theorem excessFrontier_of_m1 (hM1 : M1WalkBound k) : ExcessFrontier k :=
  m1WalkBound_iff_excessFrontier.mp hM1

end ProofsM1

/-! ## §4. The `Hunter.Proved` capstones from the M1 slab bound

The M1 slab certificate delivers `ExcessFrontier k`, from which every Theorem-2 / Theorem-1 capstone
follows through the existing `thm2_of_frontier` / `ProofsFinal.frontierTightHeavy_of_excessFrontier`
/ `ProofsMF` chains — identically to the `Res1` capstones (`ProofsCascade`), but from the M1 bound
(a global finite-state DP fact) rather than the window-local graph residual. -/

namespace Proved

open ProofsRecursion ProofsSynthesis ProofsFinal ProofsM1

/-- **`ExcessFrontier` from the M1 slab bound.** -/
theorem excessFrontier_of_m1 {k : ℕ} (hM1 : M1WalkBound k) : ExcessFrontier k :=
  ProofsM1.excessFrontier_of_m1 hM1

/-- **`FrontierTightHeavy` from the M1 slab bound.** -/
theorem frontierTightHeavy_of_m1 {k : ℕ} (hk : 3 ≤ k) (hM1 : M1WalkBound k) :
    FrontierTightHeavy k :=
  frontierTightHeavy_of_excessFrontier hk (ProofsM1.excessFrontier_of_m1 hM1)

/-- **Theorem 2 from the M1 slab bound** (verbatim `Statements.thm2` conclusion). -/
theorem thm2_of_m1 {k ℓ : ℕ} (hk : 3 ≤ k) (hM1 : M1WalkBound k) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (ProofsM1.excessFrontier_of_m1 hM1) hℓ

/-- **The global M1 slab bound.** -/
def M1WalkBoundAll : Prop := ∀ k, 3 ≤ k → M1WalkBound k

/-- **Theorem 2, globally, from the M1 slab bound.** -/
theorem thm2_global_of_m1 (hM1 : M1WalkBoundAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  fun k _ℓ hk hℓ => thm2_of_m1 hk (hM1 k hk) hℓ

/-- `M1WalkBoundAll → FrontierTightHeavyAll` (= `(MF)` global). -/
theorem frontierTightHeavyAll_of_m1All (hM1 : M1WalkBoundAll) : FrontierTightHeavyAll :=
  fun k hk => frontierTightHeavy_of_excessFrontier hk (ProofsM1.excessFrontier_of_m1 (hM1 k hk))

/-- **thm1v1 from the M1 slab bound** (superpermutation form). -/
theorem thm1v1_of_m1 (hM1 : M1WalkBoundAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsMF.thm1v1_of_MF (frontierTightHeavyAll_of_m1All hM1) hproof hexists

/-- **thm1v2 from the M1 slab bound** (`L(k) ≥ coeff(k)·k! − O(1)`). -/
theorem thm1v2_of_m1 (hM1 : M1WalkBoundAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsMF.thm1v2_of_MF (frontierTightHeavyAll_of_m1All hM1) hproof hexists

end Proved

end Hunter

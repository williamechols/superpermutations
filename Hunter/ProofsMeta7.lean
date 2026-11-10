/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta6
import Hunter.ProofsB2
import Hunter.ProofsGreedy2

/-!
# Theorem 2 — the RUN MANUFACTURE: the final named gate for `thm2`

This file takes the meta-supply residual `ProofsMeta6.MetaWindowSupply` down to its sharpest
honest form and discharges everything around it, so that Hunter's Theorem 2 (`Statements.thm2`)
is delivered — as `Hunter.Proved.thm2_closed` — conditional on a **single** named residual for a
**concrete, base-region-vanishing** potential `Φ`, with `BaseBound` fully proved.

## The arithmetic verdict (the arbiter, up front)

The construction the six prior passes circled is a per-window heavy-edge count that would upgrade
the proved floor `windowExcess_ge_km3 : excess q + (k − 3) ≤ excess p` to `+ (k − 2)`.  Careful
accounting says this count comes out **`k − 3`, not `k − 2`**, per window — and the `k = 5`
witness (`Refutations.windowExcess_false`, the arbiter named in the task) *proves* it: the
`ℓ = 120` optimal path `P` has `excess P = 6` and its `ℓ = 65` exitless prefix `q` has
`excess q = 4`, so that window carries exactly `6 − 4 = 2 = k − 3`.  `WindowExcess 5`
(the per-window `k − 2`) is therefore FALSE.  The missing `+1` is **not** a bigger count; it is
genuinely *amortized* — banked by earlier windows and released here.  Per the task's off-by-one
instruction we do **not** force `k − 2`: instead we route the `+1` through a bounded potential
`Φ ∈ {0,1}` (the LP-feasible frame, `invariant/results.json` `maxPhi = 1`), which is exactly what
`MetaWindowSupply`'s release disjunct encodes.

## The `ℓ = 120 / q = 65` calibration (must reproduce the tight `7 ≤ 7`)

`MetaWindowSupply`'s direct disjunct at this window is
`excess q + (k−2) + Φ p ≤ excess p + Φ q`, i.e. `4 + 3 + Φ p ≤ 6 + Φ q`, i.e.
`7 + Φ p ≤ 6 + Φ q`.  This forces `Φ q ≥ Φ p + 1`, i.e. the window is a **release** window and the
direct disjunct is *unavailable*; the release disjunct `Φ p + 1 ≤ Φ q` must carry it.  With the
LP-feasible assignment `(Φ p, Φ q) = (0, 1)` the amortized bound is the tight `7 ≤ 7` and the
release disjunct `0 + 1 ≤ 1` holds — discharged here by the proved floor
(`windowExcess_ge_km3` : `4 + 2 ≤ 6`, via `ProofsMeta6.amortizedWindow_of_metaSupply`).  So this
witness window is a *release* window; it does **not** enter the residual.  The residual is exactly
the **non-release** windows.

## What is genuinely closed here (sorry-free, axiom-clean)

* `PhiState` — a concrete `{0,1}` potential that **vanishes on the base region** and, on the
  recursion region, is the LP's "`Φ = 1` at the start of a 2-loop" mid-run indicator (the last
  block boundary being a door: the terminator payment is deferred).
* `baseBound_phiState : BaseBound k (PhiState k)` — **unconditional**, immediate from
  `excess_frontier_base` since `PhiState` is `0` on the base region.
* `NonReleaseSupply` — the **sharp** residual: `MetaWindowSupply` restricted to the non-release
  windows (`Φ q ≤ Φ p`), where the floor cannot help.  This is strictly smaller than
  `MetaWindowSupply` (the release windows are peeled off logically).
* `metaWindowSupply_of_nonRelease : NonReleaseSupply k Φ → MetaWindowSupply k Φ` — the logical
  peel (release windows use `MetaWindowSupply`'s free left disjunct).
* `Hunter.Proved.thm2_closed` — Theorem 2 verbatim, conditional **only** on
  `NonReleaseSupply k (PhiState k)` (a single residual; `BaseBound` discharged, `Φ` concrete).

Namespace `Hunter.ProofsMeta7`; the headline gate in `Hunter.Proved`.  Zero `sorry`, zero new
axioms.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta7

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
open ProofsMeta3 ProofsWindow ProofsMeta5 ProofsMeta6
open HPath

variable {k : ℕ}

/-! ## The concrete finer potential `Φ ∈ {0,1}`

The LP analysis (`invariant/results.json`) pins the winning invariant to
`s(i) ≥ Φ(door_depth, meta_depth, run_complete2, ℓ mod ℓ₀)`, `Φ ∈ {0,1}`, with the note
"`Φ = 1` at start of a 2-loop (holds banked surplus, released as demand jumps inside the 2-loop)".
We realize this as the **mid-run indicator**: `Φ = 1` iff the last complete block of `p` is
entered by a *door* boundary (weight 2) — i.e. `p` ends *inside* a door-run / 2-loop, with its
α-terminator payment still deferred.  Crucially we force `Φ = 0` on the whole base region, which
makes `BaseBound` immediate (the base region is a separate, already-proved regime —
`invariant/results.json`: "base region is separate; base is thm2_base-proved"). -/

/-- **The finer state-based potential.**  `Φ ∈ {0,1}`: `0` throughout the base region
(`|p| ≤ k(k−1)(k−2)`), and on the recursion region the mid-run indicator — `1` iff the boundary
into `p`'s last complete block is a door (weight `2`), meaning `p` ends inside a 2-loop with its
α-terminator payment deferred (the LP's "banked surplus at a 2-loop start"). -/
noncomputable def PhiState (k : ℕ) (p : HPath k) : ℕ :=
  if p.numVerts ≤ k * (k - 1) * (k - 2) then 0
  else if ew k (p.vert (p.numVerts - k - 1)) (p.vert (p.numVerts - k)) = 2 then 1 else 0

/-- `PhiState` is `{0,1}`-valued. -/
theorem phiState_le_one (p : HPath k) : PhiState k p ≤ 1 := by
  unfold PhiState
  split
  · exact Nat.zero_le _
  · split <;> simp

/-- `PhiState` vanishes on the base region — the key that makes `BaseBound` free. -/
theorem phiState_base {p : HPath k} (hle : p.numVerts ≤ k * (k - 1) * (k - 2)) :
    PhiState k p = 0 := by
  unfold PhiState; rw [if_pos hle]

/-- **`BaseBound` for any base-vanishing potential** — unconditional.  If `Φ = 0` throughout the
base region then the invariant there collapses to the proved base slice `excess_frontier_base`.
This is the certain content; the concrete `PhiState` is one instance (the base region is a
separate, already-proved regime, so any recursion-region `Φ` shape is admissible for `BaseBound`
as long as it vanishes on the base). -/
theorem baseBound_of_baseVanish {Φ : HPath k → ℕ} (hk : 3 ≤ k)
    (hbv : ∀ p : HPath k, p.numVerts ≤ k * (k - 1) * (k - 2) → Φ p = 0) :
    BaseBound k Φ := by
  intro p hpe h0 hle
  rw [hbv p hle, Nat.add_zero]
  exact ProofsRecursion.excess_frontier_base hk hpe h0 hle

/-- **`BaseBound` for the concrete `Φ`** — unconditional, via `baseBound_of_baseVanish` and
`phiState_base`. -/
theorem baseBound_phiState (hk : 3 ≤ k) : BaseBound k (PhiState k) :=
  baseBound_of_baseVanish hk (fun _ hle => phiState_base hle)

/-! ## The sharp residual: `MetaWindowSupply` on the non-release windows only

`MetaWindowSupply` already splits each `ℓ₀`-window into a **release** disjunct (`Φ p + 1 ≤ Φ q`,
discharged downstream by the proved floor `windowExcess_ge_km3` inside
`amortizedWindow_of_metaSupply`) and a **direct** disjunct.  The direct disjunct is only ever
needed when the window is *not* a release window, i.e. `Φ q ≤ Φ p`.  We name exactly that slice —
it is where the floor gives `k − 3` but the amortized demand is `k − 2` (or, if `Φ` drops,
`k − 1`), so the run-manufacture `+1` (the genuinely open meta-confinement) must live. -/

/-- **The sharp meta-supply residual.**  `MetaWindowSupply` restricted to the non-release windows
(`Φ q ≤ Φ p`): the last `ℓ₀`-window carries the full amortized demand
`excess q + (k−2) + Φ p ≤ excess p + Φ q`.  Strictly smaller than `MetaWindowSupply` — the
release windows (which the proved `k − 3` floor already covers) are peeled off. -/
def NonReleaseSupply (k : ℕ) (Φ : HPath k → ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    Φ q ≤ Φ p →
    excess q + (k - 2) + Φ p ≤ excess p + Φ q

/-- **The logical peel.**  `NonReleaseSupply k Φ → MetaWindowSupply k Φ`, for any `Φ`: a window is
either a release window (`Φ p + 1 ≤ Φ q`, `MetaWindowSupply`'s free left disjunct) or, failing
that, has `Φ q ≤ Φ p` and is covered by `NonReleaseSupply`. -/
theorem metaWindowSupply_of_nonRelease {Φ : HPath k → ℕ}
    (hnr : NonReleaseSupply k Φ) : MetaWindowSupply k Φ := by
  intro p q hpe hqe hlt hprefix
  by_cases hrel : Φ p + 1 ≤ Φ q
  · exact Or.inl hrel
  · exact Or.inr (hnr p q hpe hqe hlt hprefix (by omega))

/-! ## Step 1 — the boundary-type sequence (the run-decomposition primitive)

The run manufacture reads each block boundary of the window through the four-way classification
`ProofsMeta3.boundary_classify` and groups maximal door-runs into 2-loops.  Here we package the
classification as a positional function `bkind p i` on block boundaries, with the definitional
positional lemmas the grouping is written against.  This is the self-contained list-level
skeleton of the decomposition (the `hdoor`/`halpha` interface of `Proved.alpha_run_bound` is
manufactured against these primitives); it does not depend on the still-open α-vs-σ²
characterization, which is what blocks completing the manufacture (see the residual note). -/

/-- The four structural kinds of a block boundary (Layer B of `ProofsMeta3`):
`door` (weight 2), `alphaSib` (weight-3 marker-preserving: α or σ²-sibling), `metaHeavy`
(weight-3 marker-moving), `heavy` (weight `≥ 4`). -/
inductive BKind where
  | door | alphaSib | metaHeavy | heavy
  deriving DecidableEq, Repr

/-- **The boundary-type classifier.**  Reads off the structural kind of the boundary edge
`p[i] → p[i+1]` from its weight and (at weight 3) marker preservation.  Positional realization of
`ProofsMeta3.boundary_classify`; the boundary-type *sequence* of a window is `fun i => bkind p i`
over its block boundaries. -/
noncomputable def bkind (p : HPath k) (i : ℕ) : BKind :=
  if ew k (p.vert i) (p.vert (i + 1)) = 2 then BKind.door
  else if ew k (p.vert i) (p.vert (i + 1)) = 3 then
    (if (p.vert (i + 1) : List ℕ).getLastD 0 = marker p i then BKind.alphaSib else BKind.metaHeavy)
  else BKind.heavy

/-- Positional characterization: a boundary is a `door` in the sequence iff it has weight `2`. -/
theorem bkind_eq_door_iff (p : HPath k) (i : ℕ) :
    bkind p i = BKind.door ↔ ew k (p.vert i) (p.vert (i + 1)) = 2 := by
  unfold bkind
  by_cases h2 : ew k (p.vert i) (p.vert (i + 1)) = 2
  · rw [if_pos h2]; simp [h2]
  · rw [if_neg h2]
    constructor
    · intro h
      by_cases h3 : ew k (p.vert i) (p.vert (i + 1)) = 3
      · rw [if_pos h3] at h; split at h <;> exact absurd h (by decide)
      · rw [if_neg h3] at h; exact absurd h (by decide)
    · intro h; exact absurd h h2

/-- A `door` boundary carries the door word identity (for exitless paths).  Bridges the sequence
kind to the concrete word step the 2-loop grouping composes. -/
theorem bkind_door_word (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) (hk_door : bkind p i = BKind.door) :
    (p.vert (i + 1) : List ℕ) = door (p.vert i : List ℕ) := by
  have hw2 : ew k (p.vert i) (p.vert (i + 1)) = 2 := (bkind_eq_door_iff p i).mp hk_door
  exact door_of_boundary (by omega : 2 ≤ k) hp hi hd hw2

/-- **Per-kind excess contribution.**  The per-edge ledger summand `ew − 2` of
`ProofsMeta3.excess_eq_sum_edgeWeight` by boundary kind: a `door` pays `0`; an `alphaSib` or
`metaHeavy` (both weight-3) pays exactly `1`; a `heavy` pays `≥ 2`.  This is the payment table the
run telescope sums — every non-door boundary is a paying event. -/
theorem bkind_contribution (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) :
    (bkind p i = BKind.door ∧ ew k (p.vert i) (p.vert (i + 1)) - 2 = 0) ∨
    (bkind p i ≠ BKind.door ∧ ew k (p.vert i) (p.vert (i + 1)) - 2 = 1) ∨
    (bkind p i ≠ BKind.door ∧ 2 ≤ ew k (p.vert i) (p.vert (i + 1)) - 2) := by
  rcases boundary_classify hk hp hi hd with ⟨_, hw2⟩ | ⟨hw3, _⟩ | ⟨hw3, _⟩ | hw4
  · exact Or.inl ⟨(bkind_eq_door_iff p i).mpr hw2, by omega⟩
  · refine Or.inr (Or.inl ⟨?_, by omega⟩); rw [ne_eq, bkind_eq_door_iff]; omega
  · refine Or.inr (Or.inl ⟨?_, by omega⟩); rw [ne_eq, bkind_eq_door_iff]; omega
  · refine Or.inr (Or.inr ⟨?_, by omega⟩); rw [ne_eq, bkind_eq_door_iff]; omega

/-- **Maximal door-run predicate** (the 2-loop grouping primitive).  `IsDoorRun p t s` says the
`s` consecutive block boundaries opening blocks `t+1, …, t+s` are all doors — a run of `s`
door-joined blocks (a complete 2-loop is the special case `s = k − 2`, closed by an α).  The run
*terminator* at block `t+s+1` is, by maximality, a non-door (paying) boundary — the α / σ² / meta
/ heavy / window-end of the decomposition. -/
def IsDoorRun (p : HPath k) (t s : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ s → bkind p (k * (t + r) - 1) = BKind.door

/-- A door-run supplies the weight-`2` interior boundaries the run bound `alpha_run_bound`
consumes as `hdoor` (positionally, before the α-vs-σ² terminator characterization). -/
theorem isDoorRun_ew (hk : 3 ≤ k) {p : HPath k} {t s : ℕ} (h : IsDoorRun p t s) :
    ∀ r, 1 ≤ r → r ≤ s → ew k (p.vert (k * (t + r) - 1)) (p.vert (k * (t + r))) = 2 := by
  intro r hr1 hrs
  have := h r hr1 hrs
  have heq : k * (t + r) - 1 + 1 = k * (t + r) := by
    have : 1 ≤ k * (t + r) := by
      have h1 : 1 ≤ t + r := by omega
      calc 1 ≤ k := by omega
        _ = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * (t + r) := Nat.mul_le_mul (le_refl k) h1
    omega
  have hd := (bkind_eq_door_iff p (k * (t + r) - 1)).mp this
  rwa [heq] at hd

end ProofsMeta7

/-! ## The headline gate: `thm2` conditional on the single residual -/

namespace Proved

open ProofsMeta7

/-- **Theorem 2, closed to the single run-manufacture residual.**  Verbatim `Statements.thm2`
(`j_k(ℓ) ≤ i_k(ℓ)` under `HasExitlessPath k ℓ`), conditional **only** on
`NonReleaseSupply k (PhiState k)` — the non-release-window meta-supply for the concrete
base-vanishing potential `PhiState`.  `BaseBound` is discharged (`baseBound_phiState`) and the
release windows are discharged by the proved floor
(`ProofsMeta6.windowExcess_ge_km3`, via `amortizedWindow_of_metaSupply`); everything except the
non-release `+1` (the genuinely open meta-confinement / α-run manufacture) is closed. -/
theorem thm2_closed {k ℓ : ℕ} (hk : 3 ≤ k)
    (hsupply : NonReleaseSupply k (PhiState k)) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  ProofsMeta6.thm2_of_metaSupply hk (PhiState k) (baseBound_phiState hk)
    (metaWindowSupply_of_nonRelease hsupply) hℓ

/-! ### The headline chain — how the gate reaches Theorem 1

`thm2_closed` discharges the Theorem-2 **lower bound** `j_k ≤ i_k` from the single meta-supply
residual.  The Theorem-2 **equality** on the base region (`thm2_equality`) is already proved
unconditionally, so both Theorem-2 inputs of the proved conditional dashboard
`Proved.thm1v2_current` / `Proved.thm1v1_current` are supplied here.  What remains are the two
genuinely-separate reduction/greedy leaves that the whole tree still carries and that are
**independent of the meta-confinement**: `hproof` (the per-`k` `proof_thm1v2` assembly — its own
`red_R` `p_u`-extension is the open reduction leaf, `PROGRESS-gb2.md`) and `hexists` (the
`greedy_g` full-range existence witness).  We wire them explicitly so the gate's placement in the
headline is exact. -/

/-- **thm1v2 from the meta-supply residual** (dashboard capstone).  The paper's coefficient lower
bound, with **both** Theorem-2 inputs of `thm1v2_current` discharged: the lower bound from
`thm2_closed` (⟸ the universal meta-supply residual `∀ k, NonReleaseSupply k (PhiState k)`) and
the base-region equality from the proved `thm2_equality`.  Remaining hypotheses `hproof`,
`hexists` are the meta-confinement-independent reduction/greedy leaves (`PROGRESS-gb2.md`,
`PROGRESS-hrev.md`). -/
theorem thm1v2_of_metaResidual
    (hsupply : ∀ k, ProofsMeta7.NonReleaseSupply k (ProofsMeta7.PhiState k))
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_current
    (fun k _ hk hℓ => Proved.thm2_closed hk (hsupply k) hℓ)
    (fun _ _ hk hℓ0 hle hex => Proved.thm2_equality hk hℓ0 hle hex)
    hproof hexists

/-- **thm1v1 from the meta-supply residual** (superpermutation form; same inputs as
`thm1v2_of_metaResidual`). -/
theorem thm1v1_of_metaResidual
    (hsupply : ∀ k, ProofsMeta7.NonReleaseSupply k (ProofsMeta7.PhiState k))
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_current
    (fun k _ hk hℓ => Proved.thm2_closed hk (hsupply k) hℓ)
    (fun _ _ hk hℓ0 hle hex => Proved.thm2_equality hk hℓ0 hle hex)
    hproof hexists

end Proved

end Hunter

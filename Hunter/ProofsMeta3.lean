/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta2
import Hunter.ProofsWindow

/-!
# Theorem 2 — final assembly, step (iv): path→run decomposition and the excess counting layer

This file continues `Hunter.ProofsMeta2` (which proves `meta_confinement`, the meta-pigeonhole
"an α-run of complete 2-loops has `m ≤ k−2`").  Step (iv) turns the *local* meta-confinement into
the *global* frontier `ExcessFrontier k` by

1. **the exact excess counting identity** — `excess p = Σ_i (ew_i − 2)`, the per-edge form of
   `excess = Σ_{r=3}^{k} edgeCountGe·r`.  Every edge of weight `w` contributes `(w − 2)⁺`; only
   the block-boundary edges (weight `≥ 2`) contribute, and interior `σ`-steps (weight 1)
   contribute `0`.  This is the ledger the whole telescope is written against.

2. **the block-boundary classification** — for an exitless path, every boundary edge is exactly
   one of: a **door** (weight 2, `excess` contribution 0), a **weight-3** edge (contribution 1,
   split by `weight3_marker_edge_cases` into the marker-preserving α / σ²-sibling and the
   marker-moving meta-heavy), or a **weight `≥ 4`** edge (contribution `≥ 2`).

Namespace `Hunter.ProofsMeta3`.  Everything here is sorry-free and axiom-clean.
-/

namespace Hunter

namespace ProofsMeta3

open ProofsRecursion ProofsMeta ProofsWindow ProofsConfinement

variable {k : ℕ}

/-! ## Layer A — the exact excess counting identity

`excess p = Σ_{r=3}^{k} edgeCountGe p r`.  Swapping the double sum (as in
`wtP_eq_sum_edgeCountGe`) turns this into a per-edge sum whose `i`-th term counts the layers
`r ∈ [3,k]` with `r ≤ ew_i`, i.e. `(ew_i − 2)` (truncated).  This is the level-agnostic ledger:
the excess is literally the total weight carried by edges *beyond their first two units*. -/

/-- Layer-cake for the excess: `∑_{q=3}^{k} [q ≤ e] = e − 2` whenever `e ≤ k` (truncated ℕ
subtraction, so also correct for `e < 3`). -/
theorem sum_indicator_Icc3 {e : ℕ} (hek : e ≤ k) :
    ∑ q ∈ Finset.Icc 3 k, (if q ≤ e then (1 : ℕ) else 0) = e - 2 := by
  rw [← Finset.card_filter]
  have hfilt : (Finset.Icc 3 k).filter (fun q => q ≤ e) = Finset.Icc 3 e := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt, Nat.card_Icc]
  omega

/-- **The excess counting identity.**  `excess p = Σ_i (ew_i − 2)`, the per-edge "weight beyond
two" sum over all `numVerts − 1` edges.  This is the exact analogue of `wtP_eq_sum_edgeCountGe`
one layer up (starting the layer-cake at `r = 3` instead of `r = 1`). -/
theorem excess_eq_sum_edgeWeight (hk : 1 ≤ k) (p : HPath k) :
    excess p = ∑ i ∈ Finset.range (p.numVerts - 1),
      (ew k (p.vert i) (p.vert (i + 1)) - 2) := by
  have key : ∀ q : ℕ, edgeCountGe p q = ∑ i ∈ Finset.range (p.numVerts - 1),
      (if q ≤ ew k (p.vert i) (p.vert (i + 1)) then (1 : ℕ) else 0) := by
    intro q; rw [edgeCountGe, Finset.card_filter]
  rw [excess]
  simp_rw [key]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_indicator_Icc3 (ew_le_k hk _ _)

/-! ## Layer B — the block-boundary classification

Every block-boundary edge of an exitless path (`k ∣ i+1`, `boundary_ge_two`) is one of four
mutually-exclusive kinds, together with its exact `excess` contribution `(ew − 2)`:

* **door** — weight 2, `p[i+1] = door(p[i])`, contributes `0`;
* **α / σ²-sibling** — weight 3, marker-preserving, `p[i+1] ∈ {alphaWord, sigmaSqWord}(p[i])`,
  contributes `1`;
* **meta-heavy weight-3** — weight 3, marker-moving, contributes `1`;
* **heavy** — weight `≥ 4`, contributes `≥ 2`.

This is `door_of_boundary` + `weight3_marker_edge_cases` assembled into a single case split, the
qualitative skeleton the run decomposition groups into 2-loops and α-runs. -/

/-- The **marker** tracked at block start `p[i]`: the last symbol of `rho (p[i])` — the symbol
whose position separates the (fixed) meta-marker from the moving one.  A weight-3 boundary is
*marker-preserving* iff `p[i+1]` keeps this symbol last. -/
def marker (p : HPath k) (i : ℕ) : ℕ := (rho (p.vert i : List ℕ)).getLastD 0

/-- **Block-boundary classification.**  For an exitless path, every boundary edge falls into
exactly one of the four structural kinds, each pinned to its `ew` value (hence to its `excess`
contribution `ew − 2`). -/
theorem boundary_classify (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) :
    ((p.vert (i + 1) : List ℕ) = door (p.vert i : List ℕ) ∧
        ew k (p.vert i) (p.vert (i + 1)) = 2) ∨
    (ew k (p.vert i) (p.vert (i + 1)) = 3 ∧
        (p.vert (i + 1) : List ℕ).getLastD 0 = marker p i ∧
        ((p.vert (i + 1) : List ℕ) = alphaWord (p.vert i : List ℕ) ∨
         (p.vert (i + 1) : List ℕ) = sigmaSqWord (p.vert i : List ℕ))) ∨
    (ew k (p.vert i) (p.vert (i + 1)) = 3 ∧
        (p.vert (i + 1) : List ℕ).getLastD 0 ≠ marker p i) ∨
    (4 ≤ ew k (p.vert i) (p.vert (i + 1))) := by
  have hk2 : 2 ≤ k := by omega
  have h2 := boundary_ge_two (by omega : 1 ≤ k) hp hi hd
  set w := ew k (p.vert i) (p.vert (i + 1)) with hwdef
  -- split on the weight value
  rcases (by omega : w = 2 ∨ w = 3 ∨ 4 ≤ w) with hw2 | hw3 | hw4
  · exact Or.inl ⟨door_of_boundary hk2 hp hi hd hw2, hw2⟩
  · -- weight 3: split on marker preservation
    by_cases hmark : (p.vert (i + 1) : List ℕ).getLastD 0 = marker p i
    · refine Or.inr (Or.inl ⟨hw3, hmark, ?_⟩)
      exact weight3_marker_edge_cases hk hw3 hmark
    · exact Or.inr (Or.inr (Or.inl ⟨hw3, hmark⟩))
  · exact Or.inr (Or.inr (Or.inr hw4))

/-- **Excess contribution ledger.**  A door boundary contributes `0` to the excess, a weight-3
boundary (α, σ²-sibling, or meta-heavy) contributes exactly `1`, a weight-`≥4` boundary
contributes `≥ 2`.  The per-edge summand of `excess_eq_sum_edgeWeight` is `ew − 2`; the
classification pins it to `{0, 1, ≥2}`. -/
theorem boundary_contribution (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) :
    (ew k (p.vert i) (p.vert (i + 1)) - 2 = 0 ∧
        (p.vert (i + 1) : List ℕ) = door (p.vert i : List ℕ)) ∨
    (ew k (p.vert i) (p.vert (i + 1)) - 2 = 1) ∨
    (2 ≤ ew k (p.vert i) (p.vert (i + 1)) - 2) := by
  rcases boundary_classify hk hp hi hd with ⟨hdoor, hw2⟩ | ⟨hw3, _⟩ | ⟨hw3, _⟩ | hw4
  · exact Or.inl ⟨by omega, hdoor⟩
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-! ## Layer C — the amortized telescope: status, the exact demand, and the obstruction

With Layers A+B the excess is written as a per-boundary ledger `excess p = Σ_i (ew_i − 2)`,
each boundary contributing `0` (door), `1` (weight-3: α / σ²-sibling / meta-heavy) or `≥ 2`
(weight `≥ 4`).  `ExcessFrontier k` demands, for every exitless `q` of length `ℓ`,

  `excess q  ≥  Dfr(ℓ) := j_k(ℓ) − (ℓ−1) − (⌈ℓ/k⌉−1)`.

**The exact demand (computed, `k = 5`).**  `Dfr` splits as `Dfr(ℓ) = Dbase(ℓ) + deficit(ℓ)` with
`Dbase(ℓ) = ⌈ℓ/(k(k−1))⌉ − 1` already delivered unconditionally by `excess_ge_Dbase` (level-2).
The *deficit* obeys the clean recursion `Dfr(ℓ) = Dfr(ℓ − ℓ₀) + (k−2)` on the recursion region
(`ℓ₀ = k(k−1)(k−2) − k = 55`), while `Dbase` grows by only `ℓ₀/(k(k−1)) = (k−2) − 1/(k−1)` per
window — so `deficit(ℓ)` **grows without bound** at rate `1/(k−1)` per window, i.e.
`≈ ℓ/((k−1)·ℓ₀)` (numerically `≈ ℓ/220` for `k = 5`; e.g. `deficit(120) = 1`,
`deficit(3158) = 15`).  Calibration against the `ℓ = 120`
witness of `Refutations` (`excess = 6`, histogram `{1:96, 2:18, 3:4, 4:1}`): `Dfr(120) = 6`
exactly — the frontier is **tight** there, and the counting `excess = 4·1 + 1·2 = 6` (four
weight-3 + one weight-4 boundary, via Layer A) reproduces the witness.  So the ledger is aligned.

**Why the telescope is not a per-window peel.**  The natural local reduction
`WindowExcess k : excess q + (k−2) ≤ excess p` (peel one `ℓ₀`-window) is **FALSE at `k = 5`**
(`Refutations.windowExcess_false`): the top window of the `ℓ = 120` witness carries only `2 < 3`
excess because earlier windows *overpaid* (the first 64 edges carry excess `4` against demand
`Dfr(65) = 3`).  Because `deficit` is unbounded, no bounded finite check settles it either.  The
frontier is genuinely *cumulative*: the induction must carry the accumulated surplus, matching
the invariant analysis's amortized potential `s(i) = excess(p[:i]) − Dfr(i) ≥ Φ(state) ∈ {0,1}`
(structural-only potentials are LP-INFEASIBLE — the `ℓ mod ℓ₀` phase coordinate is load-bearing).

**What remains (the construction this file does not build).**  The `hstep`/`hblk`/`hcyc` inputs
of `ProofsMeta2.meta_confinement` must be *constructed from an actual exitless path*: for a
maximal α-run, take the 2-loop block-starts `Astar j`, and prove the word-level exact identity
`(Astar (j+1)).erase α₁ = door((Astar j).erase α₁ .rotate (k−2))` by composing the `k−2` internal
door boundaries (`metaWord_door_step`) with the terminating α (`metaWord_alpha_step`) — all
against the **fixed** run-marker `α₁`, reconciling it with the *dynamic* per-step marker of
`metaWord_door_step` at the exact-word (not just rotation-class) level.  Then the amortized
telescope over blocks, carrying `Φ ∈ {0,1}`, converts `meta_confinement`'s per-run bound
`m ≤ k−2` into `excess q ≥ Dfr(ℓ)` cumulatively.  Both are substantial, independent of the
Layer A/B ledger built here, which is the ledger any such telescope is written against. -/

end ProofsMeta3

end Hunter

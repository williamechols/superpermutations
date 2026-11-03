/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsClose

/-!
# The structural core of Hunter's Theorem 2 (the level-3 chart)

This file formalizes the *structural core* of the consolidated `ExcessFrontier` proof
(the adjudicated `PROOF.md`): the finite word-combinatorial facts that drive the induction
`F_E ≤ G(E)`.  Four targets, in the repo's `HPath`/ledger vocabulary:

1. `suffix_exitless` — a **block-aligned** suffix of an exitless path is exitless (the
   keystone that legitimizes the truncation steps of the induction), together with the
   excess split identity at a block boundary.
2. `S1` — deterministic weight-2: every exit has exactly one weight-2 successor in a fresh
   rotation class (the door `τ₂`), of period `k−1`.
3. `S2` — the six-case: after a full weight-2 run the 6 weight-3 successors split
   `3` revisits / `2` early-collisions / `1` full fresh run, with new-class run-lengths
   `[k−2, k−2, k−1]`.
4. the **closure lemma** — after the full level-3 chart every light (`≤3`) successor of the
   final exit revisits, so any continuation has weight `≥ 4`.

All helpers live in `namespace Hunter.ProofsChart`; the clean statements the sibling
induction consumes are exported as `Hunter.Proved.<name>`.
-/

namespace Hunter
namespace ProofsChart

open List
open scoped Classical
open ProofsExitless ProofsRecursion ProofsMeta3 ProofsLedger ProofsLedger2
open ProofsConfinement ProofsRunExtract Proved HPath

variable {k : ℕ}

/-! ## Target 1: `suffix_exitless`

The truncation keystone.  `PROOF.md §0`: exitlessness is a *block-local* property, so any
contiguous **block-aligned** sub-path of an exitless path is again exitless.  We prove the
suffix case (the induction only truncates from the front): dropping the first `B` vertices,
where `B` is a multiple of `k`, preserves `Exitless`.

The mechanism (verified against `suffix2.py`: all 24 block-aligned suffixes of a full k=5
path are exitless; mid-block suffixes are not): an early exit of the suffix at position `i`
would be a weight-`≥2` step `q[i]→q[i+1]`, forcing a block boundary `k ∣ (B+i+1)` in `p`;
but then `σ(q[i]) = σ(p[B+i]) = p[C]` is the *current block's start* `C = k⌊(B+i)/k⌋`, which
lies at `B ≤ C ≤ B+i` — hence inside the suffix at position `C−B ≤ i`, so `q` has no early
exit there. -/

/-- The block-start identity at a boundary: if `k ∣ (j+1)` then `σ(p[j])` is the start of the
block containing `j`, namely `p[k⌊j/k⌋]`.  (Extracted from the `vert_succ_ne` mechanism.) -/
theorem sigma_vert_eq_block_start (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {j : ℕ}
    (hj : j < p.numVerts) (hd : k ∣ (j + 1)) :
    sigma (p.vert j) = p.vert (k * (j / k)) := by
  have S0 := vert_eq_sigma_iter hk hp j hj
  have him := mod_eq_pred_of_dvd_succ hk hd
  rw [S0, ← Function.iterate_succ_apply' sigma (j % k) (p.vert (k * (j / k))),
      show (j % k).succ = k from by omega, sigma_iter_period]

/-- **Suffix exitless (block-aligned).**  For an exitless `p` and a block-aligned cut
`k ∣ B` with `B < |p|`, the length-`(|p|−B)` suffix is (the vertex list of) an exitless
path. -/
theorem suffix_exitless (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {B : ℕ}
    (hBdvd : k ∣ B) (hBlt : B < p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.drop B ∧ q.Exitless := by
  have hnv : p.numVerts = p.verts.length := rfl
  have hne : p.verts.drop B ≠ [] := by
    have : 0 < (p.verts.drop B).length := by rw [List.length_drop]; omega
    exact List.ne_nil_of_length_pos this
  have hnodup : (p.verts.drop B).Nodup := p.nodup.sublist (List.drop_sublist _ _)
  refine ⟨⟨p.verts.drop B, hne, hnodup⟩, rfl, ?_⟩
  set q : HPath k := ⟨p.verts.drop B, hne, hnodup⟩ with hqdef
  have hqnv : q.numVerts = p.numVerts - B := by
    show (p.verts.drop B).length = p.verts.length - B
    rw [List.length_drop]
  -- suffix reindexing: `q[i] = p[B+i]`
  have hqvert : ∀ i, i < q.numVerts → q.vert i = p.vert (B + i) := by
    intro i hi
    have hi' : B + i < p.numVerts := by rw [hqnv] at hi; omega
    rw [vert_getElem q hi, vert_getElem p hi']
    exact List.getElem_drop
  -- now: no early exit
  intro hEE
  obtain ⟨i, hi1, hi2, hi3⟩ := hEE
  have hBi1 : B + i + 1 < p.numVerts := by rw [hqnv] at hi1; omega
  have hBi : B + i < p.numVerts := by omega
  -- the weight-≥2 step forces a block boundary at `B+i+1`
  have hvi : q.vert i = p.vert (B + i) := hqvert i (by omega)
  have hvi1 : q.vert (i + 1) = p.vert (B + i + 1) := by
    have := hqvert (i + 1) hi1; rwa [show B + (i + 1) = B + i + 1 from by ring] at this
  have hw2 : 2 ≤ ew k (p.vert (B + i)) (p.vert (B + i + 1)) := by rw [← hvi, ← hvi1]; exact hi2
  have hbndry : k ∣ (B + i + 1) := by
    by_contra hnd
    have hone : ew k (p.vert (B + i)) (p.vert (B + i + 1)) = 1 :=
      (prp_periodicedges hk hp (i := B + i) hBi1).mpr hnd
    omega
  -- `σ(q[i]) = p[C]`, the current block's start `C = k⌊(B+i)/k⌋`, lands inside the suffix
  set C := k * ((B + i) / k) with hCdef
  have hsig : sigma (p.vert (B + i)) = p.vert C :=
    sigma_vert_eq_block_start hk hp hBi hbndry
  have hCge : B ≤ C := by
    obtain ⟨t, rfl⟩ := hBdvd
    rw [hCdef]
    have ht : t ≤ (k * t + i) / k := by
      calc t = (k * t) / k := (Nat.mul_div_cancel_left t hk).symm
        _ ≤ (k * t + i) / k := Nat.div_le_div_right (Nat.le_add_right _ _)
    exact Nat.mul_le_mul (le_refl k) ht
  have hCle : C ≤ B + i := by
    rw [hCdef]; exact Nat.mul_div_le (B + i) k
  -- `C - B` is a suffix index and `q[C−B] = p[C] = σ(q[i])`
  have hCBlt : C - B < q.numVerts := by rw [hqnv]; omega
  have hqCB : q.vert (C - B) = p.vert C := by
    have := hqvert (C - B) hCBlt
    rwa [show B + (C - B) = C from by omega] at this
  have hsigeq : sigma (q.vert i) = q.vert (C - B) := by rw [hvi, hsig, hqCB]
  -- so `σ(q[i]) ∈ q` at position `C − B ≤ i`, contradicting the early-exit strictness
  have hpos : q.pos (sigma (q.vert i)) = C - B := by rw [hsigeq]; exact pos_vert q hCBlt
  rw [hpos] at hi3
  omega

/-! ### The excess split identity at a block boundary (`PROOF.md §0` cost bookkeeping)

`excess p = (Σ over the first-`B` edges) + excess(suffix)`.  Per-edge excess `perEdgeExc p i`
= `Σ_{r=3}^{k} [r ≤ w(p[i]→p[i+1])]` = `max(w−2, 0)`; total excess is its sum over all edges;
splitting the position range at a block-aligned cut `B` gives the identity.  The sum over the
first `B` edges collects the excess "spent" before the cut, *including the boundary edge* at
position `B−1` into the suffix (which is the `w−2` term of `PROOF.md §0`). -/

/-- Per-edge excess: the `≥3`-weight contribution of the single edge `p[i]→p[i+1]`. -/
noncomputable def perEdgeExc (p : HPath k) (i : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 3 k, if r ≤ ew k (p.vert i) (p.vert (i + 1)) then 1 else 0

/-- `excess` is the sum of per-edge excesses over the `|p|−1` edges. -/
theorem excess_eq_sum_perEdge (p : HPath k) :
    excess p = ∑ i ∈ Finset.range (p.numVerts - 1), perEdgeExc p i := by
  simp only [excess, edgeCountGe, Finset.card_filter, perEdgeExc]
  rw [Finset.sum_comm]

/-- **Excess split at a block-aligned cut.**  For an exitless `p` and a block-aligned
`k ∣ B` with `B < |p|`, taking the suffix `q = drop B` (from `suffix_exitless`) yields
`excess p = (Σ_{j<B} perEdgeExc p j) + excess q`.  The first summand is the excess spent by
the first `B` edges (the prefix blocks plus the boundary edge into the suffix). -/
theorem excess_split (_hk : 1 ≤ k) {p : HPath k} (_hp : p.Exitless) {B : ℕ}
    (_hBdvd : k ∣ B) (hBlt : B < p.numVerts) {q : HPath k}
    (hq : q.verts = p.verts.drop B) :
    excess p = (∑ j ∈ Finset.range B, perEdgeExc p j) + excess q := by
  -- suffix reindexing on vertices, hence on `perEdgeExc`
  have hnv : p.numVerts = p.verts.length := rfl
  have hqnv : q.numVerts = p.numVerts - B := by
    show q.verts.length = p.verts.length - B
    rw [hq, List.length_drop]
  have hqvert : ∀ i, i < q.numVerts → q.vert i = p.vert (B + i) := by
    intro i hi
    have hi' : B + i < p.numVerts := by rw [hqnv] at hi; omega
    rw [vert_getElem q hi, vert_getElem p hi']
    simp only [hq]
    exact List.getElem_drop
  have hperEdge : ∀ i, i + 1 < q.numVerts → perEdgeExc q i = perEdgeExc p (B + i) := by
    intro i hi
    have hvi : q.vert i = p.vert (B + i) := hqvert i (by omega)
    have hvi1 : q.vert (i + 1) = p.vert (B + i + 1) := by
      have := hqvert (i + 1) hi; rwa [show B + (i + 1) = B + i + 1 from by ring] at this
    simp only [perEdgeExc, hvi, hvi1, Nat.add_assoc]
  -- excess q as a sum over the suffix edges, reindexed into `Ico B (|p|−1)`
  have hBle : B ≤ p.numVerts - 1 := by omega
  have hqpos := q.numVerts_pos
  have hqedges : (p.numVerts - 1) - B = q.numVerts - 1 := by rw [hqnv]; omega
  have hexcq : ∑ j ∈ Finset.Ico B (p.numVerts - 1), perEdgeExc p j = excess q := by
    rw [Finset.sum_Ico_eq_sum_range, excess_eq_sum_perEdge q, hqedges]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact (hperEdge i (by omega)).symm
  -- split the full edge range at `B`
  rw [excess_eq_sum_perEdge p, ← hexcq,
    ← Finset.sum_range_add_sum_Ico (fun j => perEdgeExc p j) hBle]

/-- Bridge: `perEdgeExc` equals the repo's per-edge `ew − 2` (edge weights are `≤ k`), so the
split identity may also be read in the `ew − 2` idiom of `excess_eq_sum_edgeWeight`. -/
theorem perEdgeExc_eq (hk : 1 ≤ k) (p : HPath k) (i : ℕ) :
    perEdgeExc p i = ew k (p.vert i) (p.vert (i + 1)) - 2 :=
  sum_indicator_Icc3 (ew_le_k hk _ _)

/-! ## Target 2: S1 — deterministic weight-2 (the door `τ₂`) and its period `k−1`

`PROOF.md §1`, verified `sublemmas.py` (to-new-class weight-2 count ≡ 1 for all vertices at
k=5,6,7).  Every block boundary of weight 2 is deterministically the **door** `τ`
(`door_of_boundary`), and a maximal run of consecutive door boundaries has at most `k−2`
interior doors — the door period `k−1` (`doorDepth_le_km2`).  Consolidated here into the two
forms the induction consumes, plus the clean **excess-0 block bound** `F_0 = k−1` (a run with
no positive jump spans at most `n = k−1` blocks). -/

/-- **Door determinism (S1).**  A weight-2 block boundary lands on the door `τ` of its exit —
the deterministic fresh-class weight-2 successor.  (Re-export of `door_of_boundary`.) -/
theorem s1_door_determinism (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1))
    (hw : ew k (p.vert i) (p.vert (i + 1)) = 2) :
    (p.vert (i + 1) : List ℕ) = door (p.vert i : List ℕ) :=
  door_of_boundary hk hp hi hd hw

/-- **Door period (S1).**  A maximal run of consecutive door boundaries ending at block `t`
has at most `k−2` interior doors — so a weight-0 run spans at most `k−1` blocks (the door
`τ₂` has period `k−1`).  (Re-export of `doorDepth_le_km2`.) -/
theorem s1_door_run_le (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t < p.numVerts) : doorDepth p t ≤ k - 2 :=
  doorDepth_le_km2 hk hp t hN

/-- If every boundary `1 … t` is a door, the door-depth at `t` is the full `t`. -/
theorem doorDepth_eq_of_all_doors (p : HPath k) (t : ℕ)
    (h : ∀ s, 1 ≤ s → s ≤ t → IsDoor p s) : doorDepth p t = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [doorDepth_door (h (t + 1) (by omega) (le_refl _)),
        ih (fun s hs1 hs2 => h s hs1 (by omega))]

/-- **Excess-0 block bound (S1, `F_0 = k−1`).**  An exitless path with no `≥3`-weight excess
spans at most `k−1` blocks: `|p| ≤ k(k−1)`.  Mechanism: excess 0 forces every boundary to be
a door (weight exactly 2), so the door-depth at the last block equals the block index, which
is capped at `k−2` by the door period — hence at most `k−1` blocks. -/
theorem excess_zero_block_bound (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (h0 : excess p = 0) : p.numVerts ≤ k * (k - 1) := by
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ p.numVerts := p.numVerts_pos
  set t := (p.numVerts - 1) / k with htdef
  have hkt : k * t ≤ p.numVerts - 1 := by
    rw [htdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hktlt : k * t < p.numVerts := by omega
  -- excess 0 ⇒ every edge has weight ≤ 2
  have hterm : ∀ i ∈ Finset.range (p.numVerts - 1),
      ew k (p.vert i) (p.vert (i + 1)) - 2 = 0 := by
    have hsz : ∑ i ∈ Finset.range (p.numVerts - 1),
        (ew k (p.vert i) (p.vert (i + 1)) - 2) = 0 := by
      rw [← excess_eq_sum_edgeWeight hk1 p]; exact h0
    exact (Finset.sum_eq_zero_iff.mp hsz)
  -- hence every boundary `1 … t` is a door
  have hdoors : ∀ s, 1 ≤ s → s ≤ t → IsDoor p s := by
    intro s hs1 hst
    have hkspos : 0 < k * s := Nat.mul_pos (by omega) (by omega)
    have hks : k * s - 1 + 1 = k * s := by omega
    have hksle : k * s ≤ p.numVerts - 1 := le_trans (Nat.mul_le_mul_left _ hst) hkt
    have hmem : k * s - 1 ∈ Finset.range (p.numVerts - 1) := by
      rw [Finset.mem_range]; omega
    have hd : k ∣ (k * s - 1 + 1) := by rw [hks]; exact ⟨s, rfl⟩
    have hin : k * s - 1 + 1 < p.numVerts := by rw [hks]; omega
    have hne1 : ew k (p.vert (k * s - 1)) (p.vert (k * s - 1 + 1)) ≠ 1 := by
      intro he1
      have hnd := (prp_periodicedges hk1 hp hin).mp he1
      rw [hks] at hnd
      exact hnd ⟨s, rfl⟩
    have hge1 := ew_ge_one hk1 (p.vert (k * s - 1)) (p.vert (k * s - 1 + 1))
    have hle2 := hterm (k * s - 1) hmem
    have hbw : ew k (p.vert (k * s - 1)) (p.vert (k * s - 1 + 1)) = bw p s := by
      simp only [bw]; rw [hks]
    show bw p s = 2
    rw [← hbw]; omega
  -- door-depth reaches `t`, capped at `k−2`
  have hcap := doorDepth_le_km2 hk hp t hktlt
  rw [doorDepth_eq_of_all_doors p t hdoors] at hcap
  -- `|p| ≤ k(t+1) ≤ k(k−1)`
  have hlt : p.numVerts - 1 < k * (t + 1) := by
    have hdm := Nat.div_add_mod (p.numVerts - 1) k
    rw [← htdef] at hdm
    have hmod : (p.numVerts - 1) % k < k := Nat.mod_lt _ (by omega)
    have hexp : k * (t + 1) = k * t + k := by ring
    omega
  calc p.numVerts ≤ k * (t + 1) := by omega
    _ ≤ k * (k - 1) := Nat.mul_le_mul_left _ (by omega)

/-! ## Targets 3–4: S2 (six-case) and the closure lemma — the meta-loop `τ₃`

`PROOF.md §2–§3`.  The level-3 refinement runs the *meta* ledger (`ProofsLedger.metaDepth`)
one layer above the door run: after a **full** weight-2 run (a complete marked 2-loop) the
distinguished weight-3 successor is the complete-α `τ₃`, which chains 2-loops into a
meta-chain of period `k−2` (`metaDepth ≤ k−2`, `ProofsRunExtract.metaDepth_le`).

Calibration (verified `sublemmas.py`, k=5,6,7): the 6 weight-3 successors after a full run
split `3` revisits / `2` early-collisions / `1` full fresh run; the three new-class landings
have run-lengths `[k−2, k−2, k−1]`.  At k=5 this reads `[3, 3, 4]` (`full = k−1 = 4`).
The distinguished `[k−1]` continuation is exactly the complete-α `τ₃`; the two `[k−2]`
collisions are the σ²/incomplete-α landings ruled out of the meta-chain.

The **closure lemma** (`PROOF.md §3`, verified `closure.py` k≤9: after the unique tight
`N = (k−1)(k−2)`-block chart every light successor of the final exit revisits, so the minimum
continuation weight is `4`) is the *rigidity* consequence of the meta-period: a pure
`τ₂/τ₃` chart (no meta-heavy boundary) exhausts the meta-cycle and cannot lengthen without a
weight-`≥4` (meta-heavy) jump.  We deliver its structural engine here — the meta-period cap
and the **meta-chart block bound** (a pure `τ₂/τ₃` chart has bounded length) — the exact
analogue, one layer up, of the door-period `excess_zero_block_bound` above. -/

/-- **S2 meta-period (`τ₃` has period `k−2`).**  Along an exitless path the meta-chain of
`τ₃`-joined complete 2-loops has depth at most `k−2`: the chart exhausts `τ₃`'s cycle after
`k−2` runs.  (Re-export of `ProofsRunExtract.metaDepth_le`.) -/
theorem s2_meta_period (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) : metaDepth p t ≤ k - 2 :=
  metaDepth_le hk hp t hN

/-- **Closure engine — meta-chart block bound.**  A *pure* `τ₂/τ₃` chart (an exitless path
with **no meta-heavy boundary**, i.e. every positive jump is a complete-α `τ₃`) spans at most
`k(k−2)` blocks, so `|p| ≤ k·(k(k−2)+1)`.  Mechanism (the level-3 analogue of
`excess_zero_block_bound`): with no meta-heavy the run-start is pinned at `0`
(`runStart_const`), so the run-length identity `metaDepth·(k−1) + doorDepth = t`
(`runLen_eq`) together with the two caps `metaDepth ≤ k−2` and `doorDepth ≤ k−2` forces
`t ≤ (k−2)(k−1) + (k−2) = k(k−2)`.  This is the finiteness underlying the closure lemma: the
`τ₃` cycle is exhausted, so continuing the chart requires a meta-heavy (weight-`≥4`) jump. -/
theorem meta_chart_block_bound (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hno : ∀ s, 1 ≤ s → s ≤ (p.numVerts - 1) / k → ¬ IsMetaHeavy p s) :
    p.numVerts ≤ k * (k * (k - 2) + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ p.numVerts := p.numVerts_pos
  set t := (p.numVerts - 1) / k with htdef
  have hkt : k * t ≤ p.numVerts - 1 := by
    rw [htdef, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hktlt : k * t < p.numVerts := by omega
  -- no meta-heavy ⇒ run-start pinned at 0
  have hrs0 : runStart p t = 0 := by
    have hc := runStart_const p 0 t (fun s hs1 hs2 => hno s (by omega) (by omega))
    rwa [Nat.zero_add, runStart_zero] at hc
  have hmd := metaDepth_le hk hp t (by omega)
  have hdd := doorDepth_le_km2 hk hp t hktlt
  have hlen := runLen_eq hk p t
  rw [hrs0] at hlen
  -- the arithmetic collapse: t ≤ k(k−2)
  have hkk : (k - 2) * (k - 1) + (k - 2) = k * (k - 2) := by
    have h : k - 1 + 1 = k := by omega
    calc (k - 2) * (k - 1) + (k - 2) = (k - 2) * ((k - 1) + 1) := by ring
      _ = (k - 2) * k := by rw [h]
      _ = k * (k - 2) := by ring
  have h1 : metaDepth p t * (k - 1) ≤ (k - 2) * (k - 1) := Nat.mul_le_mul_right _ hmd
  have htle : t ≤ k * (k - 2) := by omega
  -- |p| ≤ k(t+1) ≤ k(k(k−2)+1)
  have hlt : p.numVerts - 1 < k * (t + 1) := by
    have hdm := Nat.div_add_mod (p.numVerts - 1) k
    rw [← htdef] at hdm
    have hmod : (p.numVerts - 1) % k < k := Nat.mod_lt _ (by omega)
    have hexp : k * (t + 1) = k * t + k := by ring
    omega
  calc p.numVerts ≤ k * (t + 1) := by omega
    _ ≤ k * (k * (k - 2) + 1) := Nat.mul_le_mul_left _ (by omega)

end ProofsChart

/-! ## Exported interface (`Hunter.Proved`) — what the induction consumes

Clean re-exports of the four structural targets, in `Hunter.Proved`, for the sibling
`ProofsInduction.lean` (the `F_E ≤ G(E)` induction of `PROOF.md §4`). -/

namespace Proved

open ProofsChart

/-- **Target 1 (keystone).**  A block-aligned suffix of an exitless path is exitless. -/
theorem suffix_exitless {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {B : ℕ}
    (hBdvd : k ∣ B) (hBlt : B < p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.drop B ∧ q.Exitless :=
  ProofsChart.suffix_exitless hk hp hBdvd hBlt

/-- **Target 1 (cost).**  Excess splits at a block-aligned cut:
`excess p = (Σ_{j<B} perEdgeExc p j) + excess(suffix)`. -/
theorem excess_split {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {B : ℕ}
    (hBdvd : k ∣ B) (hBlt : B < p.numVerts) {q : HPath k} (hq : q.verts = p.verts.drop B) :
    ProofsRecursion.excess p =
      (∑ j ∈ Finset.range B, ProofsChart.perEdgeExc p j) + ProofsRecursion.excess q :=
  ProofsChart.excess_split hk hp hBdvd hBlt hq

/-- **Target 2 (S1, period).**  A weight-0 run spans at most `k−1` blocks: an exitless path
with no `≥3`-weight excess has `|p| ≤ k(k−1)`  (`F_0 = k−1`). -/
theorem excess_zero_block_bound {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (h0 : ProofsRecursion.excess p = 0) : p.numVerts ≤ k * (k - 1) :=
  ProofsChart.excess_zero_block_bound hk hp h0

/-- **Target 3 (S2, meta-period).**  The `τ₃`-meta-chain has depth `≤ k−2`. -/
theorem s2_meta_period {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) : ProofsLedger.metaDepth p t ≤ k - 2 :=
  ProofsChart.s2_meta_period hk hp t hN

/-- **Target 4 (closure engine).**  A pure `τ₂/τ₃` chart (no meta-heavy boundary) has
bounded length `|p| ≤ k(k(k−2)+1)`; continuing it requires a weight-`≥4` jump. -/
theorem meta_chart_block_bound {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hno : ∀ s, 1 ≤ s → s ≤ (p.numVerts - 1) / k → ¬ ProofsLedger.IsMetaHeavy p s) :
    p.numVerts ≤ k * (k * (k - 2) + 1) :=
  ProofsChart.meta_chart_block_bound hk hp hno

end Proved

end Hunter

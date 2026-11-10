/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLedger

/-!
# Theorem 2 — the PATH→RUN EXTRACTION (Wave 2 of the no-lift ledger route)

Wave 1 (`ProofsLedger`) promoted the run-structure inside `alpha_run_bound` to named total
functions of an exitless path (`doorDepth`, `metaDepth`, `runStart`, …) with their step
equations, and shipped the **run-conditioned** bound `metaDepth_le_of_run` — but left the
*extraction* open: manufacturing `alpha_run_bound`'s positional `hdoor`/`halpha` inputs from an
arbitrary path.  That is the "purely positional" piece this file closes.

## The engine: one positional invariant

The whole extraction is driven by a single equation, provable by structural induction on `t`
directly from the Wave-1 step equations (**no** exitlessness, **no** confinement):

> `ledger_position` :  `t = runStart p t + metaDepth p t · (k−1) + doorDepth p t`.

Reading it: since the last meta-heavy reset (`runStart`), the path has laid `metaDepth p t`
*complete* 2-loops (each `k−1` blocks, closed by an α) followed by a partial loop of
`doorDepth p t` doors.  The three boundary transitions each keep the equation:

| into `t+1`        | `runStart`      | `metaDepth`   | `doorDepth`   | equation stays |
|-------------------|-----------------|---------------|---------------|----------------|
| door              | carry           | carry         | `+1`          | `d ↦ d+1`      |
| α, `IsComplete t` | carry           | `+1`          | `0`           | `d=k−2 ↦ +(k−1)` |
| meta-heavy        | `t+1`           | `0`           | `0`           | reset          |

## Wave-2 deliverables (all sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})

* **`runExtract`** — the extraction: from any `p`, at any block `t`, the anchor `t₀ = runStart p t`
  and count `m = metaDepth p t` come with the full block-index data in exactly
  `alpha_run_bound`/`metaDepth_le_of_run`'s interface form (`hdoor` on the `m` completed loops'
  interiors, `halpha` on their α-terminators), plus the partial current loop's doors.
* **`metaDepth_le`** — UNCONDITIONAL `metaDepth p t ≤ k − 2` for every exitless `p` and every
  in-range `t` (compose `runExtract` with `metaDepth_le_of_run`/`alpha_run_bound`).
  **This closes the construction flagged open since ProofsMeta4/6 — a genuinely new theorem.**
* **`run_confined`** — α-run-wide confinement: every block-start of the whole chained run (across
  the α boundaries, not just one 2-loop) lies in the run's fixed level-3 marked loop
  (`meta_hinv_mem_Vset3` / `Vset3_of_metaWord_rotate_iter` threaded along `runExtract`'s indices).
* **`run_payment`** — along the extracted run each α boundary pays exactly `1` (`runs_pay`
  composed with `runExtract`); packaged as the per-run ledger fact Wave 4's invariant consumes.

Namespace `Hunter.ProofsRunExtract`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsRunExtract

open ProofsMeta ProofsMeta2 ProofsMeta3 ProofsMeta4 ProofsExcess ProofsConfinement
open ProofsSynthesis ProofsLedger HPath

variable {k : ℕ}

/-! ## §1. The positional invariant and the full extraction

`runExtract` bundles four facts about the run ending at block `t`, all proved together by one
structural induction on `t`.  Writing `t₀ = runStart p t`, `m = metaDepth p t`,
`d = doorDepth p t`:

* **(A)** `t = t₀ + m·(k−1) + d`  (the positional invariant);
* **(B)** the `k−2` interior boundaries of each *completed* 2-loop `j < m` are doors:
  `IsDoor p (t₀ + j·(k−1) + r)` for `1 ≤ r ≤ k−2`;
* **(C)** each completed 2-loop `1 ≤ c ≤ m` is closed by an α: `IsAlpha p (t₀ + c·(k−1))`;
* **(D)** the *current* partial loop's `d` doors: `IsDoor p (t₀ + m·(k−1) + r)` for `1 ≤ r ≤ d`.

(B) restricted to `j < m` and (C) restricted to `c < m` are *exactly* `metaDepth_le_of_run`'s
`hdoor`/`halpha`; (D) is the induction's carrier — when the current loop's α fires, (D) becomes
(B) for `j = m`. -/

/-- **PATH→RUN EXTRACTION.**  From an arbitrary path `p` and any block `t`, the maximal α-run
data anchored at `t₀ = runStart p t` with `m = metaDepth p t` complete 2-loops, in exactly
`alpha_run_bound`'s interface form.  Purely positional: needs only `2 ≤ k` (for `(k−2)+1 = k−1`)
and the Wave-1 step equations — no exitlessness, no confinement. -/
theorem runExtract (hk : 2 ≤ k) (p : HPath k) :
    ∀ t,
      t = runStart p t + metaDepth p t * (k - 1) + doorDepth p t ∧
      (∀ j r, j < metaDepth p t → 1 ≤ r → r ≤ k - 2 →
          IsDoor p (runStart p t + j * (k - 1) + r)) ∧
      (∀ c, 1 ≤ c → c ≤ metaDepth p t → IsAlpha p (runStart p t + c * (k - 1))) ∧
      (∀ r, 1 ≤ r → r ≤ doorDepth p t →
          IsDoor p (runStart p t + metaDepth p t * (k - 1) + r)) := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [runStart_zero, metaDepth_zero, doorDepth_zero]; simp
    · intro j r hj hr1 hr2; rw [metaDepth_zero] at hj; omega
    · intro c hc1 hc2; rw [metaDepth_zero] at hc2; omega
    · intro r hr1 hr2; rw [doorDepth_zero] at hr2; omega
  | succ t ih =>
    obtain ⟨ihA, ihB, ihC, ihD⟩ := ih
    by_cases hdoor : IsDoor p (t + 1)
    · -- DOOR: runStart/metaDepth carry, doorDepth += 1
      have hrs := runStart_not_metaHeavy (p := p) (t := t) (fun hmh => hmh.1 hdoor)
      have hmd := metaDepth_door hdoor
      have hdd := doorDepth_door hdoor
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hrs, hmd, hdd]; omega
      · rw [hrs, hmd]; exact ihB
      · rw [hrs, hmd]; exact ihC
      · rw [hrs, hmd, hdd]
        intro r hr1 hr2
        by_cases hrle : r ≤ doorDepth p t
        · exact ihD r hr1 hrle
        · have hre : r = doorDepth p t + 1 := by omega
          have hpos : runStart p t + metaDepth p t * (k - 1) + r = t + 1 := by omega
          rw [hpos]; exact hdoor
    · by_cases hac : IsAlpha p (t + 1) ∧ IsComplete p t
      · -- α-COMPLETE: runStart carries, metaDepth += 1, doorDepth → 0
        obtain ⟨ha, hc⟩ := hac
        have hdeq : doorDepth p t = k - 2 := hc
        have hnd : ¬ IsDoor p (t + 1) := by
          rw [IsDoor]; have := ha.1; omega
        have hrs := runStart_not_metaHeavy (p := p) (t := t) (fun hmh => hmh.2 ⟨ha, hc⟩)
        have hmd := metaDepth_alpha_complete ha hc
        have hdd := doorDepth_not_door hnd
        have hexp : (metaDepth p t + 1) * (k - 1) = metaDepth p t * (k - 1) + (k - 1) :=
          Nat.succ_mul _ _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrs, hmd, hdd, hexp]; omega
        · rw [hrs, hmd]
          intro j r hj hr1 hr2
          by_cases hjm : j < metaDepth p t
          · exact ihB j r hjm hr1 hr2
          · have hje : j = metaDepth p t := by omega
            subst hje
            exact ihD r hr1 (by omega)
        · rw [hrs, hmd]
          intro c hc1 hc2
          by_cases hcm : c ≤ metaDepth p t
          · exact ihC c hc1 hcm
          · have hce : c = metaDepth p t + 1 := by omega
            subst hce
            have hpos : runStart p t + (metaDepth p t + 1) * (k - 1) = t + 1 := by
              rw [hexp]; omega
            rw [hpos]; exact ha
        · rw [hrs, hmd, hdd]
          intro r hr1 hr2; omega
      · -- META-HEAVY: runStart → t+1, metaDepth → 0, doorDepth → 0
        have hmh : IsMetaHeavy p (t + 1) := ⟨hdoor, hac⟩
        have hrs := runStart_metaHeavy hmh
        have hmd := metaDepth_metaHeavy hmh
        have hdd := doorDepth_not_door hdoor
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrs, hmd, hdd]; omega
        · rw [hrs, hmd]; intro j r hj hr1 hr2; omega
        · rw [hrs, hmd]; intro c hc1 hc2; omega
        · rw [hrs, hmd, hdd]; intro r hr1 hr2; omega

/-! ## §2. The headline: unconditional `metaDepth_le`

Compose `runExtract` (positional data) with `metaDepth_le_of_run` (the ledger wrapper over the
proved `alpha_run_bound`).  `runExtract`'s (B)/(C) discharge `hdoor`/`halpha`; (A) supplies the
position bound `k·(t₀ + m·(k−1)) ≤ k·t ≤ numVerts`.  Result: `metaDepth ≤ k − 2` for *every*
exitless path and in-range block — the construction flagged open since ProofsMeta4/6. -/

/-- **UNCONDITIONAL `metaDepth ≤ k − 2`.**  For every exitless path `p` and every block `t` with
`k·t ≤ p.numVerts`, the meta-depth (complete 2-loops chained by α since the last meta-heavy) is
at most `k − 2`.  No manufactured run hypothesis: the run is extracted from the path itself.
**This is the theorem the repo previously only flagged as open.** -/
theorem metaDepth_le (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) : metaDepth p t ≤ k - 2 := by
  obtain ⟨hA, hB, hC, _⟩ := runExtract (by omega) p t
  refine metaDepth_le_of_run hk hp (runStart p t) (metaDepth p t) ?_ hB ?_
  · have hle : runStart p t + metaDepth p t * (k - 1) ≤ t := by omega
    calc k * (runStart p t + metaDepth p t * (k - 1))
        ≤ k * t := Nat.mul_le_mul (le_refl k) hle
      _ ≤ p.numVerts := hN
  · intro c hc1 hc2; exact hC c hc1 (le_of_lt hc2)

/-! ## §3. Per-run payment — the Wave-4 ledger seed

`run_payment` reads the α payments straight off `runExtract`'s (C): each of the `m`
run-internal α boundaries is weight-3 (`bw = 3`), banking one unit of excess (`bw − 2 = 1`).
`metaHeavy_pays_and_resets` supplies the run's *terminator*: the first non-door-non-complete-α
boundary after the run is meta-heavy, hence (by `boundary_classify_ledger`, ruling out weight-2)
weight `≥ 3` — it pays `≥ 1` and resets `metaDepth` to `0`.  Together with the count bound
`metaDepth ≤ k − 2` this is the per-run fact Wave 4's `owed`/σ invariant consumes: a maximal run
banks `m` unit payments and cannot extend past `k − 2` complete 2-loops without a fresh paying
event. -/

/-- **α payments along the extracted run.**  Every run-internal α boundary is weight-3, so it
contributes exactly one unit of excess (`bw − 2 = 1`); and the run has `≤ k − 2` complete 2-loops. -/
theorem run_payment (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t ≤ p.numVerts) :
    metaDepth p t ≤ k - 2 ∧
    ∀ c, 1 ≤ c → c ≤ metaDepth p t → bw p (runStart p t + c * (k - 1)) = 3 := by
  obtain ⟨_, _, hC, _⟩ := runExtract (by omega) p t
  exact ⟨metaDepth_le hk hp t hN, fun c hc1 hc2 => (hC c hc1 hc2).1⟩

/-- **A meta-heavy boundary is weight `≥ 3`.**  Ruling out weight-2 (`¬IsDoor`) via
`boundary_classify_ledger` leaves α / σ² / marker-move (weight 3) or heavy (weight `≥ 4`). -/
theorem metaHeavy_bw_ge3 (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {s : ℕ}
    (hs : 1 ≤ s) (hN : k * s < p.numVerts) (h : IsMetaHeavy p s) : 3 ≤ bw p s := by
  rcases boundary_classify_ledger hk hp hs hN with hd | ha | hσ | hmm | hh
  · exact absurd hd h.1
  · exact ha.1.ge
  · exact hσ.1.ge
  · exact hmm.1.ge
  · rw [IsHeavy] at hh; omega

/-- **The run terminator pays and resets.**  The meta-heavy boundary ending a maximal α-run is
weight `≥ 3` (pays `≥ 1`) and resets the meta-chain (`metaDepth = 0`). -/
theorem metaHeavy_pays_and_resets (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {s : ℕ}
    (hs : 1 ≤ s) (hN : k * s < p.numVerts) (h : IsMetaHeavy p s) :
    3 ≤ bw p s ∧ metaDepth p s = 0 := by
  refine ⟨metaHeavy_bw_ge3 hk hp hs hN h, ?_⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  exact metaDepth_metaHeavy h

/-! ## §4. α-run-wide confinement — the whole chained run in one `Vset3`

Wave 1's `ledger_confined` confines a *single* 2-loop.  Here we thread the meta-word across the
α boundaries (`metaWord_alpha_block` + `genLoop_door_eq_rho_of_len`'s completeness identity,
exactly `alpha_run_bound`'s internal derivation but concluding confinement instead of
pigeonhole).  `run_loopStart_confined` carries the level-`(k−1)` `genLoop` of each completed
2-loop's meta-word constant along the run (`= genLoop` of the run's first block); then
`run_confined` extends it to *every* block-start via `door_run_metaWord` (intra-loop rotations)
+ `Vset3_of_metaWord_rotate_iter`. -/

/-- **Meta-chain `genLoop` invariance.**  Along the extracted α-run, the block-marker of each
completed 2-loop's start equals the run-marker `α₁`, and the level-`(k−1)` `genLoop` of its
meta-word is constant (`= genLoop` of the run's first block `runStart`).  Bounded meta-`hinv`. -/
theorem run_loopStart_confined (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t < p.numVerts) :
    ∀ j, j ≤ metaDepth p t →
      (p.vert (k * (runStart p t + j * (k - 1))) : List ℕ).getLastD 0
          = (p.vert (k * runStart p t) : List ℕ).getLastD 0 ∧
      genLoop ((p.vert (k * (runStart p t + j * (k - 1))) : List ℕ).erase
          ((p.vert (k * runStart p t) : List ℕ).getLastD 0))
        = genLoop ((p.vert (k * runStart p t) : List ℕ).erase
          ((p.vert (k * runStart p t) : List ℕ).getLastD 0)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hA, hB, hC, _⟩ := runExtract hk2 p t
  set t₀ := runStart p t with ht0
  set m := metaDepth p t with hm
  set α₁ := (p.vert (k * t₀) : List ℕ).getLastD 0 with hα1
  have hcle : ∀ c, c ≤ m → t₀ + c * (k - 1) ≤ t := by
    intro c hc
    have : c * (k - 1) ≤ m * (k - 1) := Nat.mul_le_mul hc (le_refl _)
    omega
  intro j
  induction j with
  | zero =>
    intro _
    rw [show t₀ + 0 * (k - 1) = t₀ from by ring]
    exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hmarkj, hglj⟩ := ih (by omega)
    have haj1 : t₀ + (j + 1) * (k - 1) = (t₀ + j * (k - 1)) + (k - 1) := by
      rw [Nat.succ_mul]; ring
    have haj1m1 : t₀ + (j + 1) * (k - 1) - 1 = t₀ + j * (k - 1) + (k - 2) := by
      rw [haj1]; omega
    -- interior doors of loop `j`
    have hdoorj : ∀ r, 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + j * (k - 1) + r) - 1))
          (p.vert (k * (t₀ + j * (k - 1) + r))) = 2 :=
      fun r hr1 hr2 => hB j r (by omega) hr1 hr2
    have hNj : k * (t₀ + j * (k - 1) + (k - 2)) < p.numVerts := by
      have hle : t₀ + j * (k - 1) + (k - 2) ≤ t := by
        have h1 : (j + 1) * (k - 1) ≤ m * (k - 1) := Nat.mul_le_mul (by omega) (le_refl _)
        have h2 : (j + 1) * (k - 1) = j * (k - 1) + (k - 1) := Nat.succ_mul j (k - 1)
        omega
      exact lt_of_le_of_lt (Nat.mul_le_mul (le_refl k) hle) hN
    have hrun := door_run_metaWord hk2 hp (t₀ + j * (k - 1)) (k - 2) hNj hdoorj
    obtain ⟨hmarkr, hmetar⟩ := hrun (k - 2) (le_refl _)
    have hAlpha := hC (j + 1) (by omega) hj
    have hmarkAlpha : (p.vert (k * (t₀ + (j + 1) * (k - 1))) : List ℕ).getLastD 0
        = (rho (p.vert (k * (t₀ + (j + 1) * (k - 1)) - 1) : List ℕ)).getLastD 0 := hAlpha.2.1
    have hNj1 : k * (t₀ + (j + 1) * (k - 1)) < p.numVerts :=
      lt_of_le_of_lt (Nat.mul_le_mul (le_refl k) (hcle (j + 1) hj)) hN
    have ht1 : 1 ≤ t₀ + (j + 1) * (k - 1) := by
      have : 1 * 1 ≤ (j + 1) * (k - 1) := Nat.mul_le_mul (by omega) (by omega); omega
    have hmkprev : (p.vert (k * (t₀ + (j + 1) * (k - 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
      rw [haj1m1, hmarkr]; exact hmarkj
    -- meta-word length `k-1` and completeness `rotate (k-1) = id`
    have hlenj : ((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).length = k - 1 := by
      rw [← hmarkj, erase_getLastD (p.vert (k * (t₀ + j * (k - 1)))).2.nodup,
          List.length_dropLast, (p.vert (k * (t₀ + j * (k - 1)))).2.length]
    -- the α meta-step
    have hstep : (p.vert (k * (t₀ + (j + 1) * (k - 1))) : List ℕ).erase α₁
        = door (((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate (k - 2)) := by
      have hab := metaWord_alpha_block hk hp ht1 hNj1 hAlpha.1 hmarkAlpha hAlpha.2.2 hmkprev
      rw [show (p.vert (k * (t₀ + j * (k - 1))) : List ℕ).getLastD 0 = α₁ from hmarkj] at hmetar
      rw [hab, haj1m1, hmetar]
    have hrot1 :
        (((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate (k - 2)).rotate 1
          = (p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁ := by
      rw [List.rotate_rotate]
      have hexp : (k - 2) + 1 = ((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).length := by
        rw [hlenj]; omega
      rw [hexp, List.rotate_length]
    have h2le :
        2 ≤ (((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate (k - 2)).length := by
      rw [List.length_rotate, hlenj]; omega
    refine ⟨marker_alpha_step hk1 hp ht1 (le_of_lt hNj1) hmarkAlpha hmkprev, ?_⟩
    rw [hstep, genLoop_door_eq_rho_of_len h2le]
    show genLoop ((((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate (k - 2)).rotate 1)
      = _
    rw [hrot1]; exact hglj

/-- **α-run-wide confinement.**  Every block-start of the whole chained α-run at `t` — the
interiors of the `m = metaDepth p t` completed 2-loops *and* the current partial loop's
`doorDepth p t` doors, across the α boundaries — lies in the single level-3 marked loop read off
the run's anchor `runStart p t`.  Extends `ledger_confined` from one 2-loop to the entire run. -/
theorem run_confined (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t < p.numVerts) :
    ∀ j r,
      (j < metaDepth p t ∧ 1 ≤ r ∧ r ≤ k - 2) ∨ (j = metaDepth p t ∧ r ≤ doorDepth p t) →
      p.vert (k * (runStart p t + j * (k - 1) + r))
        ∈ Vset3 k ((p.vert (k * runStart p t) : List ℕ).getLastD 0)
            (((p.vert (k * runStart p t) : List ℕ).erase
                ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).getLastD 0)
            (rotClass (((p.vert (k * runStart p t) : List ℕ).erase
                ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).dropLast)) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hA, hB, _, hD⟩ := runExtract hk2 p t
  -- every completed / current loop start is confined (from the genLoop invariance)
  have hmem : ∀ j, j ≤ metaDepth p t →
      p.vert (k * (runStart p t + j * (k - 1)))
        ∈ Vset3 k ((p.vert (k * runStart p t) : List ℕ).getLastD 0)
            (((p.vert (k * runStart p t) : List ℕ).erase
                ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).getLastD 0)
            (rotClass (((p.vert (k * runStart p t) : List ℕ).erase
                ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).dropLast)) ∧
      (p.vert (k * (runStart p t + j * (k - 1))) : List ℕ).getLastD 0
        = (p.vert (k * runStart p t) : List ℕ).getLastD 0 := by
    intro j hj
    obtain ⟨hmk, hgl⟩ := run_loopStart_confined hk hp t hN j hj
    have hpair : genLoop ((p.vert (k * (runStart p t + j * (k - 1))) : List ℕ).erase
            ((p.vert (k * runStart p t) : List ℕ).getLastD 0))
        = (((p.vert (k * runStart p t) : List ℕ).erase
              ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).getLastD 0,
           rotClass (((p.vert (k * runStart p t) : List ℕ).erase
              ((p.vert (k * runStart p t) : List ℕ).getLastD 0)).dropLast)) := hgl
    exact ⟨mem_Vset3_of_genLoop_metaWord hpair, hmk⟩
  -- each block-start is a rotation of its loop's start, hence in the same `Vset3`
  intro j r hjr
  rcases hjr with ⟨hjm, hr1, hr2⟩ | ⟨hjm, hrd⟩
  · obtain ⟨hmemj, hmarkj⟩ := hmem j (le_of_lt hjm)
    have hdoorj : ∀ s, 1 ≤ s → s ≤ k - 2 →
        ew k (p.vert (k * (runStart p t + j * (k - 1) + s) - 1))
          (p.vert (k * (runStart p t + j * (k - 1) + s))) = 2 :=
      fun s hs1 hs2 => hB j s hjm hs1 hs2
    have hNj : k * (runStart p t + j * (k - 1) + (k - 2)) < p.numVerts := by
      have hle : runStart p t + j * (k - 1) + (k - 2) ≤ t := by
        have h1 : (j + 1) * (k - 1) ≤ metaDepth p t * (k - 1) := Nat.mul_le_mul (by omega) (le_refl _)
        have h2 : (j + 1) * (k - 1) = j * (k - 1) + (k - 1) := Nat.succ_mul j (k - 1)
        omega
      exact lt_of_le_of_lt (Nat.mul_le_mul (le_refl k) hle) hN
    obtain ⟨_, hrotr⟩ :=
      door_run_metaWord hk2 hp (runStart p t + j * (k - 1)) (k - 2) hNj hdoorj r (by omega)
    rw [hmarkj] at hrotr
    exact Vset3_of_metaWord_rotate_iter hmemj hrotr
  · subst hjm
    obtain ⟨hmemm, hmarkm⟩ := hmem (metaDepth p t) (le_refl _)
    have hdoorm : ∀ s, 1 ≤ s → s ≤ doorDepth p t →
        ew k (p.vert (k * (runStart p t + metaDepth p t * (k - 1) + s) - 1))
          (p.vert (k * (runStart p t + metaDepth p t * (k - 1) + s))) = 2 :=
      fun s hs1 hs2 => hD s hs1 hs2
    have hNm : k * (runStart p t + metaDepth p t * (k - 1) + doorDepth p t) < p.numVerts := by
      rw [← hA]; exact hN
    obtain ⟨_, hrotr⟩ :=
      door_run_metaWord hk2 hp (runStart p t + metaDepth p t * (k - 1)) (doorDepth p t) hNm hdoorm
        r hrd
    rw [hmarkm] at hrotr
    exact Vset3_of_metaWord_rotate_iter hmemm hrotr

end ProofsRunExtract

end Hunter

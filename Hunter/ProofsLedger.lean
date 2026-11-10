/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsSynthesis

/-!
# Theorem 2 — the LEDGER layer (Wave 1 of the no-lift ledger route)

This file promotes the run-structure that lives *inside* `ProofsMeta4.alpha_run_bound` /
`ProofsMeta2.meta_confinement` to **named total functions of an exitless path** `p : HPath k`,
so the excess telescope of later waves can quantify over it.  No new type and no lift: the meta
walk is bookkeeping over indexed families of level-`k` vertices, exactly the style already used
by the proved confinement machinery.

Block `t` occupies path vertices `k·t … k·t + (k−1)`; the **boundary into block `t`** (`t ≥ 1`)
is the edge `p.vert (k·t − 1) → p.vert (k·t)`.  Everything below is a function/predicate of `p`
and the block index `t`.

## Wave-1 deliverables (all sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})

* **the per-boundary classification** as total predicates `IsDoor / IsAlpha / IsSigmaSq /
  IsMarkerMove / IsHeavy` (weight `2 / 3α / 3σ² / 3-move / ≥4`), with coverage
  (`boundary_classify_ledger`) and the bw/marker disjointness lemmas — from `boundary_classify`;
* **the state functions** `doorDepth`, `IsComplete`, `loopStart`, `runStart`, `metaDepth`,
  `blockMarker`, `α₁`, `curVset3`, each structurally recursive or positionally defined, together
  with their **step equations** (`doorDepth_door`, `metaDepth_alpha_complete`, …) — the wave's
  core deliverable that every downstream lemma pattern-matches on;
* **the invariants** `ledger_marker_const` (marker constant along a run, from
  `marker_door_step`/`marker_alpha_step`), `ledger_confined` (the current 2-loop's block-starts
  lie in a fixed `Vset3`, from the door meta-word rotation), `sigmaSq_incomplete_only` (a σ²
  boundary forces the current loop incomplete — the contrapositive of `lemmaA_sigmaSq_excluded`),
  and the `metaDepth_reset` family (any non-α / incomplete-loop ejection resets `metaDepth`).

`metaDepth_le` (the unconditional `metaDepth ≤ k−2`) needs the path→run *extraction* that
manufactures `alpha_run_bound`'s `hdoor`/`halpha` positionally; the extraction is Wave 2 (L5/L6),
so here we ship only the **run-conditioned** bound `metaDepth_le_of_run` (a thin wrapper feeding
the ledger predicates into `alpha_run_bound`) and log the manufacture for Wave 2.

Namespace `Hunter.ProofsLedger`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsLedger

open ProofsMeta ProofsMeta2 ProofsMeta3 ProofsMeta4 ProofsMeta8 ProofsExcess ProofsConfinement
open ProofsSynthesis HPath

variable {k : ℕ}

/-! ## §1. The per-boundary weight and the five boundary kinds -/

/-- Incoming boundary weight of block `t` (`t ≥ 1`): the edge weight `k·t−1 → k·t`. -/
noncomputable def bw (p : HPath k) (t : ℕ) : ℕ := ew k (p.vert (k * t - 1)) (p.vert (k * t))

/-- The boundary into block `t` is **marker-preserving**: the block-start keeps as its last
symbol the marker `marker p (k·t−1) = (rho (p.vert (k·t−1))).getLastD 0`.  (Same predicate that
`boundary_classify`'s weight-3 case splits on.) -/
def markPres (p : HPath k) (t : ℕ) : Prop :=
  (p.vert (k * t) : List ℕ).getLastD 0 = marker p (k * t - 1)

/-- **Door** boundary — weight 2, contributes `0` to the excess. -/
def IsDoor (p : HPath k) (t : ℕ) : Prop := bw p t = 2

/-- **α** boundary — weight 3, marker-preserving, landing on `alphaWord`.  Continues a
marker-fixed run and (when it leaves a *complete* 2-loop) links it into the meta-chain. -/
def IsAlpha (p : HPath k) (t : ℕ) : Prop :=
  bw p t = 3 ∧ markPres p t ∧
    (p.vert (k * t) : List ℕ) = alphaWord (p.vert (k * t - 1) : List ℕ)

/-- **σ²** boundary — weight 3, marker-preserving, landing on `sigmaSqWord`.  The `alphaWord`
sibling; by `sigmaSq_incomplete_only` it can only leave an *incomplete* 2-loop. -/
def IsSigmaSq (p : HPath k) (t : ℕ) : Prop :=
  bw p t = 3 ∧ markPres p t ∧
    (p.vert (k * t) : List ℕ) = sigmaSqWord (p.vert (k * t - 1) : List ℕ)

/-- **Marker-move** boundary — weight 3, marker-moving; opens a new meta-window (a reset). -/
def IsMarkerMove (p : HPath k) (t : ℕ) : Prop := bw p t = 3 ∧ ¬ markPres p t

/-- **Heavy** boundary — weight `≥ 4`. -/
def IsHeavy (p : HPath k) (t : ℕ) : Prop := 4 ≤ bw p t

/-! ## §2. The door-run depth and the completeness flag -/

/-- Length of the maximal door-run ending at block `t` (= the current 2-loop's door-depth,
`0 … k−2`).  Structurally recursive on `t`: a door extends the run, anything else restarts it. -/
noncomputable def doorDepth (p : HPath k) : ℕ → ℕ
  | 0     => 0
  | t + 1 => if IsDoor p (t + 1) then doorDepth p t + 1 else 0

/-- The current 2-loop is **complete** at block `t` iff its door-run has filled the marked 2-loop
(`k − 2` interior doors, i.e. `k − 1` blocks). -/
def IsComplete (p : HPath k) (t : ℕ) : Prop := doorDepth p t = k - 2

/-- First block index of the current 2-loop (door-run): `t − doorDepth p t`. -/
noncomputable def loopStart (p : HPath k) (t : ℕ) : ℕ := t - doorDepth p t

/-! ## §3. The meta-heavy predicate and the meta-depth -/

/-- **Meta-heavy** boundary into block `t` (`t ≥ 1`): NOT a door, and NOT an α that leaves a
complete 2-loop.  Equivalently — via the coverage lemma — a weight-`≥4` heavy, a marker-moving
weight-3 reset, a σ², or an α leaving an *incomplete* loop.  Every meta-heavy resets the
meta-chain. -/
def IsMetaHeavy (p : HPath k) (t : ℕ) : Prop :=
  ¬ IsDoor p t ∧ ¬ (IsAlpha p t ∧ IsComplete p (t - 1))

/-- Meta-depth = number of complete 2-loops chained by α since the last meta-heavy (`0 … k−2`).
Structurally recursive: an α leaving a complete loop increments, a meta-heavy resets to `0`, an
interior door carries. -/
noncomputable def metaDepth (p : HPath k) : ℕ → ℕ
  | 0     => 0
  | t + 1 =>
      if IsAlpha p (t + 1) ∧ IsComplete p t then metaDepth p t + 1
      else if IsMetaHeavy p (t + 1) then 0
      else metaDepth p t

/-- First block index of the current **α-run** (meta-chain): reset to `t+1` at every meta-heavy,
carried otherwise.  The run-marker `α₁` and confining `Vset3` are read off this block. -/
noncomputable def runStart (p : HPath k) : ℕ → ℕ
  | 0     => 0
  | t + 1 => if IsMetaHeavy p (t + 1) then t + 1 else runStart p t

/-- The block-start marker at block `t`: the last symbol of `p.vert (k·t)`.  This is the symbol
that `marker_door_step` / `marker_alpha_step` hold fixed along a run. -/
noncomputable def blockMarker (p : HPath k) (t : ℕ) : ℕ := (p.vert (k * t) : List ℕ).getLastD 0

/-- The fixed run-marker `α₁` of the current α-run: the block-marker read off `runStart`. -/
noncomputable def α₁ (p : HPath k) (t : ℕ) : ℕ := blockMarker p (runStart p t)

/-- The level-3 marked loop confining the current 2-loop: `Vset3` read off the 2-loop start
`loopStart p t` (its block-marker `α₁`, second marker `α₂`, doubly-erased class `K`). -/
noncomputable def curVset3 (p : HPath k) (t : ℕ) : Finset (Vtx k) :=
  Vset3 k (blockMarker p (loopStart p t))
    ((((p.vert (k * loopStart p t) : List ℕ)).erase (blockMarker p (loopStart p t))).getLastD 0)
    (rotClass (((p.vert (k * loopStart p t) : List ℕ)).erase (blockMarker p (loopStart p t))).dropLast)

/-! ## §4. Step equations — the wave's core deliverable

The table (boundary kind × state function) that every downstream lemma pattern-matches on:

| into block `t+1` | `doorDepth (t+1)`     | `metaDepth (t+1)`      |
|------------------|-----------------------|------------------------|
| door             | `doorDepth t + 1`     | `metaDepth t` (carry)  |
| α, `IsComplete t`| `0`                   | `metaDepth t + 1`      |
| meta-heavy       | `0`                   | `0` (reset)            |
-/

@[simp] theorem doorDepth_zero (p : HPath k) : doorDepth p 0 = 0 := rfl

theorem doorDepth_door {p : HPath k} {t : ℕ} (h : IsDoor p (t + 1)) :
    doorDepth p (t + 1) = doorDepth p t + 1 := by
  show (if IsDoor p (t + 1) then doorDepth p t + 1 else 0) = doorDepth p t + 1
  rw [if_pos h]

theorem doorDepth_not_door {p : HPath k} {t : ℕ} (h : ¬ IsDoor p (t + 1)) :
    doorDepth p (t + 1) = 0 := by
  show (if IsDoor p (t + 1) then doorDepth p t + 1 else 0) = 0
  rw [if_neg h]

/-- `doorDepth` never exceeds the block index (it counts consecutive doors starting from `0`). -/
theorem doorDepth_le (p : HPath k) (t : ℕ) : doorDepth p t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases h : IsDoor p (t + 1)
    · rw [doorDepth_door h]; omega
    · rw [doorDepth_not_door h]; omega

/-- Extraction: every block strictly inside the current door-run has a **door** boundary.
`j < doorDepth p t → IsDoor p (t − j)`.  This manufactures `alpha_run_bound`'s `hdoor` inputs
from `IsComplete`. -/
theorem isDoor_of_lt_doorDepth (p : HPath k) :
    ∀ t j, j < doorDepth p t → IsDoor p (t - j) := by
  intro t
  induction t with
  | zero => intro j hj; simp at hj
  | succ t ih =>
    intro j hj
    by_cases h : IsDoor p (t + 1)
    · rw [doorDepth_door h] at hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; simpa using h
      · have : t + 1 - j = t - (j - 1) := by omega
        rw [this]; exact ih (j - 1) (by omega)
    · rw [doorDepth_not_door h] at hj; omega

theorem metaDepth_zero (p : HPath k) : metaDepth p 0 = 0 := rfl

theorem metaDepth_alpha_complete {p : HPath k} {t : ℕ}
    (hα : IsAlpha p (t + 1)) (hc : IsComplete p t) :
    metaDepth p (t + 1) = metaDepth p t + 1 := by
  show (if IsAlpha p (t + 1) ∧ IsComplete p t then metaDepth p t + 1
        else if IsMetaHeavy p (t + 1) then 0 else metaDepth p t) = metaDepth p t + 1
  rw [if_pos ⟨hα, hc⟩]

theorem metaDepth_metaHeavy {p : HPath k} {t : ℕ} (h : IsMetaHeavy p (t + 1)) :
    metaDepth p (t + 1) = 0 := by
  show (if IsAlpha p (t + 1) ∧ IsComplete p t then metaDepth p t + 1
        else if IsMetaHeavy p (t + 1) then 0 else metaDepth p t) = 0
  have hne : ¬ (IsAlpha p (t + 1) ∧ IsComplete p t) := by
    rintro ⟨ha, hcc⟩; exact h.2 ⟨ha, hcc⟩
  rw [if_neg hne, if_pos h]

theorem metaDepth_door {p : HPath k} {t : ℕ} (h : IsDoor p (t + 1)) :
    metaDepth p (t + 1) = metaDepth p t := by
  show (if IsAlpha p (t + 1) ∧ IsComplete p t then metaDepth p t + 1
        else if IsMetaHeavy p (t + 1) then 0 else metaDepth p t) = metaDepth p t
  have hnα : ¬ (IsAlpha p (t + 1) ∧ IsComplete p t) := by
    rintro ⟨ha, _⟩; exact absurd ha.1 (by rw [IsDoor] at h; omega)
  have hnmh : ¬ IsMetaHeavy p (t + 1) := fun hmh => hmh.1 h
  rw [if_neg hnα, if_neg hnmh]

theorem runStart_zero (p : HPath k) : runStart p 0 = 0 := rfl

theorem runStart_metaHeavy {p : HPath k} {t : ℕ} (h : IsMetaHeavy p (t + 1)) :
    runStart p (t + 1) = t + 1 := by
  show (if IsMetaHeavy p (t + 1) then t + 1 else runStart p t) = t + 1
  rw [if_pos h]

theorem runStart_not_metaHeavy {p : HPath k} {t : ℕ} (h : ¬ IsMetaHeavy p (t + 1)) :
    runStart p (t + 1) = runStart p t := by
  show (if IsMetaHeavy p (t + 1) then t + 1 else runStart p t) = runStart p t
  rw [if_neg h]

/-! ## §5. Coverage and disjointness of the five boundary kinds -/

/-- **Coverage.**  Every boundary of an exitless path is one of the five kinds. -/
theorem boundary_classify_ledger {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts) :
    IsDoor p t ∨ IsAlpha p t ∨ IsSigmaSq p t ∨ IsMarkerMove p t ∨ IsHeavy p t := by
  have hkt : 1 ≤ k * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hkt1 : k * t - 1 + 1 = k * t := by omega
  have hd : k ∣ (k * t - 1 + 1) := by rw [hkt1]; exact ⟨t, rfl⟩
  have hi : (k * t - 1) + 1 < p.numVerts := by rw [hkt1]; exact hN
  have hcls := boundary_classify hk hp hi hd
  rw [hkt1] at hcls
  -- `ew k (p.vert (k*t-1)) (p.vert (k*t))` is `bw p t`; `marker p (k*t-1)` is `markPres`'s RHS
  rcases hcls with ⟨_, hw2⟩ | ⟨hw3, hmp, hword⟩ | ⟨hw3, hnmp⟩ | hw4
  · exact Or.inl hw2
  · rcases hword with hα | hσ
    · exact Or.inr (Or.inl ⟨hw3, hmp, hα⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hw3, hmp, hσ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hw3, hnmp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hw4)))

theorem not_isAlpha_of_isDoor {p : HPath k} {t : ℕ} (h : IsDoor p t) : ¬ IsAlpha p t := by
  rw [IsDoor] at h; rintro ⟨h3, _⟩; omega

theorem not_isDoor_of_isHeavy {p : HPath k} {t : ℕ} (h : IsHeavy p t) : ¬ IsDoor p t := by
  rw [IsHeavy] at h; rw [IsDoor]; omega

theorem not_isAlpha_of_isHeavy {p : HPath k} {t : ℕ} (h : IsHeavy p t) : ¬ IsAlpha p t := by
  rw [IsHeavy] at h; rintro ⟨h3, _⟩; omega

theorem not_isAlpha_of_isMarkerMove {p : HPath k} {t : ℕ} (h : IsMarkerMove p t) :
    ¬ IsAlpha p t := fun ha => h.2 ha.2.1

theorem not_isSigmaSq_of_isMarkerMove {p : HPath k} {t : ℕ} (h : IsMarkerMove p t) :
    ¬ IsSigmaSq p t := fun hs => h.2 hs.2.1

/-! ## §6. The structural invariants -/

/-- **σ² lives only in the incomplete regime.**  A σ² boundary into block `t` forces the
2-loop ending at `t − 1` to be *incomplete*.  Contrapositive of `lemmaA_sigmaSq_excluded`: a σ²
leaving a **complete** door-run would have its target coincide with an already-visited block
start, contradicting `HPath.Nodup`.  This is why a σ² never appears inside a chained α-run. -/
theorem sigmaSq_incomplete_only {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) {t : ℕ}
    (hN : k * t < p.numVerts) (hσ : IsSigmaSq p t) : ¬ IsComplete p (t - 1) := by
  intro hcomp
  rw [IsComplete] at hcomp
  have hdle := doorDepth_le p (t - 1)
  rw [hcomp] at hdle
  set t₀ := t - (k - 1) with ht0
  have ht0k : t₀ + (k - 1) = t := by omega
  -- interior doors r = 1 … k-2 of the (complete) run land into blocks t₀ + r
  have hdoor : ∀ r, 1 ≤ r → r ≤ k - 2 →
      ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2 := by
    intro r hr1 hr2
    have hj : (k - 2) - r < doorDepth p (t - 1) := by rw [hcomp]; omega
    have hdr := isDoor_of_lt_doorDepth p (t - 1) ((k - 2) - r) hj
    have hidx : (t - 1) - ((k - 2) - r) = t₀ + r := by omega
    rw [hidx, IsDoor, bw] at hdr
    exact hdr
  have hσword : (p.vert (k * (t₀ + (k - 1))) : List ℕ)
      = sigmaSqWord (p.vert (k * (t₀ + (k - 1)) - 1) : List ℕ) := by
    rw [ht0k]; exact hσ.2.2
  have hN' : k * (t₀ + (k - 1)) < p.numVerts := by rw [ht0k]; exact hN
  exact lemmaA_sigmaSq_excluded hk hp t₀ hN' hdoor hσword

/-- A σ² boundary is meta-heavy (from `sigmaSq_incomplete_only`). -/
theorem metaHeavy_of_isSigmaSq {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) {t : ℕ}
    (hN : k * t < p.numVerts) (h : IsSigmaSq p t) : IsMetaHeavy p t := by
  refine ⟨?_, ?_⟩
  · have := h.1; rw [IsDoor]; omega
  · rintro ⟨_, hc⟩; exact sigmaSq_incomplete_only hk hp hN h hc

/-- A marker-move boundary is meta-heavy. -/
theorem metaHeavy_of_isMarkerMove {p : HPath k} {t : ℕ} (h : IsMarkerMove p t) :
    IsMetaHeavy p t := by
  refine ⟨?_, ?_⟩
  · have := h.1; rw [IsDoor]; omega
  · rintro ⟨ha, _⟩; exact h.2 ha.2.1

/-- A heavy (weight-≥4) boundary is meta-heavy. -/
theorem metaHeavy_of_isHeavy {p : HPath k} {t : ℕ} (h : IsHeavy p t) : IsMetaHeavy p t :=
  ⟨not_isDoor_of_isHeavy h, fun hac => not_isAlpha_of_isHeavy h hac.1⟩

/-- **`metaDepth` reset — σ².**  A σ² boundary resets the meta-chain. -/
theorem metaDepth_sigmaSq_reset {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) {t : ℕ}
    (hN : k * (t + 1) < p.numVerts) (h : IsSigmaSq p (t + 1)) : metaDepth p (t + 1) = 0 :=
  metaDepth_metaHeavy (metaHeavy_of_isSigmaSq hk hp hN h)

/-- **`metaDepth` reset — marker-move.** -/
theorem metaDepth_markerMove_reset {p : HPath k} {t : ℕ} (h : IsMarkerMove p (t + 1)) :
    metaDepth p (t + 1) = 0 :=
  metaDepth_metaHeavy (metaHeavy_of_isMarkerMove h)

/-- **`metaDepth` reset — heavy.** -/
theorem metaDepth_heavy_reset {p : HPath k} {t : ℕ} (h : IsHeavy p (t + 1)) :
    metaDepth p (t + 1) = 0 :=
  metaDepth_metaHeavy (metaHeavy_of_isHeavy h)

/-- **`runStart` reset — meta-heavy.**  Any meta-heavy boundary starts a fresh α-run. -/
theorem runStart_reset {p : HPath k} {t : ℕ} (h : IsMetaHeavy p (t + 1)) :
    runStart p (t + 1) = t + 1 := runStart_metaHeavy h

/-- **Marker constancy along a run.**  For every block whose start lies in the path, the
block-marker equals the fixed run-marker `α₁` read off `runStart`.  Doors keep it fixed
(`marker_door_step`); complete-loop α's keep it fixed (`marker_alpha_step`); every meta-heavy
restarts the run at the current block, where the equality is trivial. -/
theorem ledger_marker_const {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) :
    ∀ t, k * t < p.numVerts → blockMarker p t = α₁ p t := by
  have hk2 : 2 ≤ k := by omega
  intro t
  induction t with
  | zero => intro _; rw [α₁, runStart_zero]
  | succ t ih =>
    intro hN
    have hNt : k * t < p.numVerts := by
      have : k * t ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega)
      omega
    by_cases hmh : IsMetaHeavy p (t + 1)
    · rw [α₁, runStart_metaHeavy hmh]
    · have hrs : runStart p (t + 1) = runStart p t := runStart_not_metaHeavy hmh
      have hα1 : α₁ p (t + 1) = blockMarker p (runStart p t) := by rw [α₁, hrs]
      have ihv : blockMarker p t = blockMarker p (runStart p t) := by
        have := ih hNt; rw [α₁] at this; exact this
      rw [hα1]
      by_cases hdoor : IsDoor p (t + 1)
      · have hw : ew k (p.vert (k * (t + 1) - 1)) (p.vert (k * (t + 1))) = 2 := hdoor
        have hmk : (p.vert (k * ((t + 1) - 1)) : List ℕ).getLastD 0
            = blockMarker p (runStart p t) := by
          rw [show (t + 1) - 1 = t from rfl]; exact ihv
        have hstep := marker_door_step hk2 hp (t := t + 1) (by omega) hN hw hmk
        rw [blockMarker]; exact hstep
      · have hAC : IsAlpha p (t + 1) ∧ IsComplete p ((t + 1) - 1) := by
          by_contra hc; exact hmh ⟨hdoor, hc⟩
        have hmark : (p.vert (k * (t + 1)) : List ℕ).getLastD 0
            = (rho (p.vert (k * (t + 1) - 1) : List ℕ)).getLastD 0 := hAC.1.2.1
        have hmk : (p.vert (k * ((t + 1) - 1)) : List ℕ).getLastD 0
            = blockMarker p (runStart p t) := by
          rw [show (t + 1) - 1 = t from rfl]; exact ihv
        have hstep := marker_alpha_step (by omega : 1 ≤ k) hp (t := t + 1) (by omega)
          (le_of_lt hN) hmark hmk
        rw [blockMarker]; exact hstep

/-- **Door-run marker constancy + exact meta-word rotation** (reusable engine, also for Wave 2).
Along a door-run rooted at `t₀` (interior boundaries into `t₀+1 … t₀+d` all weight-2), every
block-start keeps the run-marker `α₁ = (p.vert (k·t₀)).getLastD 0` as its last symbol, and its
marker-erased meta-word is the `r`-fold rotation of `t₀`'s.  This is `ProofsMeta4`'s door-run
engine (as inside `lemmaA_sigmaSq_excluded`) exposed as a named function of `p`. -/
theorem door_run_metaWord {p : HPath k} (hk : 2 ≤ k) (hp : p.Exitless) (t₀ d : ℕ)
    (hN : k * (t₀ + d) < p.numVerts)
    (hdoor : ∀ r, 1 ≤ r → r ≤ d →
        ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2) :
    ∀ r, r ≤ d →
      (p.vert (k * (t₀ + r)) : List ℕ).getLastD 0 = (p.vert (k * t₀) : List ℕ).getLastD 0 ∧
      (p.vert (k * (t₀ + r)) : List ℕ).erase ((p.vert (k * t₀) : List ℕ).getLastD 0)
        = ((p.vert (k * t₀) : List ℕ).erase ((p.vert (k * t₀) : List ℕ).getLastD 0)).rotate r := by
  set α₁v : ℕ := (p.vert (k * t₀) : List ℕ).getLastD 0 with hα1def
  set u : List ℕ := (p.vert (k * t₀) : List ℕ).erase α₁v with hudef
  have hpos : ∀ s, s ≤ d → k * (t₀ + s) < p.numVerts := by
    intro s hs
    have : k * (t₀ + s) ≤ k * (t₀ + d) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [Nat.add_zero]
    · rw [Nat.add_zero, List.rotate_zero, hudef]
  | succ r ih =>
    intro hr
    obtain ⟨hmarkr, hmetar⟩ := ih (by omega)
    have hN' : k * (t₀ + (r + 1)) < p.numVerts := hpos (r + 1) (by omega)
    have hw : ew k (p.vert (k * (t₀ + (r + 1)) - 1)) (p.vert (k * (t₀ + (r + 1)))) = 2 :=
      hdoor (r + 1) (by omega) hr
    have hmk : (p.vert (k * (t₀ + (r + 1) - 1)) : List ℕ).getLastD 0 = α₁v := by
      rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega]; exact hmarkr
    refine ⟨?_, ?_⟩
    · exact marker_door_step hk hp (t := t₀ + (r + 1)) (by omega) hN' hw hmk
    · have hstep := metaWord_door_block hk hp (t := t₀ + (r + 1)) (by omega) hN' hw hmk
      rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega, hmetar, List.rotate_rotate] at hstep
      exact hstep

/-- **Confinement of the current 2-loop.**  Every block-start of the current door-run (blocks
`loopStart p t … t`) lies in the fixed level-3 marked loop `curVset3 p t`.  From
`door_run_metaWord` (meta-word rotation) + `Vset3_of_metaWord_rotate_iter` (rotation-closure of
`Vset3`); the base membership is the door-run root's own `genLoop`.  (The α-run-wide version —
across chained 2-loops — is Wave 2, needing `Vset3_of_metaWord_complete_alpha`.) -/
theorem ledger_confined {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) {t : ℕ}
    (hN : k * t < p.numVerts) :
    ∀ r, r ≤ doorDepth p t → p.vert (k * (loopStart p t + r)) ∈ curVset3 p t := by
  have hk2 : 2 ≤ k := by omega
  have hdt := doorDepth_le p t
  set d := doorDepth p t with hd
  set t₀ := loopStart p t with ht0
  have ht0d : t₀ + d = t := by rw [ht0, loopStart, ← hd]; omega
  have hN' : k * (t₀ + d) < p.numVerts := by rw [ht0d]; exact hN
  -- the interior doors of the run
  have hdoor : ∀ r, 1 ≤ r → r ≤ d →
      ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2 := by
    intro r hr1 hr2
    have hj : d - r < doorDepth p t := by rw [← hd]; omega
    have hdr := isDoor_of_lt_doorDepth p t (d - r) hj
    have hidx : t - (d - r) = t₀ + r := by rw [ht0, loopStart, ← hd]; omega
    rw [hidx, IsDoor, bw] at hdr
    exact hdr
  have hrun := door_run_metaWord hk2 hp t₀ d hN' hdoor
  -- base membership: the run root lies in its own Vset3 (its `genLoop` is `(α₂, K)` by def)
  have hbase : p.vert (k * t₀) ∈ Vset3 k ((p.vert (k * t₀) : List ℕ).getLastD 0)
      (((p.vert (k * t₀) : List ℕ).erase ((p.vert (k * t₀) : List ℕ).getLastD 0)).getLastD 0)
      (rotClass ((p.vert (k * t₀) : List ℕ).erase
        ((p.vert (k * t₀) : List ℕ).getLastD 0)).dropLast) := by
    apply mem_Vset3_of_genLoop_metaWord; rfl
  intro r hr
  obtain ⟨_, hmeta⟩ := hrun r hr
  rw [curVset3, ← ht0]
  exact Vset3_of_metaWord_rotate_iter hbase hmeta

/-! ## §7. The run-conditioned meta-depth bound (full `metaDepth_le` deferred to Wave 2)

`metaDepth_le_of_run` feeds the ledger predicates `IsDoor`/`IsAlpha` (whose `IsAlpha` already
*bakes in* the `alphaWord` equality that a raw path only gets via `lemmaA_alphaWord`) directly
into the proved `alpha_run_bound`.  The **unconditional** `metaDepth p t ≤ k − 2` needs the
path→run extraction (Wave 2 / L5) that manufactures the positional `t₀`, `m` and the block-index
arithmetic `t₀ + j·(k−1) + r` from the `metaDepth` recursion; the ledger side is ready here. -/

/-- **Run-conditioned `metaDepth ≤ k − 2`.**  A maximal α-run of `m` complete 2-loops rooted at
block `t₀` — its `k−2` interior boundaries `IsDoor`, its `m−1` terminators `IsAlpha` — has
`m ≤ k − 2`.  Thin wrapper over `alpha_run_bound`; the ledger predicates discharge its inputs. -/
theorem metaDepth_le_of_run {p : HPath k} (hk : 3 ≤ k) (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m * (k - 1)) ≤ p.numVerts)
    (hdoor : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 → IsDoor p (t₀ + j * (k - 1) + r))
    (halpha : ∀ c, 1 ≤ c → c < m → IsAlpha p (t₀ + c * (k - 1))) :
    m ≤ k - 2 := by
  refine alpha_run_bound hk hp t₀ m hN ?_ ?_
  · intro j r hj hr1 hr2
    have h := hdoor j r hj hr1 hr2
    rw [IsDoor, bw] at h; exact h
  · intro c hc1 hc2
    have h := halpha c hc1 hc2
    exact ⟨h.1, h.2.1, h.2.2⟩

/-! ## §8. Calibration — tracing the ledger on the ℓ = 120 (k = 5) DP witness

Data from `THM2-EVIDENCE.md` (ℓ=120: excess 6, weight histogram `{1:96, 2:18, 3:4, 4:1}`,
frontier tight) and the mechanism report (DESIGN §5 R2).  At `k = 5`: `k−1 = 4` blocks per
complete 2-loop, `k−2 = 3` interior doors; `ℓ₀ = 55`, one window `M = (k−1)(k−2) − 1 = 11`
block-cycles.

The witness's block-boundary kinds run in the reported `D D D a  …  4  …` pattern (three doors
then an α terminating each complete 2-loop, a lone weight-4 heavy at the meta-cap crossing):

```
block t        :  0   1   2   3 | 4   5   6   7 | 8   9  10  11 | 12  …
bw p t (into t):  -   2   2   2 | 3   2   2   2 | 3   2   2   2 | 4   …    (a = α w-3, 4 = heavy)
kind           :  -  Door Door Door|Alpha Door Door Door|Alpha Door Door Door|Heavy …
doorDepth p t  :  0   1   2   3 | 0   1   2   3 | 0   1   2   3 |  0   …    (=k−2=3 ⇒ IsComplete)
IsComplete p t :  F   F   F   T | F   F   F   T | F   F   F   T |  F   …
metaDepth p t  :  0   0   0   0 | 1   1   1   1 | 2   2   2   2 |  0   …    (metaseq of DESIGN §5 R2)
```

* `doorDepth` reaches `k−2 = 3` at the last block of each 2-loop → `IsComplete` there; the next
  α fires `metaDepth_alpha_complete`, so `metaDepth` steps `0 → 1 → 2` at the 2-loop boundaries.
* the observed `metaDepth` cap is **2 = k−3**, inside the proved bound `k−2 = 3`
  (`metaDepth_le_of_run`) — the run never fills to the cap before the heavy ejects it.
* the lone **weight-4** heavy sits exactly at the meta-cap crossing (`doorDepth = k−2`,
  `metaDepth = k−3`) and, being `IsHeavy ⇒ IsMetaHeavy`, fires `metaDepth_heavy_reset` back to
  `0` — matching the mechanism report's "weight-4 at the meta-cap crossing, metaDepth ≤ 2".
* `sigmaSq_incomplete_only` is vacuously consistent with the witness: **zero** σ² boundaries
  leave a complete loop (relative-exitless dossier Q-T2, 120/120), so no σ² ever appears inside
  the chained α-run traced above.
-/

end ProofsLedger

end Hunter

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsClose

/-!
# Theorem 2 — the EXTENDED POTENTIAL CERTIFICATE (`Hunter.ProofsTheorem`)

This is the final-assembly pass.  It carries the *extended* explicit potential certificate
(`scratchpad/campaign/extend/`, verified `k = 5 … 14`, 0 violations) which augments the
`ProofsPotential` state space with a **defective slab** state `D(d')` — reusing the normal
potential shifted by one door, `h'(D(d'), b) = h(d'+1, 0, b)` — and thereby discharges the
**marker-move-from-complete kernel `mmc_ineq`** that `PROGRESS-close.md` §2 recorded as having
"no known clean symbolic proof".

The extended certificate reduces the single-step obstruction to the already-proved
`Dfr_add_Wpot_ge` (the `h`-nonnegativity core), so `mmc_ineq` is a short arithmetic corollary.
The per-transition inequalities of the defective slab (`D-door`/`D-reset`/`D-heavy`) are the
`ProofsPotential` inequalities read at door-depth `d'+1`.  The G3 tail lemma `tail_pays`
(`cost + h ≥ δ` for every outgoing transition) closes the terminal partial-block demand jump.

## Honesty (see `PROGRESS-theorem.md`)

The arithmetic certificate closes completely and sorry-free.  Re-deriving the walk invariant with
the defective state (`ExtWalk` below) discharges **every** boundary case — including the mmc kernel
via `mmc_ineq` — leaving exactly ONE sharp, computationally-certified **path-structural** residual:
a defective slab that reaches door-depth `k−3` must eject via a *heavy* (weight `≥ 4`) boundary,
never a cost-1 marker-move/σ².  `Hunter.Proved.fill_path` gives only single-block non-completion
(door-depth `≤ k−3`), which *permits* a cost-1 eject at door-depth `k−3`; and that eject is
genuinely **unpayable** by the certificate (numerically verified: `D-reset` at `d' = k−3` fails,
`D-heavy` succeeds).  The missing fact lives in `ProofsFill`/`ProofsFillPath` (outside this pass's
edit scope) and is not among the proved leaves, so it is carried as the named `Prop`
`DefectiveDeepExit`.  This is strictly finer than — and, unlike — the previous residual
`MMExclusion` (which asserted mm-from-complete *never occurs*, and is false: `fill_path` is
non-vacuous).

Namespace `Hunter.ProofsTheorem`.
-/

namespace Hunter

open scoped Classical
open List

namespace ProofsTheorem

open ProofsPotential ProofsLedger ProofsLedger2 ProofsWalk ProofsClose ProofsM1
open ProofsRecursion HPath

variable {k : ℕ}

/-! ## §1. The defective-slab potential `hpotD` and its nonnegativity

`hpotD k d' b := hpot k (d'+1) 0 b` — the defective state `D(d')` reuses the *normal* potential at
door-depth `d'+1`, meta-depth `0`.  A defective slab is opened one door "ahead" of its actual door
count (the fill-lemma headroom the certificate spends), so `d'` ranges `0 … k−4` and the hpot
door-argument `d'+1` ranges `1 … k−3`. -/

/-- **Defective-slab potential.**  `hpotD k d' b = hpot k (d'+1) 0 b`. -/
def hpotD (k d' b : ℕ) : ℕ := hpot k (d' + 1) 0 b

/-- `hpotD` unfolds to the normal potential at door-depth `d'+1`. -/
theorem hpotD_eq (k d' b : ℕ) : hpotD k d' b = hpot k (d' + 1) 0 b := rfl

/-- **`hpotD` nonnegativity** (= the `Dfr_add_Wpot_ge` instance).  `hpotD` is a `ℕ`, so `0 ≤ hpotD`
is definitional; the honest content is that the underlying `hpot` subtraction does not truncate,
recorded by `hpot_val` at `(d'+1, 0)`.  For `1 ≤ b`, `d'+1 ≤ k−2`:
`hpotD k d' b + (k−3) + Dfr k b = Dfr k (b + Wpot k (d'+1) 0)`. -/
theorem hpotD_nonneg (hk : 4 ≤ k) {b d' : ℕ} (hb : 1 ≤ b) (hd : d' + 1 ≤ k - 2) :
    hpotD k d' b + (k - 3) + Dfr k b = Dfr k (b + Wpot k (d' + 1) 0) := by
  have h := hpot_val hk hb (show (0 : ℕ) ≤ k - 3 by omega) hd
  simpa [hpotD] using h

/-! ## §2. The marker-move-from-complete kernel `mmc_ineq`  (the closed G2 obstruction)

The single-step inequality for a cost-1 marker-move leaving a *complete* source `(k−2, j)` into the
defective entry `D(0)` (potential `hpotD k 0 = hpot k 1 0`).  Two `hpot_val` rewrites collapse the
window: the target index `(b+1)+Wpot(1,0) = b + M`, so `Dfr_shift_exact` (needs `b ≥ 2`) turns the
target into `Dfr b + (k−2)`, and the residual is exactly `hpot k (k−2) j b ≥ 0` — the
`Dfr_add_Wpot_ge` honesty core.  Guards calibrated from the walk: a complete source has door-depth
`k−2`, so its block index `b ≥ k−2 ≥ 2`; and `j ≤ k−3` from the run cap `metaDepth ≤ k−3`. -/

/-- **MMC — marker-move-from-complete** (cost 1, `d = k−2`, into `D(0)`).  For `b ≥ 2`, `j ≤ k−3`:
`hpot k 1 0 (b+1) + Dfr k (b+1) ≤ 1 + hpot k (k−2) j b + Dfr k b`.  Reduces to `hpot k (k−2) j b ≥ 0`
after `Dfr_shift_exact`; the previously-open G2 kernel, now proved symbolically. -/
theorem mmc_ineq (hk : 4 ≤ k) {b j : ℕ} (hb : 2 ≤ b) (hj : j ≤ k - 3) :
    hpot k 1 0 (b + 1) + Dfr k (b + 1) ≤ 1 + hpot k (k - 2) j b + Dfr k b := by
  -- source value: hpot k (k−2) j b + (k−3−j) + Dfr b = Dfr (b + Wpot (k−2) j)
  have v1 := hpot_val hk (show 1 ≤ b by omega) hj (show k - 2 ≤ k - 2 by omega)
  -- target value: hpot k 1 0 (b+1) + (k−3) + Dfr (b+1) = Dfr ((b+1) + Wpot 1 0)
  have v2 := hpot_val hk (show 1 ≤ b + 1 by omega) (show (0 : ℕ) ≤ k - 3 by omega)
    (show (1 : ℕ) ≤ k - 2 by omega)
  -- index collapse: (b+1) + Wpot k 1 0 = b + Mper k
  have hidx : (b + 1) + Wpot k 1 0 = b + Mper k := by
    have hAlb : 2 ≤ (k - 1) * (k - 2) := by
      have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
    simp only [Wpot, Mper, Nat.sub_zero]; omega
  rw [hidx] at v2
  -- shift: Dfr (b + Mper k) = Dfr b + (k−2)
  have hshift := Dfr_shift_exact (show 3 ≤ k by omega) (show 2 ≤ b by omega)
  -- hpot k 1 0 (b+1) reduces its k−3−0 to k−3
  have hcred : k - 3 - 0 = k - 3 := by omega
  rw [hcred] at v2
  omega

/-! ## §3. The defective-slab transition inequalities (`D-door`/`D-reset`/`D-heavy`)

Each is a `ProofsPotential` inequality read at door-depth `d'+1`, meta-depth `0`. -/

/-- **D-door** (cost 0, `d' + 1 < k−2`): `D(d') → D(d'+1)`. -/
theorem Ddoor_ineq (hk : 4 ≤ k) {b d' : ℕ} (hb : 1 ≤ b) (hd : d' + 1 < k - 2) :
    hpotD k (d' + 1) (b + 1) + Dfr k (b + 1) ≤ hpotD k d' b + Dfr k b := by
  have h := door_ineq hk hb hd (show (0 : ℕ) ≤ k - 3 by omega)
  simpa [hpotD] using h

/-- **D-reset** (cost 1, `d' + 1 ≤ k−3`): `D(d') → N(0,0)`. -/
theorem Dreset_ineq (hk : 4 ≤ k) {b d' : ℕ} (hb : 1 ≤ b) (hd : d' + 1 ≤ k - 3) :
    hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 1 + hpotD k d' b + Dfr k b := by
  have h := reset_ineq hk hb hd (show (0 : ℕ) ≤ k - 3 by omega)
  simpa [hpotD] using h

/-- **D-heavy** (cost 2, `d' + 1 ≤ k−2`): `D(d') → N(0,0)`. -/
theorem Dheavy_ineq (hk : 4 ≤ k) {b d' : ℕ} (hb : 1 ≤ b) (hd : d' + 1 ≤ k - 2) :
    hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 2 + hpotD k d' b + Dfr k b := by
  have h := heavy_ineq hk hb hd (show (0 : ℕ) ≤ k - 3 by omega)
  simpa [hpotD] using h

/-! ## §4. The defective-slab indicator `IsDefective` (positional, no new recursion)

A block `t` is **defective** iff its current door-run was opened by a marker-move leaving a
*complete* source — i.e. the boundary into the door-run root `loopStart p t` is mm-from-complete.
`loopStart` is *constant across doors* and *resets to `t+1` at every non-door*, so `IsDefective`
inherits the exact transition table of the certificate's `D`-flag without a new recursive definition.
Its key property — a defective block is never complete — is precisely `Proved.fill_path`. -/

/-- The boundary into block `t` is a **marker-move from a complete source**. -/
def defOpen (p : HPath k) (t : ℕ) : Prop := IsMarkerMove p t ∧ IsComplete p (t - 1)

/-- **Defective block**: its door-run root opened via mm-from-complete. -/
def IsDefective (p : HPath k) (t : ℕ) : Prop := defOpen p (loopStart p t)

/-- `loopStart` is constant across a door. -/
theorem loopStart_door {p : HPath k} {t : ℕ} (h : IsDoor p (t + 1)) :
    loopStart p (t + 1) = loopStart p t := by
  have hle := doorDepth_le p t
  rw [loopStart, loopStart, doorDepth_door h]; omega

/-- `loopStart` resets to `t+1` at a non-door. -/
theorem loopStart_not_door {p : HPath k} {t : ℕ} (h : ¬ IsDoor p (t + 1)) :
    loopStart p (t + 1) = t + 1 := by
  rw [loopStart, doorDepth_not_door h]; omega

/-- Defectiveness carries across a door. -/
theorem isDefective_door {p : HPath k} {t : ℕ} (h : IsDoor p (t + 1)) :
    IsDefective p (t + 1) ↔ IsDefective p t := by
  unfold IsDefective; rw [loopStart_door h]

/-- After a non-door, a block is defective iff that boundary is mm-from-complete. -/
theorem isDefective_not_door {p : HPath k} {t : ℕ} (h : ¬ IsDoor p (t + 1)) :
    IsDefective p (t + 1) ↔ (IsMarkerMove p (t + 1) ∧ IsComplete p t) := by
  unfold IsDefective defOpen; rw [loopStart_not_door h]; simp

/-- **A defective block is never complete** (via `Proved.fill_path`).  If the door-run root
`r = loopStart p t` opened by mm-from-complete, the opened slab cannot fill: were `t` complete it
would be exactly `r + (k−2)`, contradicting `fill_path`. -/
theorem isDefective_incomplete (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (hN : k * t < p.numVerts) (hdef : IsDefective p t) : ¬ IsComplete p t := by
  intro hc
  have hcd : doorDepth p t = k - 2 := hc
  set r := loopStart p t with hr
  have hrt : r = t - doorDepth p t := rfl
  have hle := doorDepth_le p t
  have htr : t = r + (k - 2) := by rw [hr, loopStart, hcd]; omega
  obtain ⟨hmm, hcomp⟩ := hdef
  -- r ≥ 1 : else IsComplete p 0 = (doorDepth p 0 = k−2) fails
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso
      have : doorDepth p (r - 1) = k - 2 := hcomp
      rw [h0] at this; simp only [Nat.zero_sub, doorDepth_zero] at this; omega
    · exact hpos
  have hNfill : k * (r + (k - 2)) < p.numVerts := by rw [← htr]; exact hN
  have hne := Proved.fill_path (show 3 ≤ k by omega) hp hr1 hNfill hmm hcomp
  rw [← htr] at hne
  exact hne hc

/-! ## §5. The extended potential `Hext` and the single path-structural residual

`Hext p t` is the certificate potential at block `t`: the defective potential `hpotD` when `t` is
defective, else the normal `hpot`. -/

/-- The extended potential: `hpotD` on defective blocks, `hpot` otherwise. -/
noncomputable def Hext (p : HPath k) (t : ℕ) : ℕ :=
  if IsDefective p t then hpotD k (doorDepth p t) t
  else hpot k (doorDepth p t) (metaDepth p t) t

theorem Hext_def {p : HPath k} {t : ℕ} (h : IsDefective p t) :
    Hext p t = hpotD k (doorDepth p t) t := by rw [Hext, if_pos h]

theorem Hext_norm {p : HPath k} {t : ℕ} (h : ¬ IsDefective p t) :
    Hext p t = hpot k (doorDepth p t) (metaDepth p t) t := by rw [Hext, if_neg h]

/-- **The single path-structural residual (`DefectiveDeepExit`).**  In an exitless path, a defective
slab that has reached door-depth `k−3` (its deepest, one short of completion) ejects via a *heavy*
(weight `≥ 4`) boundary — never a cost-1 marker-move/σ².  This is the one fact the extended
certificate needs beyond `Proved.fill_path`: `fill_path` gives only single-block non-completion
(door-depth `≤ k−3`), which permits a cost-1 eject at door-depth `k−3`, and that eject is genuinely
**unpayable** by the certificate (`D-reset` at `d' = k−3` fails numerically; `D-heavy` succeeds).
Computationally certified (`certify2.py`, 0 failures `k = 5,6,7,8`); it lives in `ProofsFill` /
`ProofsFillPath`, outside this pass's edit scope, and is not among the proved leaves. -/
def DefectiveDeepExit (k : ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → ∀ t, k * (t + 1) < p.numVerts →
    IsDefective p t → doorDepth p t = k - 3 → ¬ IsDoor p (t + 1) → IsHeavy p (t + 1)

/-! ## §6. The extended per-block potential step (`ext_walk_step`)

Every boundary kind, split on the defectiveness of the source, mapped to its certificate inequality:
the previously-open **mm-from-complete** case now routes into `D(0)` via `mmc_ineq`; the defective
transitions use `Ddoor`/`Dreset`/`Dheavy`; the deepest cost-1 defective eject is excluded by the
residual `hDE`.  There is **no `hmmc` hypothesis**. -/

/-- **The extended per-block potential step.**  Under the run cap (`hj`/`hj'`) and the deepest-eject
residual instance `hDE`, the boundary into block `t+1` moves the extended potential by no more than
its excess contribution `bw − 2`. -/
theorem ext_walk_step (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + 1) < p.numVerts)
    (hj : metaDepth p t ≤ k - 3) (hj' : metaDepth p (t + 1) ≤ k - 3)
    (hDE : IsDefective p t → doorDepth p t = k - 3 → ¬ IsDoor p (t + 1) → IsHeavy p (t + 1)) :
    Dfr k (t + 1) + Hext p (t + 1) ≤ (bw p (t + 1) - 2) + (Dfr k t + Hext p t) := by
  have hk' : 3 ≤ k := by omega
  have hexp : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
  have hNt : k * t < p.numVerts := by omega
  have hd_le : doorDepth p t ≤ k - 2 := doorDepth_le_km2 hk' hp t hNt
  have hd_le' : doorDepth p (t + 1) ≤ k - 2 := doorDepth_le_km2 hk' hp (t + 1) hN
  set d := doorDepth p t with hddef
  set m := metaDepth p t with hmdef
  have hnotdoor_dd : ¬ IsDoor p (t + 1) → doorDepth p (t + 1) = 0 := doorDepth_not_door
  -- IsComplete p t → ¬IsDefective p t
  have hcomp_notdef : IsComplete p t → ¬ IsDefective p t :=
    fun hc hdef => isDefective_incomplete hk hp hNt hdef hc
  by_cases hdeft : IsDefective p t
  · -- ===================== SOURCE DEFECTIVE =====================
    have hHt : Hext p t = hpotD k d t := Hext_def hdeft
    have hinc : ¬ IsComplete p t := isDefective_incomplete hk hp hNt hdeft
    have hdk3 : d ≤ k - 3 := by
      have : d ≠ k - 2 := hinc
      omega
    by_cases hdoor : IsDoor p (t + 1)
    · -- D-door : carry defective
      have hbw : bw p (t + 1) = 2 := hdoor
      have hdd : doorDepth p (t + 1) = d + 1 := doorDepth_door hdoor
      have hdef' : IsDefective p (t + 1) := (isDefective_door hdoor).mpr hdeft
      have hinc' : ¬ IsComplete p (t + 1) := isDefective_incomplete hk hp hN hdef'
      have hd1lt : d + 1 < k - 2 := by
        have : doorDepth p (t + 1) ≠ k - 2 := hinc'
        rw [hdd] at this; omega
      have hHt' : Hext p (t + 1) = hpotD k (d + 1) (t + 1) := by
        rw [Hext_def hdef', hdd]
      have hdi := Ddoor_ineq hk (show 1 ≤ t from ht) hd1lt
      rw [hHt', hHt, hbw]; omega
    · -- non-door eject : target normal (0,0)
      have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hdoor
      have hdef'_iff := isDefective_not_door hdoor
      have hnotdef' : ¬ IsDefective p (t + 1) := by
        rw [hdef'_iff]; rintro ⟨_, hc⟩; exact hinc hc
      -- target metaDepth = 0 (non-door, incomplete source ⇒ meta-heavy)
      have hmh : IsMetaHeavy p (t + 1) := by
        refine ⟨hdoor, ?_⟩; rintro ⟨_, hc⟩; exact hinc hc
      have hmd' : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
      have hHt' : Hext p (t + 1) = hpot k 0 0 (t + 1) := by
        rw [Hext_norm hnotdef', hdd, hmd']
      by_cases hheavy : IsHeavy p (t + 1)
      · -- D-heavy (cost ≥ 2)
        have hbw : 4 ≤ bw p (t + 1) := hheavy
        have hhi := Dheavy_ineq hk (show 1 ≤ t from ht) (show d + 1 ≤ k - 2 by omega)
        rw [hHt', hHt]; omega
      · -- cost-1 eject : must have d ≤ k−4, else residual forces heavy (contradiction)
        have hbw3 : bw p (t + 1) = 3 := by
          rcases boundary_classify_ledger hk' hp (show 1 ≤ t + 1 by omega) hN with
            h | h | h | h | h
          · exact absurd h hdoor
          · exact h.1
          · exact h.1
          · exact h.1
          · exact absurd h hheavy
        have hdk4 : d ≤ k - 4 := by
          by_contra hc
          have hd3 : d = k - 3 := by omega
          exact hheavy (hDE hdeft hd3 hdoor)
        have hri := Dreset_ineq hk (show 1 ≤ t from ht) (show d + 1 ≤ k - 3 by omega)
        rw [hHt', hHt, hbw3]; omega
  · -- ===================== SOURCE NORMAL =====================
    have hHt : Hext p t = hpot k d m t := Hext_norm hdeft
    rcases boundary_classify_ledger hk' hp (show 1 ≤ t + 1 by omega) hN with
      hdoor | hα | hσ | hmm | hheavy
    · -- DOOR (cost 0)
      have hbw : bw p (t + 1) = 2 := hdoor
      have hdd : doorDepth p (t + 1) = d + 1 := doorDepth_door hdoor
      have hmd : metaDepth p (t + 1) = m := metaDepth_door hdoor
      have hnotdef' : ¬ IsDefective p (t + 1) := fun h => hdeft ((isDefective_door hdoor).mp h)
      have hHt' : Hext p (t + 1) = hpot k (d + 1) m (t + 1) := by
        rw [Hext_norm hnotdef', hdd, hmd]
      have hdlt : d < k - 2 := by rw [hdd] at hd_le'; omega
      have hdi := door_ineq hk (show 1 ≤ t from ht) hdlt hj
      rw [hHt', hHt, hbw]; omega
    · -- ALPHA — split on completeness
      have hbw : bw p (t + 1) = 3 := hα.1
      have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
      have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
      have hnmm : ¬ IsMarkerMove p (t + 1) := fun h => not_isAlpha_of_isMarkerMove h hα
      have hnotdef' : ¬ IsDefective p (t + 1) := by
        rw [isDefective_not_door hnd]; rintro ⟨h, _⟩; exact hnmm h
      by_cases hc : IsComplete p t
      · -- α from complete → alpha_ineq
        have hdc : d = k - 2 := hc
        have hmd : metaDepth p (t + 1) = m + 1 := metaDepth_alpha_complete hα hc
        have hjk4 : m ≤ k - 4 := by rw [hmd] at hj'; omega
        have hHt' : Hext p (t + 1) = hpot k 0 (m + 1) (t + 1) := by
          rw [Hext_norm hnotdef', hdd, hmd]
        have hai := alpha_ineq hk (show 1 ≤ t from ht) hjk4
        rw [hHt', hHt, hbw, hdc]; omega
      · -- α from incomplete → reset
        have hmh : IsMetaHeavy p (t + 1) := ⟨hnd, fun h => hc h.2⟩
        have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
        have hne : d ≠ k - 2 := hc
        have hd3 : d ≤ k - 3 := by omega
        have hHt' : Hext p (t + 1) = hpot k 0 0 (t + 1) := by
          rw [Hext_norm hnotdef', hdd, hmd]
        have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
        rw [hHt', hHt, hbw]; omega
    · -- σ² → reset (incomplete source)
      have hbw : bw p (t + 1) = 3 := hσ.1
      have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
      have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
      have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isSigmaSq hk' hp hN hσ
      have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
      have hnmm : ¬ IsMarkerMove p (t + 1) := fun h => not_isSigmaSq_of_isMarkerMove h hσ
      have hnotdef' : ¬ IsDefective p (t + 1) := by
        rw [isDefective_not_door hnd]; rintro ⟨h, _⟩; exact hnmm h
      have hinc : ¬ IsComplete p t := by
        have := sigmaSq_incomplete_only hk' hp hN hσ
        rwa [show t + 1 - 1 = t from rfl] at this
      have hne : d ≠ k - 2 := hinc
      have hd3 : d ≤ k - 3 := by omega
      have hHt' : Hext p (t + 1) = hpot k 0 0 (t + 1) := by
        rw [Hext_norm hnotdef', hdd, hmd]
      have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
      rw [hHt', hHt, hbw]; omega
    · -- MARKER-MOVE — split on completeness (mmc vs reset)
      have hbw : bw p (t + 1) = 3 := hmm.1
      have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
      have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
      have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isMarkerMove hmm
      have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
      by_cases hc : IsComplete p t
      · -- mm from complete → D(0) via mmc_ineq
        have hdc : d = k - 2 := hc
        have hdef' : IsDefective p (t + 1) := by
          rw [isDefective_not_door hnd]; exact ⟨hmm, hc⟩
        have hHt' : Hext p (t + 1) = hpot k 1 0 (t + 1) := by
          rw [Hext_def hdef', hdd]; rfl
        have ht2 : 2 ≤ t := by
          have : k - 2 ≤ t := by rw [← hdc]; exact doorDepth_le p t
          omega
        have hmi := mmc_ineq hk ht2 hj
        rw [hHt', hHt, hbw, hdc]; omega
      · -- mm from incomplete → reset
        have hne : d ≠ k - 2 := hc
        have hd3 : d ≤ k - 3 := by omega
        have hnotdef' : ¬ IsDefective p (t + 1) := by
          rw [isDefective_not_door hnd]; rintro ⟨_, hcc⟩; exact hc hcc
        have hHt' : Hext p (t + 1) = hpot k 0 0 (t + 1) := by
          rw [Hext_norm hnotdef', hdd, hmd]
        have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
        rw [hHt', hHt, hbw]; omega
    · -- HEAVY (cost ≥ 2)
      have hbw : 4 ≤ bw p (t + 1) := hheavy
      have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor]; omega
      have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
      have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isHeavy hheavy
      have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
      have hnmm : ¬ IsMarkerMove p (t + 1) := by rintro ⟨h3, _⟩; omega
      have hnotdef' : ¬ IsDefective p (t + 1) := by
        rw [isDefective_not_door hnd]; rintro ⟨h, _⟩; exact hnmm h
      have hHt' : Hext p (t + 1) = hpot k 0 0 (t + 1) := by
        rw [Hext_norm hnotdef', hdd, hmd]
      have hhi := heavy_ineq hk (show 1 ≤ t from ht) hd_le hj
      rw [hHt', hHt]; omega

/-! ## §7. The extended walk invariant and the block-scale excess bound

The invariant `Dfr(t) + Hext(t) ≤ PE(t)` is preserved by every boundary (`ext_walk_step`), with
`Hext ≥ 0` giving `excess ≥ Dfr k T` at the last full block `T = (numVerts−1)/k` — carrying **only**
the sharp residual `DefectiveDeepExit` (G1's run cap is `runCap_discharged`, unconditional; there is
no `hMMC`). -/

/-- Blocks `0` and `1` are never defective (`IsComplete p 0` is false). -/
theorem not_isDefective_le1 (hk : 4 ≤ k) {p : HPath k} {s : ℕ} (hs : s ≤ 1) :
    ¬ IsDefective p s := by
  intro h
  have hc : IsComplete p (loopStart p s - 1) := h.2
  have h0 : loopStart p s - 1 = 0 := by rw [loopStart]; omega
  have hc' : doorDepth p (loopStart p s - 1) = k - 2 := hc
  rw [h0, doorDepth_zero] at hc'; omega

/-- **The extended walk invariant.**  Under the deepest-eject residual (`hDE`, G2) — with the run cap
`runCap_discharged` (G1) baked in — every block `t` within an exitless path satisfies
`Dfr k t + Hext p t ≤ PE p t`. -/
theorem ext_walk_invariant (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hDE : DefectiveDeepExit k) :
    ∀ t, k * t < p.numVerts → Dfr k t + Hext p t ≤ PE p t := by
  have hRunCap := runCap_discharged hk hp
  intro t
  induction t with
  | zero =>
    intro _
    rw [PE_zero, Hext_norm (not_isDefective_le1 hk (by omega)), doorDepth_zero, metaDepth_zero,
        Dfr_zero, hpot_000 hk]
  | succ t ih =>
    intro hN1
    have hexp : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
    have hNt : k * t < p.numVerts := by omega
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have hm1 : metaDepth p 1 = 0 := by
        have hnc : ¬ (IsAlpha p 1 ∧ IsComplete p 0) := by
          rintro ⟨_, hcc⟩
          have hc' : doorDepth p 0 = k - 2 := hcc
          rw [doorDepth_zero] at hc'; omega
        show (if IsAlpha p 1 ∧ IsComplete p 0 then metaDepth p 0 + 1
              else if IsMetaHeavy p 1 then 0 else metaDepth p 0) = 0
        rw [if_neg hnc]
        by_cases hmh : IsMetaHeavy p 1
        · rw [if_pos hmh]
        · rw [if_neg hmh]; rfl
      rw [Hext_norm (not_isDefective_le1 hk (le_refl 1)), hm1, hpot_block1 hk, Dfr_one (by omega)]
      exact Nat.zero_le _
    · have hstep := ext_walk_step hk hp htpos hN1 (hRunCap t hNt) (hRunCap (t + 1) hN1)
        (hDE p hp t hN1)
      have hpe := PE_step (by omega) p t
      have IHt := ih hNt
      omega

/-- **Block-scale frontier bound.**  Under `DefectiveDeepExit` (G2; G1 baked in), every exitless path
spends excess at least `Dfr k T` at the last full block `T = (numVerts − 1)/k`. -/
theorem ext_excess_ge_Dfr_block (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts)
    (hDE : DefectiveDeepExit k) :
    Dfr k ((p.numVerts - 1) / k) ≤ excess p := by
  set T := (p.numVerts - 1) / k with hT
  have hkpos : 0 < k := by omega
  have hkT : k * T ≤ p.numVerts - 1 := by rw [hT, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hTN : k * T < p.numVerts := by omega
  have hinv := ext_walk_invariant hk hp hDE T hTN
  have hple := PE_le_excess (by omega) T hTN
  omega

/-- **The G3 tail lemma `tail_pays`** (`cost + h ≥ δ`).  For every realized boundary of an exitless
path (under the run cap and `hDE`), the block demand increment `δ = Dfr(t+1) − Dfr(t)` is covered by
the boundary's cost plus the source potential: `Dfr k (t+1) − Dfr k t ≤ (bw p (t+1) − 2) + Hext p t`.
A corollary of `ext_walk_step` and `Hext ≥ 0`; the arithmetic mechanism the terminal partial-block
demand jump (G3) is paid by (the endpoint *vertex-level* gluing to `j k numVerts` still routes through
`TerminalFrontierTail`). -/
theorem tail_pays (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + 1) < p.numVerts)
    (hj : metaDepth p t ≤ k - 3) (hj' : metaDepth p (t + 1) ≤ k - 3)
    (hDE : IsDefective p t → doorDepth p t = k - 3 → ¬ IsDoor p (t + 1) → IsHeavy p (t + 1)) :
    Dfr k (t + 1) - Dfr k t ≤ (bw p (t + 1) - 2) + Hext p t := by
  have h := ext_walk_step hk hp ht hN hj hj' hDE
  omega

end ProofsTheorem

/-! ## §8. The `Hunter.Proved` capstones from the extended certificate

`M1WalkBound` reduces to the two residuals `DefectiveDeepExit` (G2, sharp/true) and
`TerminalFrontierTail` (G3, the endpoint vertex-gluing) — G1 (`runCap_discharged`) baked in.  The
previous G2 residual `MMExclusion` (asserting mm-from-complete *never occurs*, and false) is gone.
The Theorem-2 / Theorem-1 capstones follow through the existing `Proved` / `ProofsMF` chains. -/

namespace Proved

open ProofsRecursion ProofsM1 ProofsClose ProofsTheorem

variable {k : ℕ}

/-- **`M1WalkBound k` from the two residuals** (G1 baked in): the extended block-scale bound
(`ext_excess_ge_Dfr_block`, G2 = `DefectiveDeepExit`) lifted to the frontier demand at `numVerts`
by `TerminalFrontierTail` (G3). -/
theorem m1WalkBound_of_defExit (hk : 4 ≤ k) (hDE : DefectiveDeepExit k)
    (hG3 : TerminalFrontierTail k) : M1WalkBound k := by
  intro q hqe h0
  exact hG3 q hqe h0 (ext_excess_ge_Dfr_block hk hqe h0 hDE)

/-- **Theorem 2** (verbatim `Statements.thm2` conclusion) from the two residuals, with numeric guards
`hk`/`hℓ` only. -/
theorem thm2_final {ℓ : ℕ} (hk : 4 ≤ k) (hDE : DefectiveDeepExit k)
    (hG3 : TerminalFrontierTail k) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  Proved.thm2_of_m1 (by omega) (m1WalkBound_of_defExit hk hDE hG3) hℓ

/-- Global form of residual G2 (`DefectiveDeepExit`). -/
def DefectiveDeepExitAll : Prop := ∀ k, 4 ≤ k → DefectiveDeepExit k

/-- **The global M1 slab bound** from the residuals (base value `M1WalkBound 3`, G1 baked in). -/
theorem m1WalkBoundAll_of_defExit (hbase : M1WalkBound 3)
    (hDE : DefectiveDeepExitAll) (hG3 : TerminalFrontierTailAll) : Proved.M1WalkBoundAll := by
  intro k hk
  rcases Nat.lt_or_ge k 4 with hlt | hge
  · interval_cases k
    · exact hbase
  · exact m1WalkBound_of_defExit hge (hDE k hge) (hG3 k hge)

/-- **thm1v1** (superpermutation lower bound) from the residuals. -/
theorem thm1v1_theorem (hbase : M1WalkBound 3)
    (hDE : DefectiveDeepExitAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_of_m1 (m1WalkBoundAll_of_defExit hbase hDE hG3) hproof hexists

/-- **thm1v2** (`L(k) ≥ coeff(k)·k! − O(1)`) from the residuals. -/
theorem thm1v2_theorem (hbase : M1WalkBound 3)
    (hDE : DefectiveDeepExitAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_of_m1 (m1WalkBoundAll_of_defExit hbase hDE hG3) hproof hexists

/-- **eq-weak** (comparable-factorial form) from the residuals. -/
theorem eq_weak_theorem (hbase : M1WalkBound 3)
    (hDE : DefectiveDeepExitAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsMF.eq_weak_of_MF
    (Proved.frontierTightHeavyAll_of_m1All (m1WalkBoundAll_of_defExit hbase hDE hG3))
    hproof hexists

end Proved

end Hunter

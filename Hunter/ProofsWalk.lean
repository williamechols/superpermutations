/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsPotential
import Hunter.ProofsFillPath
import Hunter.ProofsLedger2

/-!
# Theorem 2 — the WALK INDUCTION (the block-scale gluing of the potential certificate)

This file assembles the **block-scale walk** that the explicit potential certificate
(`Hunter.ProofsPotential`) is built to consume.  It contributes:

* **§1 — the demand gluing identity** (`j_glue`): the length-scale frontier demand `j k (k·b)` and
  the block-scale demand `ProofsPotential.Dfr k b` agree,
  `j k (k·b) = Dfr k b + (k·b − 1) + (b − 1)`, for `b ≥ 1`.  This is the one arithmetic bridge
  `PROGRESS-potential.md §6` flagged as "still to write" — it links `ProofsCascade`'s
  `base_frontier`/`j_rec` recursion (period `ℓ₀ = k·M`) to `ProofsPotential`'s `Dfr` recursion
  (period `M`).  Both recursions reduce in lock-step because `ℓ₀ = k · Mper k`.

* **§2 — the partial-excess ledger** (`PE`): the prefix excess through block `t` as a pure `ℕ`
  edge-sum, with the one-block step `PE_step` (a boundary of weight `bw` adds `bw − 2`).

* **§3 — the per-block potential step** (`walk_step`): each ledger boundary kind
  (`ProofsLedger.boundary_classify_ledger`) is mapped onto one of the four certificate
  inequalities (`door_ineq`/`alpha_ineq`/`heavy_ineq`/`reset_ineq`), threading the state functions
  `doorDepth`/`metaDepth` through their step equations.

* **§4 — the walk invariant and the block-scale bound** (`walk_invariant`, `excess_ge_Dfr_block`):
  the invariant `Dfr(t) + h(state(t)) ≤ PE p t` is preserved by every boundary, giving
  `excess p ≥ Dfr k T` at the last full block `T = (numVerts − 1)/k`.

**Honesty on the residual** (see `PROGRESS-walk.md`).  The block-walk induction does **not** close
`M1WalkBound` outright: three sharply-characterised bridge facts remain beyond the proved leaves —
the tighter run-cap `metaDepth ≤ k−3` (G1), the marker-move-from-complete fill-absorption (G2), and
the non-block-aligned tail payment (G3).  G1/G2 are carried as explicit `Prop` hypotheses of
`walk_invariant`/`excess_ge_Dfr_block`, never as `sorry` or new axioms; G3 is the endpoint gluing not
performed here.  The Theorem-2 capstones therefore remain in `Hunter.Proved` (`ProofsPotential`)
unchanged, still carrying `M1WalkBound k`.

Namespace `Hunter.ProofsWalk`.
-/

namespace Hunter

open scoped Classical

namespace ProofsWalk

open ProofsPotential ProofsLedger ProofsLedger2 ProofsRecursion HPath

variable {k : ℕ}

/-! ## §1. The demand gluing identity `j k (k·b) = Dfr k b + (k·b − 1) + (b − 1)` -/

/-- `ell0 k = k · Mper k` — the two recursion periods are in lock-step (`ℓ₀` is `k` block-periods).
`ℓ₀ = k(k−1)(k−2) − k = k·((k−1)(k−2) − 1) = k · M`. -/
theorem ell0_eq_k_mul_Mper (_hk : 3 ≤ k) : ell0 k = k * Mper k := by
  have hrhs : k * Mper k = k * ((k - 1) * (k - 2)) - k := by
    rw [Mper, Nat.mul_sub, Nat.mul_one]
  rw [ell0, hrhs, Nat.mul_assoc]

/-- Arithmetic helper: `(k·b − 1) / (k·(k−1)) = (b − 1) / (k − 1)` for `k ≥ 2`, `b ≥ 1`.
The extra `k − 1` remainder introduced by the `−1` never crosses a `k·(k−1)`-block. -/
theorem key_div (hk : 2 ≤ k) {b : ℕ} (hb : 1 ≤ b) :
    (k * b - 1) / (k * (k - 1)) = (b - 1) / (k - 1) := by
  set q := (b - 1) / (k - 1) with hq
  set r := (b - 1) % (k - 1) with hr
  have hdm : (k - 1) * q + r = b - 1 := by rw [hq, hr]; exact Nat.div_add_mod (b - 1) (k - 1)
  have hrlt : r < k - 1 := by rw [hr]; exact Nat.mod_lt _ (by omega)
  -- `k*b - 1 = k*(k-1)*q + (k*r + (k-1))` with the remainder `< k*(k-1)`
  have hge : k ≤ k * b := Nat.le_mul_of_pos_right k (by omega)
  have hsplit : k * b - 1 = k * (k - 1) * q + (k * r + (k - 1)) := by
    have hmb : k * (b - 1) = k * ((k - 1) * q + r) := by rw [hdm]
    have h2 : k * (b - 1) = k * (k - 1) * q + k * r := by rw [hmb]; ring
    have hkbe : k * b = k * (b - 1) + k := by
      have hm1 : k * (b - 1) = k * b - k := by rw [Nat.mul_sub, Nat.mul_one]
      omega
    omega
  have hrem : k * r + (k - 1) < k * (k - 1) := by
    have hkk : k * (k - 1) = k * (k - 2) + k := by
      have he : k - 1 = (k - 2) + 1 := by omega
      rw [he, Nat.mul_add, Nat.mul_one]
    have hkr : k * r ≤ k * (k - 2) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  rw [hsplit, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.mul_pos (by omega) (by omega)),
      Nat.div_eq_of_lt hrem, Nat.zero_add]

/-- **The demand gluing identity.**  For `b ≥ 1` (and `k ≥ 4`), the length-scale frontier demand at
`k·b` vertices equals the block-scale demand `Dfr k b`:
`j k (k·b) = Dfr k b + (k·b − 1) + (b − 1)`.  Equivalently `Dfrontier(k·b) = Dfr b`. -/
theorem j_glue (hk : 4 ≤ k) {b : ℕ} (hb : 1 ≤ b) :
    j k (k * b) = Dfr k b + (k * b - 1) + (b - 1) := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    have hkpos : 0 < k := by omega
    have hcd_k : (k * b) ⌈/⌉ k = b := by
      rw [Proved.ceilDiv_of_dvd hkpos ⟨b, rfl⟩, Nat.mul_div_cancel_left b hkpos]
    by_cases hbase : b ≤ (k - 1) * (k - 2)
    · -- base window: `k*b ≤ k*(k-1)*(k-2)`, use `base_frontier` and `Dfr_base`
      have hkb1 : 1 ≤ k * b := by
        have := Nat.mul_pos (show 0 < k by omega) (show 0 < b by omega); omega
      have hkble : k * b ≤ k * (k - 1) * (k - 2) := by
        have : k * b ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hbase
        rw [← Nat.mul_assoc] at this; exact this
      have hbf := ProofsCascade.base_frontier (by omega) hkb1 hkble
      rw [hcd_k] at hbf
      -- `(k*b) ⌈/⌉ (k*(k-1)) = (b-1)/(k-1) + 1`
      have hcd_kk : (k * b) ⌈/⌉ (k * (k - 1)) = (b - 1) / (k - 1) + 1 := by
        rw [Proved.ceilDiv_succ_pred hkb1 (Nat.mul_pos (by omega) (by omega)),
            key_div (by omega) hb]
      rw [hcd_kk] at hbf
      have hDfr : Dfr k b = (b - 1) / (k - 1) := Dfr_base hbase
      rw [hbf, hDfr]; omega
    · -- recursion region: reduce by `ℓ₀ = k·M` (blocks) resp. `M` (blocks)
      push Not at hbase
      have hM := Mper_pos (by omega : 3 ≤ k)
      have hMval : Mper k = (k - 1) * (k - 2) - 1 := rfl
      have hbM : Mper k < b := by omega
      have hbM1 : 1 ≤ b - Mper k := by omega
      have hbMlt : b - Mper k < b := by omega
      -- length-scale recursion
      have hbaseR : k * (k - 1) * (k - 2) < k * b := by
        have : k * ((k - 1) * (k - 2)) < k * b := (Nat.mul_lt_mul_left hkpos).mpr hbase
        rw [← Nat.mul_assoc] at this; exact this
      have hjr := ProofsRecursion.j_rec_unfold_one (by omega) hbaseR
      -- `k*b - ℓ₀ = k*(b - M)`
      have hell0 : ell0 k = k * Mper k := ell0_eq_k_mul_Mper (by omega)
      have hsub : k * b - ell0 k = k * (b - Mper k) := by
        rw [hell0, ← Nat.mul_sub]
      -- value of `j k ℓ₀`
      have hell0_le : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [ell0]; omega
      have hell0_pos : 1 ≤ ell0 k := ProofsRecursion.ell0_pos (by omega)
      have hjbe : j k (ell0 k)
          = ell0 k + (ell0 k ⌈/⌉ k) + (ell0 k ⌈/⌉ (k * (k - 1))) - 3 :=
        j_base (Or.inl hell0_le)
      have hcd_ell0_k : ell0 k ⌈/⌉ k = Mper k := by
        rw [hell0, Proved.ceilDiv_of_dvd hkpos ⟨Mper k, rfl⟩, Nat.mul_div_cancel_left _ hkpos]
      have hcd_ell0_kk : ell0 k ⌈/⌉ (k * (k - 1)) = k - 2 := ProofsExcess.ceilDiv_ell0 (by omega)
      rw [hcd_ell0_k, hcd_ell0_kk] at hjbe
      -- IH at `b - M`
      have hIH := ih (b - Mper k) hbMlt hbM1
      rw [hsub] at hjr
      rw [hIH] at hjr
      -- block-scale recursion
      have hDshift : Dfr k b = Dfr k (b - Mper k) + (k - 2) := by
        have hlt : (k - 1) * (k - 2) < b := by omega
        rw [Dfr_shift_rec (by omega) hlt]
      -- assemble
      have hkMle : k * Mper k ≤ k * b := by
        rw [← hell0]; rw [ell0]; omega
      have hMle : Mper k ≤ b := by omega
      rw [hjr, hjbe, hDshift]
      have hell0v : ell0 k = k * Mper k := hell0
      -- everything is now linear in the atoms `Dfr k (b-M)`, `k*b`, `b`, `k`, `M`, `ell0`
      rw [hell0v]
      have h1 : k * (b - Mper k) = k * b - k * Mper k := by rw [Nat.mul_sub]
      rw [h1]
      have hkM : k * Mper k ≤ k * b := hkMle
      have hMb : Mper k ≤ b := hMle
      have hk2 : 2 ≤ k * Mper k := by
        have : 1 * 1 ≤ k * Mper k := Nat.mul_le_mul (by omega) (by omega)
        have := Nat.mul_le_mul (show 2 ≤ k by omega) (show 1 ≤ Mper k by omega); omega
      omega

/-! ## §2. The partial-excess ledger `PE`

`PE p t` is the excess spent through block `t` — the `ew − 2` edge-sum over the first `k·t`
vertices, a pure `ℕ` function of `p` and `t` (no prefix `HPath` reconstruction).  Its one-block step
(`PE_step`) is the sole excess-side fact the walk induction needs: the boundary into block `t+1`
adds its weight `bw p (t+1) − 2`. -/

/-- Partial excess through block `t`: the `ew − 2` sum over the first `k·t` vertices. -/
noncomputable def PE (p : HPath k) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k * t), (ew k (p.vert i) (p.vert (i + 1)) - 2)

@[simp] theorem PE_zero (p : HPath k) : PE p 0 = 0 := by simp [PE]

/-- **One-block excess step.**  The boundary into block `t+1` contributes at least `bw p (t+1) − 2`
to the partial excess: `PE p t + (bw p (t+1) − 2) ≤ PE p (t+1)`. -/
theorem PE_step (hk : 1 ≤ k) (p : HPath k) (t : ℕ) :
    PE p t + (bw p (t + 1) - 2) ≤ PE p (t + 1) := by
  set f : ℕ → ℕ := fun i => ew k (p.vert i) (p.vert (i + 1)) - 2 with hf
  have hexp : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
  have hpos : 1 ≤ k * (t + 1) := by
    have := Nat.mul_pos (show 0 < k by omega) (show 0 < t + 1 by omega); omega
  have hle : k * t ≤ k * (t + 1) := by omega
  have hsplit : PE p (t + 1) = PE p t + ∑ i ∈ Finset.Ico (k * t) (k * (t + 1)), f i := by
    simp only [PE, ← hf]
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le (k * t)) hle]
  -- the boundary edge index `k*(t+1) − 1` lies in `[k*t, k*(t+1))`
  have hidx : k * (t + 1) - 1 + 1 = k * (t + 1) := by omega
  have hmem : (k * (t + 1) - 1) ∈ Finset.Ico (k * t) (k * (t + 1)) := by
    rw [Finset.mem_Ico]; omega
  have hsingle : f (k * (t + 1) - 1) ≤ ∑ i ∈ Finset.Ico (k * t) (k * (t + 1)), f i :=
    Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hmem
  have hfval : f (k * (t + 1) - 1) = bw p (t + 1) - 2 := by
    simp only [hf, bw]; rw [hidx]
  rw [hsplit, ← hfval]; omega

/-- `PE p t ≤ excess p` whenever block `t` is within the path (`k·t < p.numVerts`): the partial
excess is a sub-sum of the full excess (all terms non-negative). -/
theorem PE_le_excess (hk : 1 ≤ k) {p : HPath k} (t : ℕ) (hN : k * t < p.numVerts) :
    PE p t ≤ excess p := by
  have hsub : Finset.range (k * t) ⊆ Finset.range (p.numVerts - 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  rw [ProofsMeta3.excess_eq_sum_edgeWeight hk p, PE]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-! ## §3. The per-block potential step

`walk_step` is the induction step: it classifies the boundary into block `t+1`
(`boundary_classify_ledger`) and maps each kind to its certificate inequality, threading the
`doorDepth`/`metaDepth` step equations.  It carries the two genuine bridge residuals as explicit
hypotheses (never `sorry`/axiom):

* `hj`, `hj'` — the **tightened run cap** `metaDepth ≤ k−3` at blocks `t`, `t+1`.  Only
  `metaDepth ≤ k−2` (`ProofsRunExtract.metaDepth_le`) is proved; the extra `−1` is essential —
  at `metaDepth = k−2` the potential collapses to `h ≡ 0`, which cannot absorb a jump-block door
  (`certificate.py` verifies the true cap is `k−3`).  *(residual G1)*
* `hmmc` — the **marker-move-from-complete exclusion** `¬(IsMarkerMove p (t+1) ∧ IsComplete p t)`.
  A cost-1 marker-move leaving a *complete* loop is the one boundary whose single-step inequality
  fails; `Hunter.Proved.fill_path` shows the opened slab stays incomplete for `k−2` blocks, a
  look-ahead absorption not expressible as a single step.  *(residual G2)*

Every other case is discharged outright by `door_ineq`/`alpha_ineq`/`heavy_ineq`/`reset_ineq`. -/

/-- **The per-block potential step.**  Under the run cap (`hj`/`hj'`) and the marker-move-from-complete
exclusion (`hmmc`), the boundary into block `t+1` moves the potential by no more than its excess
contribution `bw − 2`:
`Dfr(t+1) + h(state(t+1)) ≤ (bw p (t+1) − 2) + (Dfr(t) + h(state(t)))`. -/
theorem walk_step (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + 1) < p.numVerts)
    (hj : metaDepth p t ≤ k - 3) (hj' : metaDepth p (t + 1) ≤ k - 3)
    (hmmc : ¬ (IsMarkerMove p (t + 1) ∧ IsComplete p t)) :
    Dfr k (t + 1) + hpot k (doorDepth p (t + 1)) (metaDepth p (t + 1)) (t + 1)
      ≤ (bw p (t + 1) - 2) + (Dfr k t + hpot k (doorDepth p t) (metaDepth p t) t) := by
  have hk' : 3 ≤ k := by omega
  have hexp : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
  have hNt : k * t < p.numVerts := by omega
  have hd_le : doorDepth p t ≤ k - 2 := doorDepth_le_km2 hk' hp t hNt
  set d := doorDepth p t with hddef
  set jj := metaDepth p t with hjdef
  -- a non-door boundary has doorDepth (t+1) = 0
  have hnotdoor_dd : ¬ IsDoor p (t + 1) → doorDepth p (t + 1) = 0 := doorDepth_not_door
  rcases boundary_classify_ledger hk' hp (show 1 ≤ t + 1 by omega) hN with
    hdoor | hα | hσ | hmm | hheavy
  · -- DOOR (cost 0)
    have hbw : bw p (t + 1) = 2 := hdoor
    have hdd : doorDepth p (t + 1) = d + 1 := doorDepth_door hdoor
    have hmd : metaDepth p (t + 1) = jj := metaDepth_door hdoor
    have hdlt : d < k - 2 := by
      have h := doorDepth_le_km2 hk' hp (t + 1) hN; rw [hdd] at h; omega
    have hdi := door_ineq hk (show 1 ≤ t from ht) hdlt hj
    rw [hdd, hmd, hbw]; omega
  · -- ALPHA — split on completeness of the source loop
    have hbw : bw p (t + 1) = 3 := hα.1
    have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
    have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
    by_cases hc : IsComplete p t
    · -- α from complete → alpha_ineq (source (k−2, jj))
      have hdc : d = k - 2 := hc
      have hmd : metaDepth p (t + 1) = jj + 1 := metaDepth_alpha_complete hα hc
      have hjk4 : jj ≤ k - 4 := by rw [hmd] at hj'; omega
      have hai := alpha_ineq hk (show 1 ≤ t from ht) hjk4
      rw [hdd, hmd, hbw, hdc]; omega
    · -- α from incomplete → meta-heavy → reset_ineq (source incomplete d ≤ k−3)
      have hmh : IsMetaHeavy p (t + 1) := ⟨hnd, fun h => hc h.2⟩
      have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
      have hne : d ≠ k - 2 := hc
      have hd3 : d ≤ k - 3 := by omega
      have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
      rw [hdd, hmd, hbw]; omega
  · -- σ² → meta-heavy, incomplete source → reset_ineq
    have hbw : bw p (t + 1) = 3 := hσ.1
    have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
    have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
    have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isSigmaSq hk' hp hN hσ
    have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
    have hinc : ¬ IsComplete p t := by
      have := sigmaSq_incomplete_only hk' hp hN hσ
      rwa [show t + 1 - 1 = t from rfl] at this
    have hne : d ≠ k - 2 := hinc
    have hd3 : d ≤ k - 3 := by omega
    have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
    rw [hdd, hmd, hbw]; omega
  · -- MARKER-MOVE → meta-heavy; from-complete excluded by `hmmc`, else reset_ineq
    have hbw : bw p (t + 1) = 3 := hmm.1
    have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor, hbw]; omega
    have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
    have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isMarkerMove hmm
    have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
    have hinc : ¬ IsComplete p t := fun hc => hmmc ⟨hmm, hc⟩
    have hne : d ≠ k - 2 := hinc
    have hd3 : d ≤ k - 3 := by omega
    have hri := reset_ineq hk (show 1 ≤ t from ht) hd3 hj
    rw [hdd, hmd, hbw]; omega
  · -- HEAVY (cost ≥ 2) → heavy_ineq
    have hbw : 4 ≤ bw p (t + 1) := hheavy
    have hnd : ¬ IsDoor p (t + 1) := by rw [IsDoor]; omega
    have hdd : doorDepth p (t + 1) = 0 := hnotdoor_dd hnd
    have hmh : IsMetaHeavy p (t + 1) := metaHeavy_of_isHeavy hheavy
    have hmd : metaDepth p (t + 1) = 0 := metaDepth_metaHeavy hmh
    have hhi := heavy_ineq hk (show 1 ≤ t from ht) hd_le hj
    rw [hdd, hmd]; omega

/-! ## §4. The walk invariant and the block-scale excess bound

The invariant `Dfr(t) + h(state(t)) ≤ PE(t)` is preserved by every boundary (`walk_step`), with
`h ≥ 0` giving the clean corollary `excess p ≥ Dfr k T` at the last full block
`T = (numVerts − 1)/k`.  This is the block-scale frontier demand met by every exitless path — the
content the certificate delivers, under the two named residuals `hRunCap` (G1) and `hMMC` (G2).

Closing `M1WalkBound` on the nose needs one further step — the non-block-aligned **tail payment**
(G3): the frontier demand at the exact length `numVerts` can exceed `Dfr k T` by one, and that unit
is paid by a heavy edge inside the final partial block (`ProofsFinal.tight_window_pays`), an argument
not glued here.  So the capstones still carry `M1WalkBound`; see `PROGRESS-walk.md`. -/

/-- `Dfr k (Mper k) ≤ k − 3` — the demand at one period is below the base-window cap. -/
theorem Dfr_Mper_le (hk : 4 ≤ k) : Dfr k (Mper k) ≤ k - 3 := by
  have hle : Mper k ≤ (k - 1) * (k - 2) := by rw [Mper]; omega
  rw [Dfr_base hle]
  calc (Mper k - 1) / (k - 1) ≤ Mper k / (k - 1) := Nat.div_le_div_right (by omega)
    _ = k - 3 := Mper_div (by omega)

/-- The base value of the potential at the empty prefix: `h(0,0,0) = 0`. -/
theorem hpot_000 (hk : 4 ≤ k) : hpot k 0 0 0 = 0 := by
  have hW : Wpot k 0 0 = Mper k := by simp only [Wpot, Nat.sub_zero, Mper]
  have hDm := Dfr_Mper_le hk
  simp only [hpot, hW, Nat.zero_add, Dfr_zero, Nat.sub_zero]
  omega

/-- The potential vanishes on both block-1 states (`Dfr k 1 = 0`, the window lands at `≤ k−3`). -/
theorem hpot_block1 (hk : 4 ≤ k) (p : HPath k) : hpot k (doorDepth p 1) 0 1 = 0 := by
  have hk' : 3 ≤ k := by omega
  have hd1 : doorDepth p 1 ≤ 1 := doorDepth_le p 1
  have hP : 6 ≤ (k - 1) * (k - 2) := prod_ge hk
  have hWle : 1 + Wpot k (doorDepth p 1) 0 ≤ (k - 1) * (k - 2) := by
    have hWm : Wpot k (doorDepth p 1) 0 = (k - 1) * (k - 2) - 1 - doorDepth p 1 := by
      simp only [Wpot, Nat.sub_zero]
    rw [hWm]; omega
  have hDle : Dfr k (1 + Wpot k (doorDepth p 1) 0) ≤ k - 3 := by
    calc Dfr k (1 + Wpot k (doorDepth p 1) 0)
        ≤ Dfr k ((k - 1) * (k - 2)) := Dfr_mono hk hWle
      _ = k - 3 := by
          rw [Dfr_base (le_refl _)]
          exact Mper_div hk'
  have hval : hpot k (doorDepth p 1) 0 1
      = Dfr k (1 + Wpot k (doorDepth p 1) 0) - Dfr k 1 - (k - 3 - 0) := rfl
  rw [hval, Dfr_one hk']
  omega

/-- **The walk invariant.**  Under the tightened run cap (`hRunCap`, G1) and the
marker-move-from-complete exclusion (`hMMC`, G2), every block `t` within an exitless path satisfies
`Dfr k t + h(state(t)) ≤ PE p t`. -/
theorem walk_invariant (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hRunCap : ∀ s, k * s < p.numVerts → metaDepth p s ≤ k - 3)
    (hMMC : ∀ s, 1 ≤ s → k * (s + 1) < p.numVerts →
        ¬ (IsMarkerMove p (s + 1) ∧ IsComplete p s)) :
    ∀ t, k * t < p.numVerts →
      Dfr k t + hpot k (doorDepth p t) (metaDepth p t) t ≤ PE p t := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [PE_zero, doorDepth_zero, metaDepth_zero, Dfr_zero, hpot_000 hk]
  | succ t ih =>
    intro hN1
    have hexp : k * (t + 1) = k * t + k := by rw [Nat.mul_add, Nat.mul_one]
    have hNt : k * t < p.numVerts := by omega
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · -- base step: block 1
      subst ht0
      have hm1 : metaDepth p 1 = 0 := by
        have hnc : ¬ (IsAlpha p 1 ∧ IsComplete p 0) := by
          rintro ⟨_, hc⟩
          have hc' : doorDepth p 0 = k - 2 := hc
          rw [doorDepth_zero] at hc'; omega
        show (if IsAlpha p 1 ∧ IsComplete p 0 then metaDepth p 0 + 1
              else if IsMetaHeavy p 1 then 0 else metaDepth p 0) = 0
        rw [if_neg hnc]
        by_cases hmh : IsMetaHeavy p 1
        · rw [if_pos hmh]
        · rw [if_neg hmh]; rfl
      rw [hm1, hpot_block1 hk, Dfr_one (by omega)]
      exact Nat.zero_le _
    · -- inductive step: `t ≥ 1`, use walk_step
      have hstep := walk_step hk hp htpos hN1 (hRunCap t hNt) (hRunCap (t + 1) hN1)
        (hMMC t htpos hN1)
      have hpe := PE_step (by omega) p t
      have IHt := ih hNt
      omega

/-- **Block-scale frontier bound.**  Under `hRunCap` (G1) and `hMMC` (G2), every exitless path spends
excess at least the block-scale demand `Dfr k T` at the last full block `T = (numVerts − 1)/k`:
`Dfr k ((p.numVerts − 1)/k) ≤ excess p`.  This is the certificate's content, delivered at path
level. -/
theorem excess_ge_Dfr_block (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts)
    (hRunCap : ∀ s, k * s < p.numVerts → metaDepth p s ≤ k - 3)
    (hMMC : ∀ s, 1 ≤ s → k * (s + 1) < p.numVerts →
        ¬ (IsMarkerMove p (s + 1) ∧ IsComplete p s)) :
    Dfr k ((p.numVerts - 1) / k) ≤ excess p := by
  set T := (p.numVerts - 1) / k with hT
  have hkpos : 0 < k := by omega
  have hkT : k * T ≤ p.numVerts - 1 := by
    rw [hT, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hTN : k * T < p.numVerts := by omega
  have hinv := walk_invariant hk hp hRunCap hMMC T hTN
  have hple := PE_le_excess (by omega) T hTN
  omega

end ProofsWalk

end Hunter

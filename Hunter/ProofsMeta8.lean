/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta7

/-!
# Theorem 2 — the σ²-AS-PAYMENT run analysis (level ≥ 3 confinement, part V)

This file tests the queued **σ²-as-payment** idea against the final leaf of Theorem 2: the
`NonReleaseSupply k (PhiState k)` residual of `ProofsMeta7`.  The `ProofsMeta7` pass stalled
because `Proved.alpha_run_bound`'s `halpha` input demands each 2-loop terminator BE `alphaWord`,
whereas `ProofsMeta3.boundary_classify` only yields the dichotomy `alphaWord ∨ sigmaSqWord`.  The
idea: the σ²-sibling *already pays* (`ProofsMeta2.Vset3_of_sigmaSq_step`), so perhaps a run
analysis over marker-preserving weight-3 boundaries of EITHER kind goes through, dropping the
discrimination.

## What the analysis establishes (see `PROGRESS-meta8.md` for the full verdict)

The idea is **half right**:

* **Payment is discrimination-free** (`mixed_runs_pay`): a door pays `0`, and EVERY weight-3
  boundary — α, σ²-sibling, or marker-mover — pays exactly `ew − 2 = 1`.
* **σ² is a benign interior rotation step** (`rot_run_bound`): a door boundary rotates the
  meta-word by `1`, a σ²-boundary by `2` (`sigmaSqWord_erase_marker`); both preserve `Vset3`
  membership (`rotClass_erase_rotate`).  A run of consecutive blocks joined by door/σ² boundaries
  (any mix) keeps every block-start in ONE `Vset3` and so has `≤ (k−1)(k−2)` blocks — the
  door-vs-σ² discrimination is eliminated.

But the idea's central claim is **FALSE**: α and σ² are NOT interchangeable as 2-loop
*terminators*.  An α applies `door` on `k − 1` letters, which preserves the doubly-erased class
`Vset3` ONLY when applied at the aligned offset `w₀.rotate (k−2)` (a *complete* 2-loop).  A σ²
terminator rotates the meta-start by a net `+1`, misaligning it; a subsequent α then computes
`door` at the wrong offset and **ejects from the fixed `Vset3`**.  Concretely at `k = 5`,
`w₀ = [1,2,3,4]` (`α₂ = 4`, `K = rotClass [1,2,3]`): a σ²-then-α passage lands on
`door [1,2,3,4] = [3,4,2,1]`, whose `α₂`-erasure `[3,2,1]` has `rotClass ∉ K`.  So the
single-`Vset3` pigeonhole cannot bound a mixed-terminator run; the α-terminator's `= alphaWord`
characterization is a genuine lemma.  And the `ProofsMeta7` count arbiter
(`Refutations.windowExcess_false`: the window carries `k − 3`, the `+1` is amortized) is
untouched by σ².

Namespace `Hunter.ProofsMeta8`.  Zero `sorry`, zero new axioms.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta8

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
open ProofsMeta ProofsMeta2 ProofsMeta3 ProofsMeta4 Proved
open HPath

variable {k : ℕ}

/-! ## Step 1 — the σ²-sibling path-level steps (mirror of the α machinery)

`ProofsMeta` proves `metaWord_door_step` (door ⇒ meta-word `rotate 1`) and `metaWord_alpha_step`
(α ⇒ meta-word `door`), and `ProofsMeta4` lifts them to the fixed run-marker `α₁`
(`metaWord_door_block`, `metaWord_alpha_block`, `marker_door_step`, `marker_alpha_step`).  Here we
add the missing σ²-sibling steps: a σ²-boundary advances the meta-word by `rotate 2` and preserves
the marker — the direct analogues, built on `ProofsMeta.sigmaSqWord_erase_marker`/
`sigmaSqWord_marker`. -/

/-- **Meta-σ² step (dynamic marker).**  Across a σ²-sibling boundary (a weight-3 marker-preserving
edge landing on `sigmaSqWord`) the meta-word advances by `rotate 2` on `k − 1` letters — the
σ²-analogue of `metaWord_alpha_step` (which advances by `door`). -/
theorem metaWord_sigmaSq_step (hk : 3 ≤ k) {p : HPath k} {i : ℕ}
    (hσ : (p.vert (i + 1) : List ℕ) = sigmaSqWord (p.vert i)) :
    (p.vert (i + 1) : List ℕ).erase ((rho (p.vert i : List ℕ)).getLastD 0) =
      ((rho (p.vert i : List ℕ)).erase ((rho (p.vert i : List ℕ)).getLastD 0)).rotate 2 := by
  rw [hσ]; exact sigmaSqWord_erase_marker hk (p.vert i).2

/-- **Meta-σ² block step (fixed marker).**  Across a σ²-boundary into block `t`, if the previous
block-start's marker is `α₁`, the meta-word advances by `rotate 2` — stated with the fixed `α₁`
(mirror `metaWord_alpha_block`). -/
theorem metaWord_sigmaSq_block (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts)
    (hσ : (p.vert (k * t) : List ℕ) = sigmaSqWord (p.vert (k * t - 1)))
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).erase α₁ = ((p.vert (k * (t - 1)) : List ℕ).erase α₁).rotate 2 := by
  have hk1 : 1 ≤ k := by omega
  have hkt : 0 < k * t := Nat.mul_pos (by omega) (by omega)
  have hi1 : k * t - 1 + 1 = k * t := by omega
  have hrho := rho_boundary_prev hk1 hp ht (by omega : k * t ≤ p.numVerts)
  have hdyn : (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0 = α₁ := by rw [hrho]; exact hmk
  have hstep := metaWord_sigmaSq_step hk (p := p) (i := k * t - 1) (by rw [hi1]; exact hσ)
  rw [hi1, hdyn, hrho] at hstep
  exact hstep

/-- **σ² preserves the block marker.**  A σ²-sibling boundary into block `t` keeps the
block-start's last symbol equal to the previous block-start's (`= α₁`); marker-preservation is
σ²'s defining property (`sigmaSqWord_marker`), so this reduces to `marker_alpha_step`. -/
theorem marker_sigmaSq_step (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t ≤ p.numVerts)
    (hσ : (p.vert (k * t) : List ℕ) = sigmaSqWord (p.vert (k * t - 1)))
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).getLastD 0 = α₁ := by
  have hk1 : 1 ≤ k := by omega
  have hmark : (p.vert (k * t) : List ℕ).getLastD 0
      = (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0 := by
    rw [hσ]; exact sigmaSqWord_marker hk (p.vert (k * t - 1)).2
  exact marker_alpha_step hk1 hp ht hN hmark hmk

/-! ## Step 2 — the ROTATION-run confinement (the honest core of the mixed bound)

A door boundary rotates the meta-word by `1` and a σ²-boundary by `2`; both are *rotations*, so
both preserve `Vset3` membership (`rotClass_erase_rotate`).  Hence a run of consecutive blocks
joined by door/σ² boundaries — ANY mix of the two — keeps every block-start in ONE `Vset3`, and
the level-3 confinement budget (`card_le_of_mem_Vset3`) caps the run at `(k−1)(k−2)` blocks.  This
eliminates the door-vs-σ² discrimination and shows σ² is a benign interior step (it stays
confined and additionally pays 1).  It does NOT bound freely-mixed α/σ² *terminated* 2-loop runs
— an α after a σ² drifts out of the fixed `Vset3` (see the module verdict). -/

/-- **Self-membership.**  Every vertex lies in its own marked-3-loop (markers/class read off
itself).  The base case of the run confinement. -/
theorem mem_Vset3_self (A : Vtx k) :
    A ∈ Vset3 k ((A : List ℕ).getLastD 0) (((A : List ℕ).dropLast).getLastD 0)
      (rotClass ((A : List ℕ).dropLast.dropLast)) := by
  rw [mem_Vset3, erase_getLastD A.2.nodup,
    erase_getLastD ((List.dropLast_sublist _).nodup A.2.nodup)]

/-- **Abstract rotation confinement (pigeonhole).**  A family of `m` vertices all in one
`Vset3 k α₁ α₂ K` (markers/class from a base `A`) with pairwise-distinct 1-cycles has
`m ≤ (k−1)(k−2)`.  Direct `card_le_of_mem_Vset3`; the discrimination-free confinement budget
(no `α`-terminator structure needed — this is `meta_pigeonhole` without the `×(k−1)` split). -/
theorem rotStep_confined (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass} {A : Vtx k}
    (hα1 : α₁ = (A : List ℕ).getLastD 0)
    (hα2 : α₂ = ((A : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((A : List ℕ).dropLast.dropLast))
    {m : ℕ} (B : Fin m → Vtx k)
    (hmem : ∀ i, B i ∈ Vset3 k α₁ α₂ K)
    (hcyc : ∀ i i', i ≠ i' → rotClass (B i : List ℕ) ≠ rotClass (B i' : List ℕ)) :
    m ≤ (k - 1) * (k - 2) := by
  classical
  have hinj : Function.Injective B := fun i i' h => by
    by_contra hne; exact hcyc i i' hne (by rw [h])
  set S : Finset (Vtx k) := Finset.univ.image B with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmemS : ∀ v ∈ S, v ∈ Vset3 k α₁ α₂ K := by
    intro v hv; rw [hS, Finset.mem_image] at hv
    obtain ⟨i, _, rfl⟩ := hv; exact hmem i
  have hdisjS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      rotClass (u : List ℕ) ≠ rotClass (v : List ℕ) := by
    intro u hu v hv huv
    rw [hS, Finset.mem_image] at hu hv
    obtain ⟨i, _, rfl⟩ := hu; obtain ⟨i', _, rfl⟩ := hv
    exact hcyc i i' (fun h => huv (by rw [h]))
  have hcard := card_le_of_mem_Vset3 hk hα1 hα2 hK S hmemS hdisjS
  rwa [hScard] at hcard

/-- **Rotation-run bound (path level).**  A run of `m` consecutive blocks (`t₀, …, t₀+m−1`) whose
every interior boundary is marker-preserving and is EITHER a door (weight 2) OR a σ²-sibling
(`= sigmaSqWord`) — any mix of the two rotation-type weight-≤3 boundaries — has `m ≤ (k−1)(k−2)`.
Both boundary kinds rotate the meta-word (door by 1, σ² by 2), so every block-start stays in the
one `Vset3` read off the first block-start, and the level-3 pigeonhole caps the run. -/
theorem rot_run_bound (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m) ≤ p.numVerts)
    (hbdry : ∀ r, 1 ≤ r → r < m →
        ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2 ∨
        (p.vert (k * (t₀ + r)) : List ℕ) = sigmaSqWord (p.vert (k * (t₀ + r) - 1))) :
    m ≤ (k - 1) * (k - 2) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  set α₁ : ℕ := (p.vert (k * t₀) : List ℕ).getLastD 0 with hα1def
  set α₂ : ℕ := ((p.vert (k * t₀) : List ℕ).dropLast).getLastD 0 with hα2def
  set K : RotClass := rotClass ((p.vert (k * t₀) : List ℕ).dropLast.dropLast) with hKdef
  -- block positions of the run are strictly below numVerts
  have hposlt : ∀ r, r < m → k * (t₀ + r) < p.numVerts := by
    intro r hr
    have h1 : k * (t₀ + r) + k ≤ k * (t₀ + m) := by
      calc k * (t₀ + r) + k = k * (t₀ + r + 1) := by ring
        _ ≤ k * (t₀ + m) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  -- marker constancy along the run
  have hmkStart : ∀ r, r < m → (p.vert (k * (t₀ + r)) : List ℕ).getLastD 0 = α₁ := by
    intro r
    induction r with
    | zero => intro _; rw [Nat.add_zero]
    | succ r ih =>
      intro hr
      have hprev : (p.vert (k * (t₀ + r)) : List ℕ).getLastD 0 = α₁ := ih (by omega)
      have hmk : (p.vert (k * (t₀ + (r + 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega]; exact hprev
      rcases hbdry (r + 1) (by omega) hr with hdoor | hσ
      · exact marker_door_step hk2 hp (t := t₀ + (r + 1)) (by omega) (hposlt _ hr) hdoor hmk
      · exact marker_sigmaSq_step hk hp (t := t₀ + (r + 1)) (by omega)
          (le_of_lt (hposlt _ hr)) hσ hmk
  -- every block-start meta-word is a rotation of the first
  have hrot : ∀ r, r < m →
      ∃ s, (p.vert (k * (t₀ + r)) : List ℕ).erase α₁
        = ((p.vert (k * t₀) : List ℕ).erase α₁).rotate s := by
    intro r
    induction r with
    | zero => intro _; exact ⟨0, by rw [Nat.add_zero, List.rotate_zero]⟩
    | succ r ih =>
      intro hr
      obtain ⟨s, hs⟩ := ih (by omega)
      have hmk : (p.vert (k * (t₀ + r)) : List ℕ).getLastD 0 = α₁ := hmkStart r (by omega)
      have hmk' : (p.vert (k * (t₀ + (r + 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega]; exact hmk
      rcases hbdry (r + 1) (by omega) hr with hdoor | hσ
      · have hstep := metaWord_door_block hk2 hp (t := t₀ + (r + 1)) (by omega)
          (hposlt _ hr) hdoor hmk'
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega, hs, List.rotate_rotate] at hstep
        exact ⟨s + 1, hstep⟩
      · have hstep := metaWord_sigmaSq_block hk hp (t := t₀ + (r + 1)) (by omega)
          (hposlt _ hr) hσ hmk'
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega, hs, List.rotate_rotate] at hstep
        exact ⟨s + 2, hstep⟩
  -- membership in the one Vset3 read off the first block-start
  have hmem : ∀ i : Fin m, (fun i : Fin m => p.vert (k * (t₀ + (i : ℕ)))) i ∈ Vset3 k α₁ α₂ K := by
    intro i
    obtain ⟨s, hs⟩ := hrot i.1 i.2
    exact Vset3_of_metaWord_rotate_iter (A := p.vert (k * t₀))
      (by rw [hα1def, hα2def, hKdef]; exact mem_Vset3_self _) hs
  -- distinct 1-cycles via meta-no-reentry
  have hcyc : ∀ i i' : Fin m, i ≠ i' →
      rotClass ((fun i : Fin m => p.vert (k * (t₀ + (i : ℕ)))) i : List ℕ)
        ≠ rotClass ((fun i : Fin m => p.vert (k * (t₀ + (i : ℕ)))) i' : List ℕ) :=
    meta_no_reentry hk1 hp (fun i : Fin m => k * (t₀ + (i : ℕ)))
      (fun i => ⟨t₀ + (i : ℕ), rfl⟩)
      (fun i i' h => by
        have : (i : ℕ) < (i' : ℕ) := h
        calc k * (t₀ + (i : ℕ)) + k = k * (t₀ + (i : ℕ) + 1) := by ring
          _ ≤ k * (t₀ + (i' : ℕ)) := Nat.mul_le_mul (le_refl k) (by omega))
      (fun i => hposlt i.1 i.2)
  exact rotStep_confined hk (A := p.vert (k * t₀)) hα1def hα2def hKdef _ hmem hcyc

/-! ## The discrimination-free payment: every weight-3 boundary pays 1

The half of the σ²-as-payment idea that IS correct: the excess ledger term `ew − 2` of every
weight-3 boundary is `1`, regardless of whether it is an `α`, a σ²-sibling, or a marker-mover.
So the payment side never needs the α-vs-σ² discrimination. -/

/-- **Mixed payment.**  A door boundary pays `0`; EVERY weight-3 boundary (α, σ²-sibling, or
marker-mover) pays exactly `ew − 2 = 1`; a weight-`≥4` boundary pays `≥ 2`.  The payment table is
discrimination-free — restatement of `ProofsMeta3.boundary_contribution` emphasizing that the two
marker-preserving weight-3 shapes are on equal footing. -/
theorem mixed_runs_pay (_hk : 3 ≤ k) {p : HPath k} (_hp : p.Exitless) {i : ℕ}
    (_hi : i + 1 < p.numVerts) (_hd : k ∣ (i + 1))
    (hw3 : ew k (p.vert i) (p.vert (i + 1)) = 3) :
    ew k (p.vert i) (p.vert (i + 1)) - 2 = 1 := by
  omega

end ProofsMeta8

end Hunter

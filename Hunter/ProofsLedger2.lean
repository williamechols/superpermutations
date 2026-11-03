/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLedger

/-!
# Theorem 2 — the GLOBAL META-HEAVY COUNT (Wave 3, part L7/L8 of the no-lift ledger route)

This file is the meta analogue of `ProofsConfinement.cover_bound` / `ProofsMeta6.window_heavy_count`,
one level up: instead of counting **weight-≥3 boundaries** (non-doors) inside `(k−1)`-block windows,
it counts **meta-heavy boundaries** (`ProofsLedger.IsMetaHeavy`) inside the much larger meta-windows.

## The counting engine (`runLen_eq`)

The whole count rests on one *unconditional, hypothesis-free* structural identity of the ledger:

    runStart p t + metaDepth p t * (k − 1) + doorDepth p t = t                    (`runLen_eq`)

i.e. the number of blocks since the last meta-heavy (`t − runStart p t`) is exactly
`metaDepth · (k−1) + doorDepth`.  Proof: induction on `t`, three cases (door / complete-α /
meta-heavy) using only the pure step equations of `ProofsLedger` — no path hypotheses at all.

Combined with the two pointwise caps

  * `doorDepth p t ≤ k − 2`   (`doorDepth_le_km2`, proved here from `ProofsConfinement.confinement`
    — no `k−1` consecutive doors),
  * `metaDepth p t ≤ k − 2`   (the Wave-2 unconditional `metaDepth_le`; taken here as an explicit
    hypothesis `hmd`, see the note below),

`runLen_eq` bounds the block-span since the last meta-heavy by `(k−2)(k−1)+(k−2) = k(k−2)`.  Hence
**every window of `k(k−2)+1` consecutive blocks contains a meta-heavy**, and `cover_bound`
(applied to the meta-heavy finset) gives the global count `metaHeavy_count_ge` (L7).

## Note on the window constant `k(k−2)+1` vs architect-B's `(k−1)(k−2)`

architect-B's DESIGN quotes a span `≤ (k−1)(k−2)` between meta-heavies.  That value is only correct
under the *observed* cap `metaDepth ≤ k−3` (the ℓ=120 witness ejects at `metaDepth = k−3`).  The
**proved** cap is `metaDepth ≤ k−2` (`ProofsRunExtract.metaDepth_le` / `metaDepth_le_of_run`), and
with the honest pair `metaDepth ≤ k−2`, `doorDepth ≤ k−2` the sound span bound is `k(k−2)`, giving
the window constant `k(k−2)+1`.  We prove the sound form; see PROGRESS-ledger2.md for the
double-count analysis showing why the *looser* constant costs nothing at the counting level (the
meta-count is subsumed by the `k−3` floor either way — the residual `+1` never comes from counting
more meta-heavies).

## Note on the `hmd` hypothesis

The Wave-2 file `Hunter/ProofsRunExtract.lean` (concurrent) provides the unconditional
`metaDepth p t ≤ k − 2`.  Per the campaign rules we do **not** import that in-progress file; the
meta-depth cap enters `metaHeavy_count_ge` as the named hypothesis
`hmd : ∀ t, k * t < p.numVerts → metaDepth p t ≤ k − 2`, which `ProofsRunExtract.metaDepth_le`
discharges with a one-liner once it is stable.

Namespace `Hunter.ProofsLedger2`.  Everything is sorry-free and axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsLedger2

open ProofsConfinement ProofsLedger
open HPath

variable {k : ℕ}

/-! ## §1. The run-length identity and the two pointwise caps -/

/-- `runStart` never exceeds the block index. -/
theorem runStart_le (p : HPath k) (t : ℕ) : runStart p t ≤ t := by
  induction t with
  | zero => simp [runStart_zero]
  | succ t ih =>
    by_cases h : IsMetaHeavy p (t + 1)
    · rw [runStart_metaHeavy h]
    · rw [runStart_not_metaHeavy h]; omega

/-- **The run-length identity** (unconditional, hypothesis-free).  The number of blocks since the
last meta-heavy equals `metaDepth · (k−1) + doorDepth`:

    runStart p t + metaDepth p t * (k − 1) + doorDepth p t = t.

Induction on `t`, three exhaustive cases keyed on the boundary into block `t+1`:
door (carry meta, +1 door), complete-α (+1 meta, reset door), meta-heavy (reset all). -/
theorem runLen_eq (hk : 3 ≤ k) (p : HPath k) (t : ℕ) :
    runStart p t + metaDepth p t * (k - 1) + doorDepth p t = t := by
  induction t with
  | zero => simp [runStart_zero, metaDepth_zero]
  | succ t ih =>
    by_cases hdoor : IsDoor p (t + 1)
    · -- door: metaDepth carries, doorDepth +1, runStart carries
      have hnmh : ¬ IsMetaHeavy p (t + 1) := fun hmh => hmh.1 hdoor
      rw [doorDepth_door hdoor, metaDepth_door hdoor, runStart_not_metaHeavy hnmh]
      omega
    · by_cases hac : IsAlpha p (t + 1) ∧ IsComplete p t
      · -- complete-α: metaDepth +1, doorDepth 0, runStart carries
        have hnmh : ¬ IsMetaHeavy p (t + 1) := fun hmh => hmh.2 hac
        have hcomp : doorDepth p t = k - 2 := hac.2
        have hdd : doorDepth p (t + 1) = 0 := doorDepth_not_door hdoor
        have hmd : metaDepth p (t + 1) = metaDepth p t + 1 :=
          metaDepth_alpha_complete hac.1 hac.2
        have hrs : runStart p (t + 1) = runStart p t := runStart_not_metaHeavy hnmh
        rw [hdd, hmd, hrs]
        have hexp : (metaDepth p t + 1) * (k - 1) = metaDepth p t * (k - 1) + (k - 1) := by ring
        rw [hexp]
        -- from ih: runStart + metaDepth*(k-1) + (k-2) = t, and (k-1) = (k-2)+1
        have hk1 : k - 1 = (k - 2) + 1 := by omega
        rw [hcomp] at ih
        omega
      · -- meta-heavy: everything resets
        have hmh : IsMetaHeavy p (t + 1) := ⟨hdoor, hac⟩
        rw [doorDepth_not_door hdoor, metaDepth_metaHeavy hmh, runStart_metaHeavy hmh]
        simp

/-- **No `k−1` consecutive doors ⇒ `doorDepth ≤ k − 2`.**  From `ProofsConfinement.confinement`:
if `doorDepth p t ≥ k − 1`, then blocks `t−(k−2) … t` all carry door boundaries (`k − 1` of them),
contradicting confinement. -/
theorem doorDepth_le_km2 (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t < p.numVerts) : doorDepth p t ≤ k - 2 := by
  by_contra hcon           -- hcon : ¬ doorDepth p t ≤ k - 2, i.e. k - 1 ≤ doorDepth p t
  have hdle := doorDepth_le p t
  have htk1 : k - 1 ≤ t := by omega
  refine confinement (by omega : 2 ≤ k) hp (t₀ := t - (k - 1)) ?_ ?_
  · -- k * ((t - (k-1)) + k - 1) < numVerts, i.e. k * t < numVerts
    have : (t - (k - 1)) + k - 1 = t := by omega
    rw [this]; exact hN
  · intro s hs1 hs2
    -- s ∈ (t-(k-1), t], set j = t - s ∈ [0, k-2], j < doorDepth p t
    have hjlt : t - s < doorDepth p t := by omega
    have hdr := isDoor_of_lt_doorDepth p t (t - s) hjlt
    have hidx : t - (t - s) = s := by omega
    rw [hidx, IsDoor, bw] at hdr
    exact hdr

/-- **`runStart` is constant across a meta-heavy-free stretch.**  If no block in `(u₀, u₀+e]` is
meta-heavy, then `runStart p (u₀ + e) = runStart p u₀`. -/
theorem runStart_const (p : HPath k) (u₀ : ℕ) :
    ∀ e, (∀ s, u₀ < s → s ≤ u₀ + e → ¬ IsMetaHeavy p s) → runStart p (u₀ + e) = runStart p u₀ := by
  intro e
  induction e with
  | zero => intro _; rfl
  | succ e ih =>
    intro hno
    have hnmh : ¬ IsMetaHeavy p (u₀ + (e + 1)) := hno (u₀ + (e + 1)) (by omega) (by omega)
    have hstep : runStart p (u₀ + (e + 1)) = runStart p (u₀ + e) := by
      have he : u₀ + (e + 1) = (u₀ + e) + 1 := by omega
      rw [he, runStart_not_metaHeavy (by rw [← he]; exact hnmh)]
    rw [hstep]
    exact ih (fun s hs1 hs2 => hno s hs1 (by omega))

/-! ## §2. The global meta-heavy count (L7) — the meta analogue of `cover_bound`

`metaHeavyCount p a M` = number of meta-heavy boundaries among the `M` blocks `a+1 … a+M`.
`metaHeavy_count_ge` (L7): every window of `k(k−2)+1` consecutive blocks contains a meta-heavy
(by `runLen_eq` + the two caps), so `cover_bound` gives the global lower bound one level up. -/

/-- **Meta-heavy count.**  The number of meta-heavy boundaries among blocks `a+1 … a+M`. -/
noncomputable def metaHeavyCount (p : HPath k) (a M : ℕ) : ℕ :=
  ((Finset.Icc 1 M).filter (fun j => IsMetaHeavy p (a + j))).card

/-- **L7 — the global meta-heavy count.**  For an exitless `p` whose meta-depth is capped
(`hmd`, the Wave-2 unconditional `metaDepth_le`), among any `M` consecutive block boundaries
`a+1 … a+M` (all below `numVerts`) at least `M ⌈/⌉ (k(k−2)+1) − 1` are meta-heavy.

The meta analogue of `ProofsMeta6.window_heavy_count`: `cover_bound` applied to the meta-heavy
finset, with the window constant `d = k(k−2)+1`.  The window condition — no `d` consecutive
blocks are all non-meta-heavy — is exactly `runLen_eq` (`t − runStart = metaDepth·(k−1)+doorDepth`)
capped by `metaDepth ≤ k−2` (`hmd`) and `doorDepth ≤ k−2` (`doorDepth_le_km2`):
`metaDepth·(k−1)+doorDepth ≤ (k−2)(k−1)+(k−2) = k(k−2) < d`. -/
theorem metaHeavy_count_ge (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hmd : ∀ t, k * t < p.numVerts → metaDepth p t ≤ k - 2)
    (a M : ℕ) (hM : k * (a + M) < p.numVerts) :
    M ⌈/⌉ (k * (k - 2) + 1) - 1 ≤ metaHeavyCount p a M := by
  unfold metaHeavyCount
  refine cover_bound (d := k * (k - 2) + 1) (T := M) (by omega) _ ?_
  intro b hb1 hbd
  by_contra hcon
  -- no meta-heavy at any block a+j with j ∈ [b, b+d-1]
  have hno : ∀ s, a + b ≤ s → s ≤ a + (b + (k * (k - 2) + 1) - 1) → ¬ IsMetaHeavy p s := by
    intro s hs1 hs2 hmh
    refine hcon ⟨s - a, ?_, by omega, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hsa : a + (s - a) = s := by omega
    rw [hsa]; exact hmh
  set t := a + (b + (k * (k - 2) + 1) - 1) with ht
  -- t is in range
  have htrange : k * t < p.numVerts := by
    have htlt : t + 1 ≤ a + M := by omega
    have hkey : k * t + k ≤ k * (a + M) := by
      calc k * t + k = k * (t + 1) := by ring
        _ ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) htlt
    omega
  have hmdt : metaDepth p t ≤ k - 2 := hmd t htrange
  have hddt : doorDepth p t ≤ k - 2 := doorDepth_le_km2 hk hp t htrange
  -- runStart constant across the meta-heavy-free stretch
  have hrs : runStart p t = runStart p (a + b - 1) := by
    rw [ht, show a + (b + (k * (k - 2) + 1) - 1) = (a + b - 1) + (k * (k - 2) + 1) from by omega]
    exact runStart_const p (a + b - 1) (k * (k - 2) + 1)
      (fun s hs1 hs2 => hno s (by omega) (by omega))
  have hrsle : runStart p (a + b - 1) ≤ a + b - 1 := runStart_le p (a + b - 1)
  -- the run-length identity and the arithmetic collapse
  have hlen := runLen_eq hk p t
  have hmul : metaDepth p t * (k - 1) ≤ (k - 2) * (k - 1) := Nat.mul_le_mul_right _ hmdt
  have hQ1 : (k - 2) * (k - 1) + (k - 2) = k * (k - 2) := by
    have hk1 : (k - 1) + 1 = k := by omega
    calc (k - 2) * (k - 1) + (k - 2) = (k - 2) * ((k - 1) + 1) := by ring
      _ = (k - 2) * k := by rw [hk1]
      _ = k * (k - 2) := by ring
  omega

/-! ## §3. The double-count resolution — the meta-count is SUBSUMED by the `k−3` floor

The honest accounting question (RULING §1a, DESIGN §2c): does `metaHeavy_count_ge` deliver excess
*above* the `k−3` floor `ProofsMeta6.windowExcess_ge_km3` already counts?  The answer proved here is
**no, at the counting level it collapses to the floor**.  Every meta-heavy boundary is one of the
*same* weight-≥3 boundaries the floor counts (`metaHeavy_imp_weight3`), and over any block range the
meta-heavy finset is a **subset** of the weight-≥3 finset that `window_heavy_count` lower-bounds
(`metaHeavyCount_le_weight3`).  Because the meta-cover (`d = k(k−2)+1`) is far coarser than the
floor-cover (`d = k−1`), the meta-count is strictly weaker on that same set — it never forces an
*extra* weight-≥3 edge.  So the residual `+1` (excess `k−2` vs floor `k−3`) is realised only by
(a) a weight-≥4 meta-heavy paying `2` instead of `1` [ℓ=110,115,120: one weight-4], or (b) an
**incomplete** door-run producing an extra weight-3 boundary beyond the floor [ℓ=101: no weight-4].
Neither is delivered by the count; both are the L8 / σ-frame content.  This is the (MF) gap made
exact at the counting level. -/

/-- **Every meta-heavy boundary is weight-≥3.**  `IsMetaHeavy` requires `¬ IsDoor` (`bw ≠ 2`) and
every block boundary has `bw ≥ 2` (`ProofsWindow.boundary_ge_two`), so `bw ≥ 3`.  This is the
double-count fact: a meta-heavy is one of the same weight-≥3 edges the `k−3` floor already counts. -/
theorem metaHeavy_imp_weight3 (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts) (h : IsMetaHeavy p t) : 3 ≤ bw p t := by
  have hkt : 1 ≤ k * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hi1 : k * t - 1 + 1 = k * t := by omega
  have hin : (k * t - 1) + 1 < p.numVerts := by rw [hi1]; exact hN
  have hd : k ∣ ((k * t - 1) + 1) := by rw [hi1]; exact ⟨t, rfl⟩
  have hge2 := ProofsWindow.boundary_ge_two (by omega : 1 ≤ k) hp hin hd
  rw [hi1] at hge2
  have hnd := h.1
  rw [IsDoor, bw] at hnd
  rw [bw]; omega

/-- **The meta-count is a subcount of the floor's weight-≥3 set.**  Over blocks `a+1 … a+M`,
`metaHeavyCount p a M ≤` the weight-≥3 boundary count — the *identical* finset that
`ProofsMeta6.window_heavy_count` lower-bounds by `M ⌈/⌉ (k−1) − 1 = k−3`.  Hence L7 provides no
weight-≥3 edge beyond the floor; the meta-heavies ARE (a subset of) the floor's counted edges. -/
theorem metaHeavyCount_le_weight3 (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (a M : ℕ) (hM : k * (a + M) < p.numVerts) :
    metaHeavyCount p a M ≤
      ((Finset.Icc 1 M).filter
        (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))).card := by
  unfold metaHeavyCount
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
  obtain ⟨⟨hj1, hjM⟩, hmh⟩ := hj
  refine ⟨⟨hj1, hjM⟩, ?_⟩
  have hN' : k * (a + j) < p.numVerts := by
    have : k * (a + j) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  have hw := metaHeavy_imp_weight3 hk hp (by omega : 1 ≤ a + j) hN' hmh
  rw [bw] at hw; exact hw

/-! ## §4. L8 — an incomplete-loop ejection makes the `k−3` floor slack (`window_incomplete_slack`)

**Numeric verdict (settled before formalizing).**  The `k−3` floor `M ⌈/⌉ (k−1) − 1 = k−3`
(`ProofsMeta6.window_heavy_count`, `M = (k−1)(k−2)−1`) is *tight only* when the window is perfectly
saturated: `k−2` maximal door-runs each of length exactly `k−2`.  ANY door-run of length `< k−2`
inside the window (an incomplete-loop ejection) forces the weight-≥3 (non-door) count `W ≥ k−2`.
This is **alignment-free** — it does not depend on the `ℓ mod ℓ₀` phase.  (The phase only afflicts a
`cover_bound`-style proof, whose `(h−1)/(k−1)` pigeonholes ARE phase-sensitive; the truth is not.)

**The telescoping engine.**  Track `doorDepth` across the window `(a, a+e]`.  Writing
`dCount` = #doors and `rSum` = Σ over non-door steps of `doorDepth` just before the ejection, the
`doorDepth` recursion telescopes exactly:

    doorDepth p a + dCount = doorDepth p (a+e) + rSum                               (`doorTele`)

Each ejection's `doorDepth`-before is `≤ k−2` (`doorDepth_le_km2`, confinement); an **incomplete**
ejection has it `≤ k−3`, saving `1`, so `rSum + 1 ≤ (nonDoors)·(k−2)` (`rSum_le_strong`).  Feeding
this and `doorDepth p (a+e) ≤ k−2` into `doorTele` at `e = (k−1)(k−2)−1` gives `W·(k−1) ≥ (k−2)²`,
hence `W ≥ k−2`.

Relation to the (MF) residual: this closes the *counting* content of the "no-weight-4 face"
(ℓ=101) — the extra weight-3 edge is real and forced.  What it does NOT do is prove "the slack IS
σ": tying the extra edge to the σ-frame's demand across windows is the L9/L10 obligation and is not
attempted here (see PROGRESS-ledger2.md). -/

/-- Number of **door** boundaries among blocks `a+1 … a+e`. -/
noncomputable def dCount (p : HPath k) (a : ℕ) : ℕ → ℕ
  | 0     => 0
  | e + 1 => dCount p a e + (if IsDoor p (a + (e + 1)) then 1 else 0)

/-- Sum, over the **non-door** (ejection) boundaries among blocks `a+1 … a+e`, of the door-run
depth just before the ejection (`doorDepth` at the previous block). -/
noncomputable def rSum (p : HPath k) (a : ℕ) : ℕ → ℕ
  | 0     => 0
  | e + 1 => rSum p a e + (if IsDoor p (a + (e + 1)) then 0 else doorDepth p (a + e))

theorem dCount_le (p : HPath k) (a e : ℕ) : dCount p a e ≤ e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [dCount]; split <;> omega

/-- **The door telescope.**  `doorDepth p a + dCount = doorDepth p (a+e) + rSum`, by induction on
the window length using only `doorDepth_door` / `doorDepth_not_door`. -/
theorem doorTele (p : HPath k) (a e : ℕ) :
    doorDepth p a + dCount p a e = doorDepth p (a + e) + rSum p a e := by
  induction e with
  | zero => simp [dCount, rSum]
  | succ e ih =>
    by_cases h : IsDoor p (a + (e + 1))
    · have hdd : doorDepth p (a + (e + 1)) = doorDepth p (a + e) + 1 := doorDepth_door h
      rw [dCount, rSum, if_pos h, if_pos h, hdd]; omega
    · have hdd : doorDepth p (a + (e + 1)) = 0 := doorDepth_not_door h
      rw [dCount, rSum, if_neg h, if_neg h, hdd]; omega

/-- **Plain reset-sum bound.**  Every ejection's door-run depth is `≤ k−2` (confinement), so the
reset sum is `≤ (#non-doors)·(k−2)`. -/
theorem rSum_le (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (a M : ℕ)
    (hM : k * (a + M) < p.numVerts) :
    ∀ e, e ≤ M → rSum p a e ≤ (e - dCount p a e) * (k - 2) := by
  intro e
  induction e with
  | zero => intro _; simp [rSum, dCount]
  | succ e ih =>
    intro heM
    have ihe := ih (by omega)
    have hdle := dCount_le p a e
    by_cases h : IsDoor p (a + (e + 1))
    · rw [rSum, dCount, if_pos h, if_pos h]
      have hR : ((e + 1) - (dCount p a e + 1)) * (k - 2) = (e - dCount p a e) * (k - 2) := by
        congr 1; omega
      omega
    · rw [rSum, dCount, if_neg h, if_neg h]
      simp only [Nat.add_zero]
      have hrange : k * (a + e) < p.numVerts := by
        have : k * (a + e) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
        omega
      have hdd : doorDepth p (a + e) ≤ k - 2 := doorDepth_le_km2 hk hp (a + e) hrange
      have hR : ((e + 1) - dCount p a e) * (k - 2)
          = (e - dCount p a e) * (k - 2) + (k - 2) := by
        rw [show (e + 1) - dCount p a e = (e - dCount p a e) + 1 from by omega]; ring
      omega

/-- **Strengthened reset-sum bound.**  If any ejection among blocks `a+1 … a+e` is *incomplete*
(door-run depth `≤ k−3`), the reset sum is `≤ (#non-doors)·(k−2) − 1`. -/
theorem rSum_le_strong (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (a M : ℕ)
    (hM : k * (a + M) < p.numVerts) :
    ∀ e, e ≤ M → (∃ s, 1 ≤ s ∧ s ≤ e ∧ ¬ IsDoor p (a + s) ∧ doorDepth p (a + s - 1) ≤ k - 3) →
      rSum p a e + 1 ≤ (e - dCount p a e) * (k - 2) := by
  intro e
  induction e with
  | zero => intro _ ⟨s, hs1, hs2, _⟩; omega
  | succ e ih =>
    intro heM ⟨s, hs1, hs2, hsnd, hsinc⟩
    have hdle := dCount_le p a e
    have hrange : k * (a + e) < p.numVerts := by
      have : k * (a + e) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
      omega
    have hdd : doorDepth p (a + e) ≤ k - 2 := doorDepth_le_km2 hk hp (a + e) hrange
    by_cases h : IsDoor p (a + (e + 1))
    · -- door step: the incomplete witness must be ≤ e
      have hsle : s ≤ e := by
        rcases hs2.lt_or_eq with hlt | heq
        · omega
        · rw [heq] at hsnd; exact absurd h hsnd
      have ihe := ih (by omega) ⟨s, hs1, hsle, hsnd, hsinc⟩
      rw [rSum, dCount, if_pos h, if_pos h]
      have hR : ((e + 1) - (dCount p a e + 1)) * (k - 2) = (e - dCount p a e) * (k - 2) := by
        congr 1; omega
      omega
    · rw [rSum, dCount, if_neg h, if_neg h]
      simp only [Nat.add_zero]
      have hR : ((e + 1) - dCount p a e) * (k - 2)
          = (e - dCount p a e) * (k - 2) + (k - 2) := by
        rw [show (e + 1) - dCount p a e = (e - dCount p a e) + 1 from by omega]; ring
      by_cases hs_top : s = e + 1
      · -- the incomplete ejection is the current step: door-run depth ≤ k-3, save 1
        have hplain := rSum_le hk hp a M hM e (by omega)
        have hddinc : doorDepth p (a + e) ≤ k - 3 := by
          have hidx : a + s - 1 = a + e := by omega
          rw [hidx] at hsinc; exact hsinc
        omega
      · -- witness earlier: use IH for the +1, current step contributes ≤ k-2
        have ihe := ih (by omega) ⟨s, hs1, by omega, hsnd, hsinc⟩
        omega

/-- **`dCount` counts the door boundaries.** -/
theorem dCount_eq_card (p : HPath k) (a e : ℕ) :
    dCount p a e = ((Finset.Icc 1 e).filter (fun j => IsDoor p (a + j))).card := by
  induction e with
  | zero => simp [dCount]
  | succ e ih =>
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ e + 1),
        ← Finset.card_filter, dCount, ih]

/-- **L8 — an incomplete-loop ejection forces `k−2` weight-≥3 edges in the window.**  For an
exitless `p` and the `M = (k−1)(k−2)−1`-block window `(a, a+M]`, if some ejection `s₀` in the
window leaves an *incomplete* door-run (`doorDepth p (a+s₀−1) ≤ k−3`), then the window carries at
least `k−2` weight-≥3 boundaries — one MORE than the unconditional `k−3` floor.  This is the exact
counting content of the "no-weight-4 face"; it is unconditional (phase-free). -/
theorem window_incomplete_slack (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (a : ℕ)
    (hM : k * (a + ((k - 1) * (k - 2) - 1)) < p.numVerts)
    (s₀ : ℕ) (hs01 : 1 ≤ s₀) (hs02 : s₀ ≤ (k - 1) * (k - 2) - 1)
    (hnd : ¬ IsDoor p (a + s₀)) (hinc : doorDepth p (a + s₀ - 1) ≤ k - 3) :
    k - 2 ≤ ((Finset.Icc 1 ((k - 1) * (k - 2) - 1)).filter
        (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))).card := by
  set M := (k - 1) * (k - 2) - 1 with hMdef
  -- W = number of non-door boundaries in the window
  set W := M - dCount p a M with hWdef
  have hdle := dCount_le p a M
  -- the telescope, the strong reset bound, and the final-block cap
  have htele := doorTele p a M
  have hstrong := rSum_le_strong hk hp a M hM M (le_refl M) ⟨s₀, hs01, hs02, hnd, hinc⟩
  rw [← hWdef] at hstrong                       -- rSum p a M + 1 ≤ W * (k - 2)
  have hfin : doorDepth p (a + M) ≤ k - 2 := doorDepth_le_km2 hk hp (a + M) hM
  -- W ≥ k - 2 by the arithmetic collapse
  have hWk : k - 2 ≤ W := by
    have hdc : dCount p a M + W = M := by omega
    have hWid : W * (k - 2) + W = W * (k - 1) := by
      rw [show k - 1 = (k - 2) + 1 from by omega]; ring
    -- chain (atoms W*(k-2), W*(k-1)):  M ≤ W*(k-1) + (k-3)
    have hchain : M ≤ W * (k - 1) + (k - 3) := by omega
    -- M + 1 = (k-1)*(k-2)
    have hprodpos : 1 ≤ (k - 1) * (k - 2) := by
      calc 1 = 1 * 1 := by ring
        _ ≤ (k - 1) * (k - 2) := Nat.mul_le_mul (by omega) (by omega)
    have hM1 : M + 1 = (k - 1) * (k - 2) := by rw [hMdef]; omega
    -- (k-1)*(k-2) = (k-3)*(k-1) + (k-1)
    have hAid : (k - 1) * (k - 2) = (k - 3) * (k - 1) + (k - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, k - 3 = m := ⟨k - 3, rfl⟩
      have e1 : k - 1 = m + 2 := by omega
      have e2 : k - 2 = m + 1 := by omega
      rw [e1, e2, hm]; ring
    by_contra hlt
    have hWle : W ≤ k - 3 := by omega
    have hWmul : W * (k - 1) ≤ (k - 3) * (k - 1) := Nat.mul_le_mul_right _ hWle
    omega
  -- convert W (non-door count) into the weight-≥3 count
  have hWcard : W = ((Finset.Icc 1 M).filter (fun j => ¬ IsDoor p (a + j))).card := by
    have hdcard := dCount_eq_card p a M
    have hpart : ((Finset.Icc 1 M).filter (fun j => IsDoor p (a + j))).card
        + ((Finset.Icc 1 M).filter (fun j => ¬ IsDoor p (a + j))).card = M := by
      rw [Finset.card_filter_add_card_filter_not, Nat.card_Icc]; omega
    rw [hWdef, hdcard]; omega
  rw [hWcard] at hWk
  refine le_trans hWk (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
  obtain ⟨⟨hj1, hjM⟩, hjnd⟩ := hj
  refine ⟨⟨hj1, hjM⟩, ?_⟩
  have hN' : k * (a + j) < p.numVerts := by
    have : k * (a + j) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  have hkt : 1 ≤ k * (a + j) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hi1 : k * (a + j) - 1 + 1 = k * (a + j) := by omega
  have hin : (k * (a + j) - 1) + 1 < p.numVerts := by rw [hi1]; exact hN'
  have hd : k ∣ ((k * (a + j) - 1) + 1) := by rw [hi1]; exact ⟨a + j, rfl⟩
  have hge2 := ProofsWindow.boundary_ge_two (by omega : 1 ≤ k) hp hin hd
  rw [hi1] at hge2
  rw [IsDoor, bw] at hjnd
  omega

end ProofsLedger2

end Hunter

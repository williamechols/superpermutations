/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsFinale
import Hunter.ProofsMeta6
import Hunter.ProofsConfinement

/-!
# Hunter Theorem 2 — LINK (1): the run-coordinate weight profile (`Hunter/ProofsProfile.lean`)

This module is the *counting* half of the endgame: it turns a **low front-excess** hypothesis
(the total boundary excess `Σ (bw − 2)` over the first `N = (k−1)(k−2)` block boundaries is at
most `k − 3 = m + 1`) into the **exact chart weight profile** consumed by
`Hunter.ProofsFinale.hpath_chart_heavy`:

* every within-run boundary has weight `2`  (`hbw2`);
* the `k − 3` run boundaries land **exactly** at chart coordinates `j·(k−1) + (k−2) + 1`, each of
  weight `3`  (`hbw3`).

The route is the `PROOF_S2 §2` zero-slack pigeonhole:
`excess = Σ (bw − 2)` over the window boundaries; the confinement floor forces at least `k − 3`
weight-`≥3` boundaries; low front-excess pins that count to exactly `k − 3`, each of weight exactly
`3`; then `runlen_pigeonhole` forces the `k − 2` maximal weight-2 runs to each have the full length
`k − 1`, which pins the weight-3 boundaries at `j·(k−1)`.

Namespace `Hunter.ProofsProfile`.  **Zero `sorry`, zero new axioms.**

## k = 5 calibration (`m = 1`, `k = m + 4 = 5`, `n = k−1 = 4`, `r = k−2 = 3`, `N = n·r = 12`)

The window boundary indices are `t = 1 .. N−1 = 1 .. 11`.  The completed deterministic chart has
its `k − 3 = 2` internal weight-3 boundaries at ledger indices `t = (j+1)·n = 4, 8` (`j < r−1 = 2`),
all other boundaries `t ∈ {1,2,3,5,6,7,9,10,11}` weight `2`.  In `m + 4 = 5` coordinates:

* `hbw3 j (hj : j < m + 1 = 1)`: only `j = 0`, index `0·4 + 3 + 1 = 4`.  ✓ matches `t = 4`.
* `hbw2 j i (j ≤ m+1 = 2) (i < m+2 = 3)`: indices `j·4 + i + 1`.
    `j=0`: `1,2,3`; `j=1`: `5,6,7`; `j=2`: `9,10,11`.  ✓ matches the weight-2 set.

(`t = 12 = N` is the fresh continuation boundary, proved `≥ 4` by `hpath_chart_heavy`, not part of
this profile.)  The `r − 1 = 2` positive cuts `{4, 8}` partition `[0, 12]` into `r = 3` maximal
door runs each of length `n = 4`, exactly the `runlen_pigeonhole` collapse.
-/

namespace Hunter.ProofsProfile

open Hunter ProofsLedger

/-! ## §1. Boundary lower bound: every window boundary weighs `≥ 2`. -/

/-- Every block boundary `t` with `1 ≤ t ≤ N − 1` (so `k·t < numVerts`) weighs at least `2`.
Direct from `ProofsWindow.boundary_ge_two` unfolded through `ProofsLedger.bw`. -/
lemma bw_ge_two_in_window {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    {t : ℕ} (ht1 : 1 ≤ t) (htM : t ≤ ((m + 3) * (m + 2)) - 1) :
    2 ≤ bw p t := by
  have hk1 : 1 ≤ m + 4 := by omega
  -- `k · t < numVerts` from `t ≤ N − 1 < N` and `hN`.
  have htN : t < (m + 3) * (m + 2) := by
    have hNpos : 1 ≤ (m + 3) * (m + 2) := by nlinarith
    omega
  have htlt : (m + 4) * t < p.numVerts :=
    lt_trans (Nat.mul_lt_mul_of_pos_left htN (by omega)) hN
  have hkt : 1 ≤ (m + 4) * t := by
    calc 1 ≤ (m + 4) * 1 := by omega
      _ ≤ (m + 4) * t := Nat.mul_le_mul_left _ ht1
  have hkt1 : (m + 4) * t - 1 + 1 = (m + 4) * t := by omega
  have hin : ((m + 4) * t - 1) + 1 < p.numVerts := by rw [hkt1]; exact htlt
  have hd : (m + 4) ∣ (((m + 4) * t - 1) + 1) := by rw [hkt1]; exact ⟨t, rfl⟩
  have hge2 := ProofsWindow.boundary_ge_two hk1 hp hin hd
  rw [hkt1] at hge2
  -- `bw p t` is definitionally the `ew` in `hge2`.
  show 2 ≤ ew (m + 4) (p.vert ((m + 4) * t - 1)) (p.vert ((m + 4) * t))
  exact hge2

/-! ## §2. Confinement floor: at least `m + 1 = k − 3` heavy boundaries in the window. -/

/-- `ProofsMeta6.window_heavy_count` (confinement + cover) forces at least
`(N−1) ⌈/⌉ (k−1) − 1 = k − 3 = m + 1` boundaries of weight `≥ 3` in the window `t ∈ [1, N−1]`. -/
lemma positive_boundary_count_ge {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts) :
    m + 1 ≤ ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter
        (fun t => 3 ≤ bw p t)).card := by
  have hk3 : 3 ≤ m + 4 := by omega
  have hNpos : 1 ≤ (m + 3) * (m + 2) := by nlinarith
  have hMlt : (m + 4) * (0 + (((m + 3) * (m + 2)) - 1)) < p.numVerts := by
    have hlt : (0 + (((m + 3) * (m + 2)) - 1)) < (m + 3) * (m + 2) := by omega
    exact lt_trans (Nat.mul_lt_mul_of_pos_left hlt (by omega)) hN
  have hcount := ProofsMeta6.window_heavy_count hk3 hp 0 (((m + 3) * (m + 2)) - 1) hMlt
  have hceil : (((m + 3) * (m + 2)) - 1) ⌈/⌉ (m + 4 - 1) - 1 = m + 1 := by
    have hw := ProofsMeta6.windowM_ceilDiv (k := m + 4) hk3
    have e1 : m + 4 - 1 = m + 3 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    rw [e1, e2] at hw
    rw [e1, hw]
    omega
  rw [hceil] at hcount
  -- convert the `ew` filter predicate (at `0 + j`) to the `bw` predicate
  have hfe : ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter
        (fun j => 3 ≤ ew (m + 4) (p.vert ((m + 4) * (0 + j) - 1)) (p.vert ((m + 4) * (0 + j))))).card
      = ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).card := by
    congr 1
    apply Finset.filter_congr
    intro t _
    simp only [Nat.zero_add, ProofsLedger.bw]
  rw [hfe] at hcount
  exact hcount

/-! ## §3–4. Pin the heavy count to exactly `m + 1` under low front-excess. -/

/-- The number of heavy boundaries is at most the total boundary excess `Σ (bw − 2)`: each heavy
boundary contributes at least `1`, all boundaries contribute `≥ 0`. -/
lemma positive_boundary_count_le_sum {m : ℕ} {p : HPath (m + 4)} (_hp : p.Exitless)
    (_hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts) :
    ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).card
      ≤ (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) := by
  set R := Finset.Icc 1 (((m + 3) * (m + 2)) - 1) with hR
  set S := R.filter (fun t => 3 ≤ bw p t) with hS
  calc S.card = ∑ _t ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ t ∈ S, (bw p t - 2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [hS, Finset.mem_filter] at ht
        omega
    _ ≤ ∑ t ∈ R, (bw p t - 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro t _ _; exact Nat.zero_le _

/-- Under the low front-excess hypothesis `Σ (bw − 2) ≤ m + 1`, the heavy count is **exactly**
`m + 1 = k − 3`, and the excess sum is exactly `m + 1` too. -/
lemma positive_boundary_count_eq {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hlow : (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) ≤ m + 1) :
    ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).card = m + 1 := by
  have hge := positive_boundary_count_ge hp hN
  have hle := positive_boundary_count_le_sum hp hN
  omega

/-! ## §5. Exact boundary weights: heavy ⇒ weight 3, non-heavy ⇒ weight 2. -/

/-- Under low front-excess, every window boundary weighs exactly `2` (within-run door) or exactly
`3` (run boundary); there are **no** weight-`≥4` boundaries in the window.  The `= 3` half is the
`PROOF_S2 §2` zero-slack collapse: the `m+1` heavy boundaries carry total excess exactly `m+1`, so
each carries excess exactly `1`. -/
lemma boundary_weights_exact {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hlow : (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) ≤ m + 1) :
    (∀ t ∈ Finset.Icc 1 (((m + 3) * (m + 2)) - 1), 3 ≤ bw p t → bw p t = 3) ∧
    (∀ t ∈ Finset.Icc 1 (((m + 3) * (m + 2)) - 1), ¬ 3 ≤ bw p t → bw p t = 2) := by
  -- the "off the heavy set ⇒ weight 2" half (also zeroes out the complement in the sum)
  have hpart2 : ∀ t ∈ Finset.Icc 1 (((m + 3) * (m + 2)) - 1), ¬ 3 ≤ bw p t → bw p t = 2 := by
    intro t htR hnh
    rw [Finset.mem_Icc] at htR
    have := bw_ge_two_in_window hp hN htR.1 htR.2
    omega
  refine ⟨?_, hpart2⟩
  -- the sum over the heavy set equals the sum over the whole window (complement terms are 0)
  have hsub : (((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).sum
        (fun t => bw p t - 2))
      = (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t htR htnS
    have hnh : ¬ 3 ≤ bw p t := fun hh => htnS (Finset.mem_filter.mpr ⟨htR, hh⟩)
    have := hpart2 t htR hnh
    omega
  -- pin the sum, the card, and hence force each heavy boundary to excess exactly 1
  have hge := positive_boundary_count_ge hp hN
  have hle := positive_boundary_count_le_sum hp hN
  have hcard := positive_boundary_count_eq hp hN hlow
  -- `∑_S 1 = ∑_S (bw − 2)` : both equal `m + 1`
  have hge' : ∀ t ∈ (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t),
      (1 : ℕ) ≤ bw p t - 2 := by
    intro t ht; rw [Finset.mem_filter] at ht; omega
  have hSsum : ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).sum
        (fun _ => (1 : ℕ))
      = ((Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t)).sum
        (fun t => bw p t - 2) := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, hcard, hsub]
    omega
  have hforce := (Finset.sum_eq_sum_iff_of_le hge').mp hSsum
  intro t htR hh
  have htS : t ∈ (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).filter (fun t => 3 ≤ bw p t) :=
    Finset.mem_filter.mpr ⟨htR, hh⟩
  have := hforce t htS
  omega

/-! ## §6. Door-run length cap: no `k = m + 4` consecutive door-joined blocks (`confinement`). -/

/-- A maximal weight-2 (door) run of `L` blocks starting at block `a`, staying inside the window,
has length `L ≤ m + 3 = k − 1`.  If `L ≥ k`, the boundaries `a+1 … a+(k−1)` would be `k − 1`
consecutive doors joining `k` complete blocks, contradicting `ProofsConfinement.confinement`. -/
lemma door_run_length_cap {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    {a L : ℕ} (hLast : a + L ≤ (m + 3) * (m + 2))
    (hdoors : ∀ r, 1 ≤ r → r ≤ L - 1 → bw p (a + r) = 2) :
    L ≤ m + 3 := by
  by_contra hcon
  push Not at hcon   -- `m + 3 < L`, i.e. `m + 4 ≤ L`
  have hlt : a + (m + 4) - 1 < (m + 3) * (m + 2) := by omega
  have hlast : (m + 4) * (a + (m + 4) - 1) < p.numVerts :=
    lt_trans (Nat.mul_lt_mul_of_pos_left hlt (by omega)) hN
  refine ProofsConfinement.confinement (by omega : (2 : ℕ) ≤ m + 4) hp hlast ?_
  intro t ht1 ht2
  have hbwt := hdoors (t - a) (by omega) (by omega)
  rw [show a + (t - a) = t from by omega] at hbwt
  -- `bw p t = 2` is definitionally the `ew` door equation `confinement` wants
  exact hbwt

/-! ## §7. The pure `ℕ`/`Finset` zero-slack pigeonhole (the coordinate-alignment core).

This isolates all the sorted-cut / `orderEmbOfFin` bookkeeping.  Given `r − 1` "positive" positions
in `[1, n·r − 1]` whose door-runs are each capped at length `n`, the zero-slack collapse
(`runlen_pigeonhole`) forces the `r` runs to each have the full length `n`, pinning the positives at
exactly `n, 2n, …, (r−1)n`.  The consumer instantiates `n = m + 3`, `r = m + 2`,
`P t := 3 ≤ bw p t`. -/

/-- Telescoping of truncated differences of a monotone `ℕ → ℕ`. -/
private lemma sum_tsub_telescope (g : ℕ → ℕ) (hg : Monotone g) :
    ∀ M, (Finset.range M).sum (fun i => g (i + 1) - g i) = g M - g 0 := by
  intro M
  induction M with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 := hg (Nat.zero_le k)
      have h2 := hg (show k ≤ k + 1 by omega)
      omega

/-- **Zero-slack positions.**  If exactly `r − 1` positions of `[1, n·r − 1]` satisfy `P`, and every
`P`-free run of blocks has length `≤ n` (`hcap`), then the `P`-positions are **exactly**
`{(j+1)·n : j < r − 1}`. -/
lemma positive_positions_zero_slack {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (P : ℕ → Prop) [DecidablePred P]
    (hcount : ((Finset.Icc 1 (n * r - 1)).filter P).card = r - 1)
    (hcap : ∀ a L, 1 ≤ L → a + L ≤ n * r →
        (∀ s, 1 ≤ s → s ≤ L - 1 → ¬ P (a + s)) → L ≤ n) :
    ∀ t, t ∈ Finset.Icc 1 (n * r - 1) →
      (P t ↔ ∃ j, j < r - 1 ∧ t = (j + 1) * n) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcount ⊢
  -- the positive set and its order embedding
  set S : Finset ℕ := (Finset.Icc 1 (n * (r' + 1) - 1)).filter P with hSdef
  have hSc : S.card = r' := hcount
  set e : Fin r' ↪o ℕ := S.orderEmbOfFin hSc with hedef
  have emem : ∀ i, e i ∈ S := fun i => S.orderEmbOfFin_mem hSc i
  have erange : Set.range e = ↑S := S.range_orderEmbOfFin hSc
  have hein : ∀ i : Fin r', 1 ≤ e i ∧ e i ≤ n * (r' + 1) - 1 := by
    intro i
    have := emem i
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at this
    exact this.1
  -- the extended cut function on `ℕ`
  set e' : ℕ → ℕ := fun j => if hj : j < r' then e ⟨j, hj⟩ else n * (r' + 1) with he'def
  have he'lt : ∀ j (hj : j < r'), e' j = e ⟨j, hj⟩ := fun j hj => dif_pos hj
  have he'ge : ∀ j, r' ≤ j → e' j = n * (r' + 1) := fun j hj => dif_neg (by omega)
  have he'bound : ∀ j, e' j ≤ n * (r' + 1) := by
    intro j; by_cases hj : j < r'
    · rw [he'lt j hj]; have := (hein ⟨j, hj⟩).2; omega
    · rw [he'ge j (by omega)]
  have he'mono : Monotone e' := by
    intro a b hab
    by_cases hb : b < r'
    · have ha : a < r' := by omega
      rw [he'lt a ha, he'lt b hb]; exact e.monotone (by exact_mod_cast Fin.mk_le_mk.mpr hab)
    · rw [he'ge b (by omega)]
      by_cases ha : a < r'
      · rw [he'lt a ha]; have := (hein ⟨a, ha⟩).2; omega
      · rw [he'ge a (by omega)]
  set cut : ℕ → ℕ := fun j => if j = 0 then 0 else e' (j - 1) with hcutdef
  have hcut0 : cut 0 = 0 := if_pos rfl
  have hcutS : ∀ i, cut (i + 1) = e' i := by
    intro i; show (if i + 1 = 0 then 0 else e' (i + 1 - 1)) = e' i
    rw [if_neg (by omega), Nat.add_sub_cancel]
  have hcutbound : ∀ j, cut j ≤ n * (r' + 1) := by
    intro j; rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, hcut0]; exact Nat.zero_le _
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hcutS]; exact he'bound i
  have hcutval : ∀ i : Fin r', cut (i.val + 1) = e i := by
    intro i; rw [hcutS, he'lt i.val i.isLt]
  have hmono : Monotone cut := by
    apply monotone_nat_of_le_succ
    intro i
    cases i with
    | zero => rw [hcut0]; exact Nat.zero_le _
    | succ k => rw [hcutS k, hcutS (k + 1)]; exact he'mono (Nat.le_succ k)
  -- the `r' + 1` run lengths
  set L : Fin (r' + 1) → ℕ := fun i => cut (i.val + 1) - cut i.val with hLdef
  -- run-length sum is `n · (r' + 1)` (telescoping)
  have hsum : (Finset.univ.sum fun i => L i) = n * (r' + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => cut (j + 1) - cut j) (r' + 1)]
    rw [sum_tsub_telescope cut hmono (r' + 1), hcut0, Nat.sub_zero]
    -- `cut (r' + 1) = n · (r' + 1)`
    rw [hcutS r', he'ge r' (le_refl r')]
  -- each run length is `≤ n` (via `hcap`)
  have hcapL : ∀ i, L i ≤ n := by
    intro i
    rcases Nat.eq_zero_or_pos (L i) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hmi := hmono (show i.val ≤ i.val + 1 by omega)   -- cut i ≤ cut (i+1)
      have hsegeq : cut i.val + L i = cut (i.val + 1) := by simp only [hLdef]; omega
      apply hcap (cut i.val) (L i) hpos
      · rw [hsegeq]; exact hcutbound (i.val + 1)
      · intro s hs1 hs2 hPs
        -- `cut i + s` lies strictly between the two cuts, so it is a positive between adjacent
        -- cuts — impossible.
        have hlt1 : cut i.val < cut i.val + s := by omega
        have hlt2 : cut i.val + s < cut (i.val + 1) := by
          simp only [hLdef] at hs2; omega
        have hmemwin : cut i.val + s ∈ Finset.Icc 1 (n * (r' + 1) - 1) := by
          rw [Finset.mem_Icc]
          have hub : cut (i.val + 1) ≤ n * (r' + 1) := hcutbound (i.val + 1)
          exact ⟨by omega, by omega⟩
        have hmemS : cut i.val + s ∈ S := by
          rw [hSdef, Finset.mem_filter]; exact ⟨hmemwin, hPs⟩
        obtain ⟨k, hk⟩ : ∃ k : Fin r', e k = cut i.val + s := by
          have : cut i.val + s ∈ Set.range e := by rw [erange]; exact hmemS
          exact this
        rw [← hcutval k] at hk    -- cut (k+1) = cut i + s
        -- strict monotonicity ⇒ `i < k+1 < i+1`, contradiction
        have hA : i.val < k.val + 1 := by
          by_contra hc; push Not at hc
          exact absurd (hmono hc) (by omega)
        have hB : k.val + 1 < i.val + 1 := by
          by_contra hc; push Not at hc
          exact absurd (hmono hc) (by omega)
        omega
  -- fire the zero-slack pigeonhole
  obtain ⟨_, hLn⟩ := ProofsRigidity2.runlen_pigeonhole (r := r' + 1) (m := r' + 1)
    (n := n) hn (le_refl _) L hcapL hsum
  -- each cut is at `i · n`
  have hcuteq : ∀ i, i ≤ r' + 1 → cut i = i * n := by
    intro i
    induction i with
    | zero => intro _; rw [hcut0]; ring
    | succ k ih =>
        intro hk1
        have hkr : k < r' + 1 := by omega
        have hLk : cut (k + 1) - cut k = n := hLn ⟨k, hkr⟩
        have hmk := hmono (show k ≤ k + 1 by omega)
        have hck := ih (by omega)
        have hstep : cut (k + 1) = cut k + n := by omega
        rw [hstep, hck]; ring
  -- so `e j = (j+1) · n`
  have hej : ∀ j : Fin r', e j = (j.val + 1) * n := by
    intro j
    rw [← hcutval j, hcuteq (j.val + 1) (by omega)]
  -- conclude the position characterization
  intro t ht
  constructor
  · intro hPt
    have htS : t ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨ht, hPt⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin r', e k = t := by
      have : t ∈ Set.range e := by rw [erange]; exact htS
      exact this
    exact ⟨k.val, k.isLt, by rw [← hk, hej k]⟩
  · rintro ⟨j, hj, rfl⟩
    have hkt : e ⟨j, hj⟩ = (j + 1) * n := hej ⟨j, hj⟩
    have : (j + 1) * n ∈ S := by rw [← hkt]; exact emem ⟨j, hj⟩
    rw [hSdef, Finset.mem_filter] at this
    exact this.2

/-! ## §8. Heavy boundaries sit exactly at the chart run-end coordinates `(j+1)(m+3)`. -/

/-- Instantiate the zero-slack pigeonhole at `n = m + 3`, `r = m + 2`, `P t := 3 ≤ bw p t`:
the heavy boundaries in the window are **exactly** `t = (j+1)(m+3)` for `j < m + 1`. -/
lemma positive_boundary_positions {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hlow : (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) ≤ m + 1) :
    ∀ t, t ∈ Finset.Icc 1 (((m + 3) * (m + 2)) - 1) →
      (3 ≤ bw p t ↔ ∃ j, j < m + 1 ∧ t = (j + 1) * (m + 3)) := by
  have hcount : ((Finset.Icc 1 ((m + 3) * (m + 2) - 1)).filter (fun t => 3 ≤ bw p t)).card
      = (m + 2) - 1 := by
    have := positive_boundary_count_eq hp hN hlow; omega
  have hcap : ∀ a L, 1 ≤ L → a + L ≤ (m + 3) * (m + 2) →
      (∀ s, 1 ≤ s → s ≤ L - 1 → ¬ 3 ≤ bw p (a + s)) → L ≤ m + 3 := by
    intro a L _ hLN hnoP
    apply door_run_length_cap hp hN hLN
    intro r hr1 hr2
    have h2 := bw_ge_two_in_window hp hN (show 1 ≤ a + r by omega)
      (show a + r ≤ (m + 3) * (m + 2) - 1 by omega)
    have hnp := hnoP r hr1 hr2
    omega
  have hpz := positive_positions_zero_slack (n := m + 3) (r := m + 2) (by omega) (by omega)
    (fun t => 3 ≤ bw p t) hcount hcap
  intro t ht
  have hres := hpz t ht
  simpa using hres

/-! ## §9. The main profile: `run_profile_of_front_low`. -/

/-- **LINK (1).**  From an exitless path whose first `N = (k−1)(k−2)` blocks have **low front-excess**
(total boundary excess `Σ (bw − 2) ≤ m + 1 = k − 3`), extract the exact chart weight profile: every
within-run boundary weighs `2`, and the `k − 3` run boundaries — landing exactly at chart
coordinates `j·(k−1) + (k−2) + 1` — weigh `3`.  This is precisely the `(hbw2, hbw3)` pair consumed
by `Hunter.ProofsFinale.hpath_chart_heavy`. -/
theorem run_profile_of_front_low {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hlow : (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) ≤ m + 1) :
    (∀ j i, j ≤ m + 1 → i < m + 2 → bw p (j * (m + 3) + i + 1) = 2) ∧
    (∀ j, j < m + 1 → bw p (j * (m + 3) + (m + 2) + 1) = 3) := by
  have hpos := positive_boundary_positions hp hN hlow
  have hwt := boundary_weights_exact hp hN hlow
  refine ⟨?_, ?_⟩
  · -- within-run boundaries weigh 2
    intro j i hj hi
    have h1 : j * (m + 3) ≤ (m + 1) * (m + 3) := Nat.mul_le_mul_right _ hj
    have hlt : j * (m + 3) + i + 1 < (m + 3) * (m + 2) := by nlinarith [h1, hi]
    have htmem : j * (m + 3) + i + 1 ∈ Finset.Icc 1 ((m + 3) * (m + 2) - 1) := by
      rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
    have hnh : ¬ 3 ≤ bw p (j * (m + 3) + i + 1) := by
      intro hheavy
      obtain ⟨j', _, heq⟩ := (hpos _ htmem).mp hheavy
      have hd1 : (m + 3) ∣ (j * (m + 3)) := ⟨j, by ring⟩
      have hdt : (m + 3) ∣ (j * (m + 3) + (i + 1)) := by
        rw [show j * (m + 3) + (i + 1) = (j' + 1) * (m + 3) from by omega]
        exact ⟨j' + 1, by ring⟩
      have hdj : (m + 3) ∣ (i + 1) := (Nat.dvd_add_right hd1).mp hdt
      have := Nat.le_of_dvd (by omega) hdj
      omega
    exact hwt.2 _ htmem hnh
  · -- run boundaries weigh 3, at coordinate `(j+1)(m+3)`
    intro j hj
    have hteq : j * (m + 3) + (m + 2) + 1 = (j + 1) * (m + 3) := by ring
    have h1 : j * (m + 3) ≤ m * (m + 3) := Nat.mul_le_mul_right _ (by omega)
    have hlt : j * (m + 3) + (m + 2) + 1 < (m + 3) * (m + 2) := by nlinarith [h1]
    have htmem : j * (m + 3) + (m + 2) + 1 ∈ Finset.Icc 1 ((m + 3) * (m + 2) - 1) := by
      rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
    have hheavy : 3 ≤ bw p (j * (m + 3) + (m + 2) + 1) :=
      (hpos _ htmem).mpr ⟨j, hj, hteq⟩
    exact hwt.1 _ htmem hheavy

/-! ## §10. Immediate consumer wrapper: the heavy continuation boundary. -/

/-- Composing `run_profile_of_front_low` with `Hunter.ProofsFinale.hpath_chart_heavy`: a low
front-excess exitless path enters block `N = (m+3)(m+2)` by a boundary of weight `≥ 4`. -/
theorem front_low_chart_heavy {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hlow : (Finset.Icc 1 (((m + 3) * (m + 2)) - 1)).sum (fun t => bw p t - 2) ≤ m + 1) :
    4 ≤ bw p ((m + 3) * (m + 2)) := by
  obtain ⟨hbw2, hbw3⟩ := run_profile_of_front_low hp hN hlow
  exact Hunter.ProofsFinale.hpath_chart_heavy hp hN hbw2 hbw3

end Hunter.ProofsProfile

/-! ## Axiom audit -/
#print axioms Hunter.ProofsProfile.run_profile_of_front_low
#print axioms Hunter.ProofsProfile.front_low_chart_heavy

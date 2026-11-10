/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsRFrame

/-!
# Theorem 2 — the COMBINED strong induction (the doorDepth-0 kernel)

This file rebuilds the `ExcessFrontier k` argument as a single self-contained strong induction on
`numVerts`, so that the induction hypothesis (the frontier bound for *all shorter prefixes*) is
available exactly where the standalone residual `ProofsRFrame.TightLoopEntryFree` could not reach
it.  With the sub-prefix bound in hand the `doorDepth (winA p) = 0` ("loop-entry frontier") case
splits on whether the demand jumps over the frontier block:

* **non-jump length** (`j_k(n) = j_k(n−k) + (k+1)`, i.e. `Dfr(n) = Dfr(n−k)`): the loop-entry
  boundary pays `+1` excess whose demand has not arrived, so the sub-prefix bound + the `+1`
  contradict tightness — **closed here, unconditionally, by the combined induction** (`step_nojump`);
* **jump length** (`Dfr(n) = Dfr(n−k) + 1`): the `+1` is cancelled by the coincident demand jump;
  excluding it is the absolute door-phase ↔ demand-phase lock — the single residual
  `JumpLoopEntryFree k`, strictly smaller than `TightLoopEntryFree` (all non-jump lengths peeled).

Namespace `Hunter.ProofsFinal`.  Sorry-free, axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsFinal

open ProofsLedger ProofsLedger2 ProofsAssembly ProofsSynthesis ProofsRecursion ProofsWindow
open ProofsRFrame ProofsExcess ProofsMeta3 ProofsMeta6 ProofsConfinement
open HPath

variable {k : ℕ}

/-! ## §1. Arithmetic and ledger micro-lemmas -/

/-- `⌈n/k⌉ = ⌈(n−k)/k⌉ + 1` for `k ≤ n` (add-a-block ceiling step). -/
theorem ceilDiv_step (hk : 0 < k) {n : ℕ} (hn : k ≤ n) :
    n ⌈/⌉ k = (n - k) ⌈/⌉ k + 1 := by
  have h : (n - k) + k = n := by omega
  have := ceilDiv_add_dvd (a := n - k) (b := k) hk ⟨1, by ring⟩
  rw [h] at this
  rw [this, Nat.div_self hk]

/-- A loop-entry frontier block has a weight-`≥3` boundary: if `doorDepth p a = 0` with `a ≥ 1`
and the boundary is in range, then `3 ≤ bw p a` (it is a non-door, hence pays `≥ 1` excess). -/
theorem bw_ge_three_of_doorDepth_zero (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {a : ℕ}
    (ha : 1 ≤ a) (hN : k * a < p.numVerts) (hdd : doorDepth p a = 0) :
    3 ≤ bw p a := by
  -- `doorDepth p a = 0` with `a ≥ 1` forces `¬ IsDoor p a`
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hnd : ¬ IsDoor p (a' + 1) := by
    intro hd
    rw [doorDepth_door hd] at hdd; omega
  -- every boundary has `bw ≥ 2`; a non-door has `bw ≠ 2`, so `bw ≥ 3`
  have hkt : 1 ≤ k * (a' + 1) := Nat.mul_pos hk (by omega)
  have hi1 : k * (a' + 1) - 1 + 1 = k * (a' + 1) := by omega
  have hin : (k * (a' + 1) - 1) + 1 < p.numVerts := by rw [hi1]; exact hN
  have hd : k ∣ ((k * (a' + 1) - 1) + 1) := by rw [hi1]; exact ⟨a' + 1, rfl⟩
  have hge2 := boundary_ge_two hk hp hin hd
  rw [hi1] at hge2
  rw [IsDoor, bw] at hnd
  unfold bw
  omega

/-! ## §2. Prefix excess as an edge-weight sum, and the one-block step bound -/

/-- The excess of a length-`m` prefix, expressed as the `ew − 2` edge sum over `p` up to `m − 1`. -/
theorem excess_prefix_eq (hk : 1 ≤ k) {p q : HPath k} {m : ℕ} (hm : m ≤ p.numVerts)
    (hq : q.verts = p.verts.take m) :
    excess q = ∑ i ∈ Finset.range (m - 1), (ew k (p.vert i) (p.vert (i + 1)) - 2) := by
  have hqn : q.numVerts = m := by
    have hlen : q.verts.length = (p.verts.take m).length := by rw [hq]
    have hNl : p.verts.length = p.numVerts := rfl
    rw [List.length_take, hNl] at hlen
    show q.verts.length = m
    rw [hlen]; omega
  rw [excess_eq_sum_edgeWeight hk q, hqn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [prefix_vert_eq hq hm (show i < m by omega),
      prefix_vert_eq hq hm (show i + 1 < m by omega)]

/-- **One-block excess step.**  If `q` is the length-`n` prefix and `q'` the length-`n−k` prefix of
an exitless `p`, and `a = (n−1)/k` is the top block with `1 ≤ a`, `k ≤ n`, then the extra block
boundary `a` contributes at least its excess: `excess q' + (bw p a − 2) ≤ excess q`. -/
theorem excess_block_step (hk : 1 ≤ k) {p q q' : HPath k} {n a : ℕ}
    (hn : k ≤ n) (hnN : n ≤ p.numVerts) (ha : 1 ≤ a) (haval : a = (n - 1) / k)
    (hq : q.verts = p.verts.take n) (hq' : q'.verts = p.verts.take (n - k)) :
    excess q' + (bw p a - 2) ≤ excess q := by
  set f : ℕ → ℕ := fun i => ew k (p.vert i) (p.vert (i + 1)) - 2 with hfdef
  have heq : excess q = ∑ i ∈ Finset.range (n - 1), f i := excess_prefix_eq hk hnN hq
  have heq' : excess q' = ∑ i ∈ Finset.range (n - k - 1), f i :=
    excess_prefix_eq hk (by omega) hq'
  -- block-`a` boundary index
  have hka1 : k * a ≤ n - 1 := by
    rw [haval, Nat.mul_comm]; exact Nat.div_mul_le_self (n - 1) k
  have hmod : (n - 1) % k < k := Nat.mod_lt _ (by omega)
  have hdm : k * ((n - 1) / k) + (n - 1) % k = n - 1 := Nat.div_add_mod (n - 1) k
  have hka2 : n - 1 < k * a + k := by rw [haval]; omega
  have hkapos : 1 ≤ k * a := Nat.mul_pos (by omega) ha
  -- split the range `[0, n−1)` at `n−k−1`
  have hsplit : ∑ i ∈ Finset.range (n - 1), f i
      = ∑ i ∈ Finset.range (n - k - 1), f i + ∑ i ∈ Finset.Ico (n - k - 1) (n - 1), f i := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le (n - k - 1)) (by omega : n - k - 1 ≤ n - 1)]
  -- the block-`a` boundary edge `k*a − 1` lies in `[n−k−1, n−1)`
  have hmem : (k * a - 1) ∈ Finset.Ico (n - k - 1) (n - 1) := by
    rw [Finset.mem_Ico]; omega
  have hsingle : f (k * a - 1) ≤ ∑ i ∈ Finset.Ico (n - k - 1) (n - 1), f i :=
    Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hmem
  have hfval : f (k * a - 1) = bw p a - 2 := by
    have e1 : k * a - 1 + 1 = k * a := by omega
    simp only [hfdef, bw]; rw [e1]
  rw [heq, heq', hsplit, ← hfval]
  omega

/-! ## §3. The pointwise tight-window payment (Cases A/B/C, `doorDepth ≠ 0`) -/

/-- **Pointwise tight-window payment.**  For a frontier-tight prefix `q` of a recursion-region
exitless `p` whose frontier block is *not* a loop entry (`doorDepth p (winA p) ≠ 0`), the top
`ℓ₀`-window pays the full `k − 2`.  This is the pointwise form of
`frontierTightHeavy_of_saturated ∘ saturatedTightHeavy_of_loopEntryFree`: Cases A/B are the
unconditional counting closures, Case C is `saturatedHeavy_of_doorPos` fed with `hdoor`. -/
theorem tight_window_pays (hk : 3 ≤ k) {p q : HPath k} (hpe : p.Exitless) (hqe : q.Exitless)
    (hlt : k * (k - 1) * (k - 2) < p.numVerts)
    (hprefix : q.verts = p.verts.take (p.numVerts - ell0 k))
    (hdoor : doorDepth p (winA p) ≠ 0) :
    excess q + (k - 2) ≤ excess p := by
  set a := winA p with hadef
  set M := (k - 1) * (k - 2) - 1 with hMdef
  have hrange : k * (a + M) < p.numVerts := by rw [hadef, hMdef]; exact winA_range hk hlt
  have hsplit := excess_window_split hk hlt hprefix
  rw [← hadef, ← hMdef] at hsplit
  set W3 := (Finset.filter (fun j => 3 ≤ bw p (a + j)) (Finset.Icc 1 M)).card with hW3
  set H4 := (Finset.filter (fun j => 4 ≤ bw p (a + j)) (Finset.Icc 1 M)).card with hH4
  have hpay : W3 + H4 ≤ ∑ j ∈ Finset.Icc 1 M, (bw p (a + j) - 2) := by
    rw [hW3, hH4, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases h3 : 3 ≤ bw p (a + j) <;> by_cases h4 : 4 ≤ bw p (a + j) <;>
      simp only [h3, h4, if_true, if_false] <;> omega
  have hfloor : k - 3 ≤ W3 := by
    have h := window_heavy_count hk hpe a M hrange
    rw [hMdef, windowM_ceilDiv hk] at h
    have hcard : (Finset.filter (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))
        (Finset.Icc 1 M)).card = W3 := rfl
    rw [hcard] at h; omega
  by_cases hA : ∃ j, 1 ≤ j ∧ j ≤ M ∧ 4 ≤ bw p (a + j)
  · obtain ⟨j, hj1, hjM, hj4⟩ := hA
    have hH4pos : 1 ≤ H4 := by
      rw [hH4]; apply Finset.one_le_card.mpr
      exact ⟨j, by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hj1, hjM⟩, hj4⟩⟩
    omega
  · by_cases hB : ∃ j, 1 ≤ j ∧ j ≤ M ∧ ¬ IsDoor p (a + j) ∧ doorDepth p (a + j - 1) ≤ k - 3
    · obtain ⟨s₀, hs01, hs02, hnd, hinc⟩ := hB
      have h := window_incomplete_slack hk hpe a (by rw [← hMdef]; exact hrange)
        s₀ hs01 (by rw [← hMdef]; exact hs02) hnd hinc
      have hcard : (Finset.filter
          (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))
          (Finset.Icc 1 M)).card = W3 := rfl
      rw [← hMdef] at h; rw [hcard] at h; omega
    · -- Case C: saturated window, `doorDepth ≠ 0` ⇒ pays `k − 2` by `saturatedHeavy_of_doorPos`
      have hWsat : WindowSaturated p a M := by
        refine ⟨fun j hj1 hjM => ?_, fun j hj1 hjM => ?_⟩
        · by_contra hc; exact hA ⟨j, hj1, hjM, by omega⟩
        · by_cases hd : IsDoor p (a + j)
          · exact Or.inl hd
          · exact Or.inr (by by_contra hc; exact hB ⟨j, hj1, hjM, hd, by omega⟩)
      exact saturatedHeavy_of_doorPos hk hpe hqe hlt hprefix hWsat hdoor

/-! ## §4. The residual and the combined strong induction -/

/-- **The residual `JumpLoopEntryFree`.**  The `doorDepth (winA p) = 0` case restricted to
*jump lengths* — the top window's prefix length `n = |p| − ℓ₀` where the demand strictly jumps
over the frontier block (`j_k(n) ≠ j_k(n−k) + (k+1)`, i.e. `Dfr(n) = Dfr(n−k)+1`).  This is
strictly weaker than `ProofsRFrame.TightLoopEntryFree`: the combined induction below discharges
*every non-jump length* unconditionally (`excessFrontier_of_jumpLoopEntryFree`), so only the
absolute demand-phase alignment on jump lengths remains. -/
def JumpLoopEntryFree (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q →
    j k (p.numVerts - ell0 k) ≠ j k (p.numVerts - ell0 k - k) + (k + 1) →
    doorDepth p (winA p) ≠ 0

/-- **The combined strong induction.**  `JumpLoopEntryFree k → ExcessFrontier k`, by a single
strong induction on `numVerts`.  The tight-prefix window step splits into: Cases A/B/C with
`doorDepth ≠ 0` (`tight_window_pays`, unconditional payment `k − 2`); and the loop-entry case
`doorDepth (winA p) = 0`, itself split on the demand jump — **non-jump lengths are closed by the
induction hypothesis** (the loop-entry boundary pays `+1` whose demand has not arrived,
contradicting tightness), **jump lengths** are the residual `JumpLoopEntryFree`. -/
theorem excessFrontier_of_jumpLoopEntryFree (hk : 3 ≤ k) (hJ : JumpLoopEntryFree k) :
    ExcessFrontier k := by
  have main : ∀ ℓ : ℕ, ∀ p : HPath k, p.Exitless → p.numVerts = ℓ →
      j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro p hpe hpℓ
      have h0 : 0 < p.numVerts := p.numVerts_pos
      by_cases hbaseR : p.numVerts ≤ k * (k - 1) * (k - 2)
      · exact excess_frontier_base hk hpe h0 hbaseR
      · rw [Nat.not_le] at hbaseR
        have he0pos : 0 < ell0 k := ell0_pos hk
        have hm : 2 ≤ (k - 1) * (k - 2) := by
          have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
          omega
        have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
        have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
        have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
        have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
        have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
        set n := p.numVerts - ell0 k with hn
        have hn1 : 1 ≤ n := by rw [hn]; omega
        have hnk : k < n := by rw [hn, he0val]; omega
        have hnle : n ≤ p.numVerts := by rw [hn]; omega
        have hnlt : n < p.numVerts := by rw [hn]; omega
        have hNsum : p.numVerts = n + ell0 k := by rw [hn]; omega
        obtain ⟨q, hqv, hqe⟩ := prefix_exitless hpe hn1 hnle
        have hqnv : q.numVerts = n := by
          have hlen : p.verts.length = p.numVerts := rfl
          show q.verts.length = n
          rw [hqv, List.length_take, hlen]; omega
        have hpre : q.verts = p.verts.take (p.numVerts - ell0 k) := by rw [hqv, hn]
        have hnltℓ : n < ℓ := by rw [← hpℓ]; exact hnlt
        have hIH := ih n hnltℓ q hqe hqnv
        rw [hqnv] at hIH
        have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
        have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
          rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd,
              ceilDiv_ell0 hk]
        have hsplit : p.numVerts ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
          rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
        have hjrec : j k p.numVerts = j k n + j k (ell0 k) + 3 := by
          have hr := j_rec_unfold_one hk hbaseR
          rw [← hn] at hr; exact hr
        have hXn1 : 1 ≤ n ⌈/⌉ k := by
          rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
        have hXe1 : 1 ≤ ell0 k / k :=
          (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
        by_cases htight : j k n = (n - 1) + (n ⌈/⌉ k - 1) + excess q
        · -- frontier-tight prefix: establish `doorDepth (winA p) ≠ 0`, then pay `k − 2`
          have haval : winA p = (n - 1) / k := by
            show (p.numVerts - ell0 k - 1) / k = (n - 1) / k
            have hnn : p.numVerts - ell0 k - 1 = n - 1 := by omega
            rw [hnn]
          have ha1 : 1 ≤ winA p := by
            rw [haval]; exact (Nat.one_le_div_iff (show 0 < k by omega)).mpr (by omega)
          have hdoor : doorDepth p (winA p) ≠ 0 := by
            intro hdd0
            by_cases hjump : j k n = j k (n - k) + (k + 1)
            · -- non-jump length: the induction hypothesis closes it
              obtain ⟨q', hq'v, hq'e⟩ := prefix_exitless hpe (show 1 ≤ n - k by omega)
                (show n - k ≤ p.numVerts by omega)
              have hq'nv : q'.numVerts = n - k := by
                have hlen : p.verts.length = p.numVerts := rfl
                show q'.verts.length = n - k
                rw [hq'v, List.length_take, hlen]; omega
              have hIH' := ih (n - k) (by omega) q' hq'e hq'nv
              rw [hq'nv] at hIH'
              have hkaN : k * winA p < p.numVerts := by
                have : k * winA p ≤ n - 1 := by
                  rw [haval, Nat.mul_comm]; exact Nat.div_mul_le_self (n - 1) k
                omega
              have hbw3 : 3 ≤ bw p (winA p) :=
                bw_ge_three_of_doorDepth_zero (by omega) hpe ha1 hkaN hdd0
              have hstep : excess q' + (bw p (winA p) - 2) ≤ excess q :=
                excess_block_step (by omega) (by omega) hnle ha1 haval hqv hq'v
              have hcstep : n ⌈/⌉ k = (n - k) ⌈/⌉ k + 1 := ceilDiv_step (by omega) (by omega)
              have hXnk1 : 1 ≤ (n - k) ⌈/⌉ k := by
                rw [Proved.ceilDiv_succ_pred (show 1 ≤ n - k by omega) (show 0 < k by omega)]
                exact Nat.le_add_left 1 _
              omega
            · -- jump length: the residual
              exact hJ p q hpe hqe hbaseR hpre (by rw [hqnv]; exact htight) (by rw [← hn]; exact hjump) hdd0
          have hwin : excess q + (k - 2) ≤ excess p := tight_window_pays hk hpe hqe hbaseR hpre hdoor
          omega
        · -- bank ≥ 1: the proved `k − 3` floor suffices
          have hfloor : excess q + (k - 3) ≤ excess p :=
            windowExcess_ge_km3 hk hpe hbaseR hpre
          omega
  intro q hqe h0
  have := main q.numVerts q hqe rfl
  omega

/-! ## §5. The residue lock — where the jump-length kernel sits -/

/-- **The door-phase residue of a loop-entry frontier.**  By `runLen_eq`, a loop-entry frontier
block (`doorDepth p (winA p) = 0`) satisfies `winA p ≡ runStart p (winA p)  (mod k−1)`.  Combined
with the jump-block phase (the demand `Dfr` jumps at `t ≡ 1 (mod k−1)` *within each ℓ₀-window*,
verified symbolically in `scratchpad/campaign/final/jumpblocks.py` at k=5,6,7,8), a loop entry lands
on a jump block exactly when `runStart p (winA p) ≡ 1 (mod k−1)`.  The residual `JumpLoopEntryFree`
is thus the statement that a tight saturated loop-entry frontier avoids this residue — the
"absolute" door-phase ↔ demand-phase alignment.  `runStart` drifts by the meta-heavy firing depth
at each meta-heavy (`runStart mod (k−1)` is preserved iff meta-heavies fire at `doorDepth 0`), so the
alignment is genuinely path-global (not a function of any bounded structural state); this is the
irreducible content the LP flagged and Hunter's `HPath(k−1)` meta-lift would supply. -/
theorem winA_residue_of_doorDepth_zero (hk : 3 ≤ k) (p : HPath k)
    (hdd : doorDepth p (winA p) = 0) :
    winA p % (k - 1) = runStart p (winA p) % (k - 1) := by
  have h := runLen_eq hk p (winA p)
  rw [hdd, Nat.add_zero] at h
  calc winA p % (k - 1)
      = (runStart p (winA p) + metaDepth p (winA p) * (k - 1)) % (k - 1) := by rw [h]
    _ = runStart p (winA p) % (k - 1) := by rw [Nat.add_mul_mod_self_right]

/-! ## §6. Certification and the capstone chain -/

/-- **The residual is strictly weaker than `TightLoopEntryFree`.**  `JumpLoopEntryFree k` merely
drops the jump-length hypothesis, so it follows from `ProofsRFrame.TightLoopEntryFree k` — the
combined induction has peeled off every non-jump length. -/
theorem jumpLoopEntryFree_of_tightLoopEntryFree (h : TightLoopEntryFree k) :
    JumpLoopEntryFree k :=
  fun p q hpe hqe hlt hpre htight _ => h p q hpe hqe hlt hpre htight

/-- **`ExcessFrontier k → FrontierTightHeavy k`.**  Once the frontier bound holds for *all*
exitless paths, a frontier-tight prefix's top window pays the full `k − 2`: the frontier at `p`
gives `excess p ≥ Dfr(N)`, tightness gives `excess q = Dfr(n)`, and the `D`-recursion gives
`Dfr(N) = Dfr(n) + (k − 2)`.  This recovers the `(MF)`-conditional capstones from the (weaker)
combined-induction residual. -/
theorem frontierTightHeavy_of_excessFrontier (hk : 3 ≤ k) (hfr : ExcessFrontier k) :
    FrontierTightHeavy k := by
  intro p q hpe hqe hbaseR hprefix htight
  have he0pos : 0 < ell0 k := ell0_pos hk
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hm : 2 ≤ (k - 1) * (k - 2) := by
    have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
  have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
  have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
  set N := p.numVerts with hNdef
  set n := N - ell0 k with hn
  have hn1 : 1 ≤ n := by rw [hn]; omega
  have hnle : n ≤ N := by rw [hn]; omega
  have hNsum : N = n + ell0 k := by rw [hn]; omega
  have hqnv : q.numVerts = n := by
    have hlen : p.verts.length = N := rfl
    show q.verts.length = n
    rw [hprefix, List.length_take, hlen]; omega
  have h0p : 0 < N := by omega
  have hfrp := hfr p hpe h0p
  rw [← hNdef] at hfrp
  rw [hqnv] at htight
  have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
  have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
    rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd, ceilDiv_ell0 hk]
  have hsplit : N ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
    rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
  have hjrec : j k N = j k n + j k (ell0 k) + 3 := by
    have hr := j_rec_unfold_one hk hbaseR; rw [← hn] at hr; exact hr
  have hXn1 : 1 ≤ n ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
  have hXe1 : 1 ≤ ell0 k / k := (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
  have hXN1 : 1 ≤ N ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred (show 1 ≤ N by omega) (show 0 < k by omega)]
    exact Nat.le_add_left 1 _
  omega

/-- **The global combined residual.** -/
def JumpLoopEntryFreeAll : Prop := ∀ k, 3 ≤ k → JumpLoopEntryFree k

/-- `JumpLoopEntryFreeAll → FrontierTightHeavyAll` (= `(MF)` global) — the bridge into the
`ProofsMF` / `ProofsAssembly` capstones. -/
theorem frontierTightHeavyAll_of_jumpLoopEntryFreeAll (hJ : JumpLoopEntryFreeAll) :
    FrontierTightHeavyAll :=
  fun k hk => frontierTightHeavy_of_excessFrontier hk
    (excessFrontier_of_jumpLoopEntryFree hk (hJ k hk))

/-- **Theorem 2 from the combined residual** (verbatim `Statements.thm2` conclusion). -/
theorem thm2_of_jumpLoopEntryFree {k ℓ : ℕ} (hk : 3 ≤ k) (hJ : JumpLoopEntryFree k)
    (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (excessFrontier_of_jumpLoopEntryFree hk hJ) hℓ

/-- **Theorem 2, globally, from the combined residual.** -/
theorem thm2_global_of_jumpLoopEntryFree (hJ : JumpLoopEntryFreeAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  fun k _ℓ hk hℓ => thm2_of_jumpLoopEntryFree hk (hJ k hk) hℓ

/-- **thm1v1 from the combined residual** (superpermutation form). -/
theorem thm1v1_of_jumpLoopEntryFree (hJ : JumpLoopEntryFreeAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsMF.thm1v1_of_MF (frontierTightHeavyAll_of_jumpLoopEntryFreeAll hJ) hproof hexists

/-- **thm1v2 from the combined residual** (`L(k) ≥ coeff(k)·k! − O(1)`). -/
theorem thm1v2_of_jumpLoopEntryFree (hJ : JumpLoopEntryFreeAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsMF.thm1v2_of_MF (frontierTightHeavyAll_of_jumpLoopEntryFreeAll hJ) hproof hexists

end ProofsFinal

end Hunter

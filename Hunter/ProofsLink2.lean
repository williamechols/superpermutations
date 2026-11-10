/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsFinale
import Hunter.ProofsEndgame
import Hunter.ProofsWindow
import Hunter.ProofsMeta3
import Hunter.ProofsMeta6
import Hunter.ProofsLedger2
import Hunter.ProofsProfile
import Hunter.ProofsQED

/-!
# LINK 2 — the §4 excess strong-induction that closes Hunter's Theorem 2

This file implements the plan `PLAN.md` (link 2).  It proves the sharp opened-block bound
`⌈|p|/k⌉ ≤ G k (excess p)` (equivalently `ProofsRigid.ExcessBlockCeil k`) by strong induction on
`E = excess p`, and converts it to `ProofsEndgame.TightJumpFreeAll` via a reverse bridge.

The step-B (chart-drop) branch consumes the front-`N`-block chart profile that
`ProofsFinale.hpath_chart_heavy` requires. That profile is produced by the sibling development
`Hunter.ProofsProfile.run_profile_of_front_low`. The main induction is factored through an
explicit `ProfileHyp`; `profileHyp_holds` discharges it below, yielding the unconditional
`Hunter.Proved.tightJumpFree` and headline capstones.

Everything here lives in `namespace Hunter.ProofsLink2`; it is sorry-free and axiom-clean.
-/

namespace Hunter
namespace ProofsLink2

open scoped Classical
open ProofsPotential ProofsRecursion ProofsInduction Proved HPath ProofsLedger ProofsChart

variable {k : ℕ}

/-! ## §1. Small arithmetic and cut helpers -/

/-- Front-pay: the accumulated boundary excess `Σ_{t=1}^{R} (bw p t − 2)` over the first `R`
block boundaries. -/
noncomputable def frontPay (p : HPath k) (R : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc 1 R, (bw p t - 2)

/-- `(|p| − k·R) ⌈/⌉ k = |p| ⌈/⌉ k − R` for `k·R ≤ |p|`. -/
theorem ceil_blocks_sub_mul (hk : 1 ≤ k) {p : HPath k} {R : ℕ}
    (hR : k * R ≤ p.numVerts) :
    (p.numVerts - k * R) ⌈/⌉ k = p.numVerts ⌈/⌉ k - R :=
  ProofsRigid.ceilDiv_sub_mul hk p.numVerts_pos hR

/-- If `R` is below the block count then the block boundary `k·R` is interior. -/
theorem mul_lt_numVerts_of_lt_ceil (hk : 1 ≤ k) {p : HPath k} {R : ℕ}
    (hR : R < p.numVerts ⌈/⌉ k) : k * R < p.numVerts := by
  have h0 := p.numVerts_pos
  rw [Proved.ceilDiv_succ_pred h0 hk] at hR
  have hRle : R ≤ (p.numVerts - 1) / k := by omega
  have hle : k * R ≤ k * ((p.numVerts - 1) / k) := Nat.mul_le_mul_left k hRle
  have hkey := Nat.div_add_mod (p.numVerts - 1) k
  omega

/-- One extra excess step strictly raises `G` by at least one (in fact by `k−2`). -/
theorem G_succ_ge (hk : 4 ≤ k) (x : ℕ) : G k x + 1 ≤ G k (x + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  have hd : 0 < m + 2 := by omega
  simp only [G, show m + 4 - 1 = m + 3 from rfl, show m + 4 - 2 = m + 2 from rfl]
  -- G (x) = (x+1)*(m+3) - x/(m+2);  G (x+1) = (x+2)*(m+3) - (x+1)/(m+2)
  have hpoly : (x + 1 + 1) * (m + 3) = (x + 1) * (m + 3) + (m + 3) := by ring
  have hdiv : (x + 1) / (m + 2) ≤ x / (m + 2) + 1 := by
    calc (x + 1) / (m + 2) ≤ (x + (m + 2)) / (m + 2) := Nat.div_le_div_right (by omega)
      _ = x / (m + 2) + 1 := Nat.add_div_right x hd
  have hBx : x / (m + 2) ≤ x := Nat.div_le_self _ _
  have hP1 : x + 1 ≤ (x + 1) * (m + 3) := Nat.le_mul_of_pos_right _ (by omega)
  have hBx1 : (x + 1) / (m + 2) ≤ x + 1 := Nat.div_le_self _ _
  omega

/-- Dropping `k−1` excess (period plus a chart boundary) costs at most `G`-value
`(k−1)(k−2)`. -/
theorem G_drop_N (hk : 4 ≤ k) {E : ℕ} (hE : k - 1 ≤ E) :
    (k - 1) * (k - 2) + G k (E - (k - 1)) ≤ G k E := by
  have hE2 : k - 2 ≤ E := by omega
  have hper : G k E = G k (E - (k - 2)) + Mper k := ProofsInduction.G_period hk hE2
  have hstep : G k (E - (k - 1)) + 1 ≤ G k (E - (k - 2)) := by
    have heq : E - (k - 2) = (E - (k - 1)) + 1 := by omega
    rw [heq]; exact G_succ_ge hk (E - (k - 1))
  have hMper : Mper k = (k - 1) * (k - 2) - 1 := rfl
  have hMpos : 1 ≤ (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
  omega

/-- In the period region a block count `≤ (k−1)(k−2)` is already `≤ G k E`. -/
theorem G_small_blocks (hk : 4 ≤ k) {E b : ℕ}
    (hE : k - 2 ≤ E) (hb : b ≤ (k - 1) * (k - 2)) : b ≤ G k E := by
  have hmono : G k (k - 2) ≤ G k E := ProofsInduction.G_mono hk hE
  have hge : (k - 1) * (k - 2) ≤ G k (k - 2) := by
    rw [ProofsInduction.G_period hk (le_refl (k - 2)), Nat.sub_self, ProofsPotential.Mper]
    have hg0 : 1 ≤ G k 0 := by
      rw [ProofsInduction.G_base (show (3 : ℕ) ≤ k by omega) (show (0 : ℕ) ≤ k - 3 by omega)]
      have := Nat.mul_pos (show 0 < 0 + 1 by omega) (show 0 < k - 1 by omega); omega
    have hQ : 1 ≤ (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
    omega
  exact le_trans hb (le_trans hge hmono)

/-! ## §4. Prefix-pay / suffix bookkeeping -/

/-- The block count of a block-aligned suffix drops by exactly `R`. -/
theorem suffix_blockCeil (hk : 1 ≤ k) {p q : HPath k} {R : ℕ}
    (hR : k * R < p.numVerts) (hq : q.verts = p.verts.drop (k * R)) :
    q.numVerts ⌈/⌉ k = p.numVerts ⌈/⌉ k - R := by
  have hlen : q.numVerts = p.numVerts - k * R := by
    simp only [numVerts, hq, List.length_drop]
  rw [hlen]
  exact ceil_blocks_sub_mul hk (le_of_lt hR)

/-- The front-pay over the first `R` boundaries is dominated by the per-edge excess of the
first `k·R` edges (the boundary edges are a subset). -/
theorem frontPay_le_split_sum (hk : 1 ≤ k) (p : HPath k) (R : ℕ) :
    frontPay p R ≤ ∑ j ∈ Finset.range (k * R), perEdgeExc p j := by
  have hterm : ∀ t ∈ Finset.Icc 1 R, bw p t - 2 = perEdgeExc p (k * t - 1) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hkt1 : 1 ≤ k * t := by
      calc 1 ≤ k := hk
        _ = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * t := Nat.mul_le_mul_left k ht.1
    have hkt : k * t - 1 + 1 = k * t := by omega
    rw [ProofsChart.perEdgeExc_eq hk, hkt, bw]
  have hinj : Set.InjOn (fun t => k * t - 1) (Finset.Icc 1 R : Finset ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_Icc] at hx hy
    simp only at hxy
    have hx1 : 1 ≤ k * x := by
      calc 1 ≤ k := hk
        _ = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * x := Nat.mul_le_mul_left k hx.1
    have hy1 : 1 ≤ k * y := by
      calc 1 ≤ k := hk
        _ = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * y := Nat.mul_le_mul_left k hy.1
    have : k * x = k * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [frontPay, Finset.sum_congr rfl hterm]
  have himg : ∑ t ∈ Finset.Icc 1 R, perEdgeExc p (k * t - 1)
      = ∑ j ∈ (Finset.Icc 1 R).image (fun t => k * t - 1), perEdgeExc p j :=
    (Finset.sum_image (f := fun j => perEdgeExc p j) hinj).symm
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro j hj
  rw [Finset.mem_image] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  rw [Finset.mem_Icc] at ht
  rw [Finset.mem_range]
  have hkt : k * t ≤ k * R := Nat.mul_le_mul_left k ht.2
  have hkt1 : 1 ≤ k * t := by
    calc 1 ≤ k := hk
      _ = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * t := Nat.mul_le_mul_left k ht.1
  omega

/-- If the front-pay pays at least `c`, the suffix excess is at most `excess p − c`. -/
theorem suffix_excess_le_of_frontPay (hk : 1 ≤ k) {p q : HPath k}
    (hp : p.Exitless) {R c : ℕ} (hR : k * R < p.numVerts)
    (hq : q.verts = p.verts.drop (k * R)) (hpay : c ≤ frontPay p R) :
    excess q ≤ excess p - c := by
  have hsplit : excess p = (∑ j ∈ Finset.range (k * R), perEdgeExc p j) + excess q :=
    ProofsChart.excess_split hk hp ⟨R, rfl⟩ hR hq
  have hle := frontPay_le_split_sum hk p R
  omega

/-! ## §3. Base counting — the sharp opened-block bound at small excess -/

/-- `excess` as the range-sum of per-edge excess. -/
theorem excess_eq_perEdge (hk : 1 ≤ k) (p : HPath k) :
    excess p = ∑ i ∈ Finset.range (p.numVerts - 1), perEdgeExc p i := by
  rw [ProofsMeta3.excess_eq_sum_edgeWeight hk]
  exact Finset.sum_congr rfl (fun i _ => (ProofsChart.perEdgeExc_eq hk p i).symm)

/-- Number of non-door (weight `≥3`) boundaries among the first `b−1` block boundaries. -/
noncomputable def posBoundaryCount (p : HPath k) (b : ℕ) : ℕ :=
  ((Finset.Icc 1 (b - 1)).filter (fun t => ¬ IsDoor p t)).card

/-- Non-door block boundaries inject into edges each spending `≥1`, so their count is `≤ excess`. -/
theorem posBoundaryCount_le_excess (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (h0 : 0 < p.numVerts) :
    posBoundaryCount p (p.numVerts ⌈/⌉ k) ≤ excess p := by
  have hbT : p.numVerts ⌈/⌉ k - 1 = (p.numVerts - 1) / k := by
    rw [Proved.ceilDiv_succ_pred h0 (by omega), Nat.add_sub_cancel]
  unfold posBoundaryCount
  rw [hbT]
  set T := (p.numVerts - 1) / k with hT
  have hkey : k * T + (p.numVerts - 1) % k = p.numVerts - 1 := by
    rw [hT]; exact Nat.div_add_mod _ _
  have hkTle : k * T ≤ p.numVerts - 1 := by omega
  set S := (Finset.Icc 1 T).filter (fun t => ¬ IsDoor p t) with hS
  have hkt_pos : ∀ t, 1 ≤ t → 1 ≤ k * t := by
    intro t ht1
    calc 1 ≤ k := by omega
      _ = k * 1 := (Nat.mul_one k).symm
      _ ≤ k * t := Nat.mul_le_mul_left k ht1
  have hge1 : ∀ t ∈ S, 1 ≤ perEdgeExc p (k * t - 1) := by
    intro t ht
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨⟨ht1, htT⟩, hnd⟩ := ht
    have hkt1 := hkt_pos t ht1
    have hktle : k * t ≤ k * T := Nat.mul_le_mul_left k htT
    have hktlt : k * t < p.numVerts := by omega
    have hkt : k * t - 1 + 1 = k * t := by omega
    have hbwdef : bw p t = ew k (p.vert (k * t - 1)) (p.vert (k * t)) := rfl
    have hb2 : 2 ≤ bw p t := by
      have hbg := ProofsWindow.boundary_ge_two (by omega : (1 : ℕ) ≤ k) hp (i := k * t - 1)
        (by rw [hkt]; exact hktlt) (by rw [hkt]; exact ⟨t, rfl⟩)
      rw [hkt] at hbg
      rw [hbwdef]; exact hbg
    have hbne : bw p t ≠ 2 := hnd
    rw [ProofsChart.perEdgeExc_eq (by omega : (1 : ℕ) ≤ k), hkt, ← hbwdef]
    omega
  have hinj : Set.InjOn (fun t => k * t - 1) (S : Finset ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_Icc] at hx hy
    simp only at hxy
    have hx1 := hkt_pos x hx.1.1
    have hy1 := hkt_pos y hy.1.1
    have : k * x = k * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hsub : S.image (fun t => k * t - 1) ⊆ Finset.range (p.numVerts - 1) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨t, ht, rfl⟩ := hj
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨⟨ht1, htT⟩, _⟩ := ht
    have hkt1 := hkt_pos t ht1
    have hktle : k * t ≤ k * T := Nat.mul_le_mul_left k htT
    rw [Finset.mem_range]; omega
  calc S.card = ∑ _t ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ t ∈ S, perEdgeExc p (k * t - 1) := Finset.sum_le_sum hge1
    _ = ∑ j ∈ S.image (fun t => k * t - 1), perEdgeExc p j :=
        (Finset.sum_image (f := fun j => perEdgeExc p j) hinj).symm
    _ ≤ ∑ j ∈ Finset.range (p.numVerts - 1), perEdgeExc p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = excess p := (excess_eq_perEdge (by omega) p).symm

/-- Door-run invariant: `t ≤ (#non-doors in 1..t)·(k−1) + doorDepth t` for interior `t`. -/
theorem block_run_bound (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) :
    ∀ t, k * t < p.numVerts →
      t ≤ ((Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s)).card * (k - 1)
          + doorDepth p t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
      intro hlt
      have hltt : k * t < p.numVerts := by
        have : k * t ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega); omega
      have iht := ih hltt
      have hddt : doorDepth p t ≤ k - 2 := ProofsLedger2.doorDepth_le_km2 (by omega) hp t hltt
      have hins : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
        ext s; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnotmem : (t + 1) ∉ (Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s) := by
        rw [Finset.mem_filter, Finset.mem_Icc]; omega
      by_cases hd : IsDoor p (t + 1)
      · have hfilter : (Finset.Icc 1 (t + 1)).filter (fun s => ¬ IsDoor p s)
            = (Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s) := by
          rw [hins, Finset.filter_insert, if_neg (not_not.mpr hd)]
        rw [hfilter, doorDepth_door hd]; omega
      · have hfilter : (Finset.Icc 1 (t + 1)).filter (fun s => ¬ IsDoor p s)
            = insert (t + 1) ((Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s)) := by
          rw [hins, Finset.filter_insert, if_pos hd]
        rw [hfilter, Finset.card_insert_of_notMem hnotmem, doorDepth_not_door hd]
        have hexp : (((Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s)).card + 1) * (k - 1)
            = ((Finset.Icc 1 t).filter (fun s => ¬ IsDoor p s)).card * (k - 1) + (k - 1) := by
          ring
        omega

/-- Block count is at most `(non-door count + 1)·(k−1)`. -/
theorem blocks_le_runs (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts) :
    p.numVerts ⌈/⌉ k ≤ (posBoundaryCount p (p.numVerts ⌈/⌉ k) + 1) * (k - 1) := by
  set b := p.numVerts ⌈/⌉ k with hb
  have hbT : b = (p.numVerts - 1) / k + 1 := Proved.ceilDiv_succ_pred h0 (by omega)
  set T := (p.numVerts - 1) / k with hT
  have hkey : k * T + (p.numVerts - 1) % k = p.numVerts - 1 := by
    rw [hT]; exact Nat.div_add_mod _ _
  have hkTlt : k * T < p.numVerts := by omega
  have hinv := block_run_bound hk hp T hkTlt
  have hddt : doorDepth p T ≤ k - 2 := ProofsLedger2.doorDepth_le_km2 (by omega) hp T hkTlt
  have hpbc : posBoundaryCount p b = ((Finset.Icc 1 T).filter (fun s => ¬ IsDoor p s)).card := by
    unfold posBoundaryCount; rw [hbT, Nat.add_sub_cancel]
  rw [hpbc, hbT]
  have hexp : (((Finset.Icc 1 T).filter (fun s => ¬ IsDoor p s)).card + 1) * (k - 1)
      = ((Finset.Icc 1 T).filter (fun s => ¬ IsDoor p s)).card * (k - 1) + (k - 1) := by ring
  omega

/-- Base case of the induction: at excess `E ≤ k−3`, the block count is `≤ G k E`. -/
theorem base_blockCeil_le_G (hk : 4 ≤ k) {E : ℕ} (hE : E ≤ k - 3)
    {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts) (hpe : excess p = E) :
    p.numVerts ⌈/⌉ k ≤ G k E := by
  have hpbc := posBoundaryCount_le_excess hk hp h0
  have hruns := blocks_le_runs hk hp h0
  rw [hpe] at hpbc
  rw [ProofsInduction.G_base (show (3 : ℕ) ≤ k by omega) hE]
  have hmul : (posBoundaryCount p (p.numVerts ⌈/⌉ k) + 1) * (k - 1) ≤ (E + 1) * (k - 1) :=
    Nat.mul_le_mul (by omega) (le_refl (k - 1))
  exact le_trans hruns hmul

/-! ## §2. The LINK-1 profile hypothesis and the chart-heavy bridge -/

/-- The front-`N`-block chart profile consumed by `ProofsFinale.hpath_chart_heavy`, taken here as
an explicit hypothesis.  A sibling development (`Hunter.ProofsProfile.run_profile_of_front_low`)
discharges it: low front-excess over the first `N = (k−1)(k−2)` block boundaries forces the exact
deterministic chart weights. -/
def ProfileHyp : Prop :=
  ∀ {m : ℕ} {p : HPath (m + 4)}, p.Exitless →
    (m + 4) * ((m + 3) * (m + 2)) < p.numVerts →
    frontPay p (((m + 3) * (m + 2)) - 1) ≤ m + 1 →
    (∀ j i, j ≤ m + 1 → i < m + 2 → bw p (j * (m + 3) + i + 1) = 2) ∧
    (∀ j, j < m + 1 → bw p (j * (m + 3) + (m + 2) + 1) = 3)

/-- From low front-excess over the first `N−1` boundaries, the chart-continuation boundary `N`
is heavy (`bw ≥ 4`).  This is the sole use of `ProfileHyp` + `hpath_chart_heavy`; it is stated in
`k`-form for the `k`-abstract induction, converting internally to the `m = k − 4` form. -/
theorem chart_heavy_of_frontLow (hprof : ProfileHyp) (hk : 4 ≤ k) {p : HPath k}
    (hp : p.Exitless) (hcut : k * ((k - 1) * (k - 2)) < p.numVerts)
    (hlow : frontPay p ((k - 1) * (k - 2) - 1) ≤ k - 3) :
    4 ≤ bw p ((k - 1) * (k - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  have hcut' : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts := hcut
  have hlow' : frontPay p ((m + 3) * (m + 2) - 1) ≤ m + 1 := hlow
  obtain ⟨hbw2, hbw3⟩ := hprof hp hcut' hlow'
  exact ProofsFinale.hpath_chart_heavy hp hcut' hbw2 hbw3

/-! ## §5 (front-pay lower/upper bounds used by the induction step B) -/

/-- `frontPay` telescopes one boundary at a time. -/
theorem frontPay_succ (p : HPath k) (R : ℕ) :
    frontPay p (R + 1) = frontPay p R + (bw p (R + 1) - 2) := by
  rw [frontPay, frontPay, Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ R + 1)]

/-- The front-pay never exceeds the total excess. -/
theorem frontPay_le_excess (hk : 4 ≤ k) {p : HPath k} {R : ℕ}
    (hR : k * R < p.numVerts) : frontPay p R ≤ excess p := by
  have h1 := frontPay_le_split_sum (by omega) p R
  have h2 : ∑ j ∈ Finset.range (k * R), perEdgeExc p j
      ≤ ∑ j ∈ Finset.range (p.numVerts - 1), perEdgeExc p j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
    · exact fun _ _ _ => Nat.zero_le _
  rw [excess_eq_perEdge (by omega)]; omega

/-- Weight-`≥3` boundary count is dominated by the front-pay (each spends `≥1`). -/
theorem heavyCount_le_frontPay (p : HPath k) (R : ℕ) :
    ((Finset.Icc 1 R).filter (fun t => 3 ≤ bw p t)).card ≤ frontPay p R := by
  rw [frontPay]
  set F := (Finset.Icc 1 R).filter (fun t => 3 ≤ bw p t) with hF
  calc F.card = ∑ _t ∈ F, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ t ∈ F, (bw p t - 2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [hF, Finset.mem_filter] at ht
        omega
    _ ≤ ∑ t ∈ Finset.Icc 1 R, (bw p t - 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)

/-- Confinement floor: the first `N−1` boundaries pay at least `k−3`. -/
theorem frontPay_window_ge (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hcut : k * ((k - 1) * (k - 2)) < p.numVerts) :
    k - 3 ≤ frontPay p ((k - 1) * (k - 2) - 1) := by
  set N := (k - 1) * (k - 2) with hNdef
  have hNpos : 1 ≤ N := by rw [hNdef]; exact Nat.mul_pos (by omega) (by omega)
  have hcut' : k * (N - 1) < p.numVerts := by
    have : k * (N - 1) ≤ k * N := Nat.mul_le_mul_left k (by omega)
    omega
  have hwin := ProofsMeta6.window_heavy_count (show 3 ≤ k by omega) hp 0 (N - 1)
    (by rw [Nat.zero_add]; exact hcut')
  simp only [Nat.zero_add] at hwin
  have hpredeq : ((Finset.Icc 1 (N - 1)).filter
        (fun j => 3 ≤ ew k (p.vert (k * j - 1)) (p.vert (k * j))))
      = (Finset.Icc 1 (N - 1)).filter (fun j => 3 ≤ bw p j) := rfl
  rw [hpredeq] at hwin
  have hwm : (N - 1) ⌈/⌉ (k - 1) = k - 2 := by
    rw [hNdef]; exact ProofsMeta6.windowM_ceilDiv (by omega)
  rw [hwm] at hwin
  have hheavy := heavyCount_le_frontPay p (N - 1)
  omega

/-! ## §5. Main strong induction on `E = excess p` -/

/-- **The sharp opened-block bound** `⌈|p|/k⌉ ≤ G k (excess p)`, conditional on `ProfileHyp`.
Strong induction on `E = excess p`, with the base window (`E ≤ k−3`), the small-path window
(`b ≤ N`), and the two recursion branches: step A (period drop, `M = N−1` blocks, `k−2` excess)
and step B (chart drop, `N` blocks, `k−1` excess).  k=5 calibration: `N = 12`, `M = 11`. -/
theorem blockCeil_le_G_excess_frontChart (hprof : ProfileHyp) (hk : 4 ≤ k)
    {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts) :
    p.numVerts ⌈/⌉ k ≤ G k (excess p) := by
  have hk1 : 1 ≤ k := by omega
  have main : ∀ E, ∀ p : HPath k, p.Exitless → 0 < p.numVerts → excess p = E →
      p.numVerts ⌈/⌉ k ≤ G k E := by
    intro E
    induction E using Nat.strong_induction_on with
    | _ E ih =>
        intro p hp h0 hE
        set b := p.numVerts ⌈/⌉ k with hb
        by_cases hbase : E ≤ k - 3
        · exact base_blockCeil_le_G hk hbase hp h0 hE
        · have hEge : k - 2 ≤ E := by omega
          by_cases hsmall : b ≤ (k - 1) * (k - 2)
          · exact G_small_blocks hk hEge hsmall
          · have hNb : (k - 1) * (k - 2) < b := by omega
            have hNpos : 1 ≤ (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
            by_cases hA : k - 2 ≤ frontPay p (Mper k)
            · -- step A: period drop of `M = Mper k` blocks
              have hMval : Mper k = (k - 1) * (k - 2) - 1 := rfl
              have hMb : Mper k < b := by omega
              have hcut : k * Mper k < p.numVerts := mul_lt_numVerts_of_lt_ceil hk1 (by rw [← hb]; exact hMb)
              obtain ⟨q, hqv, hqe⟩ := ProofsChart.suffix_exitless hk1 hp ⟨Mper k, rfl⟩ hcut
              have hxq : excess q ≤ excess p - (k - 2) :=
                suffix_excess_le_of_frontPay hk1 hp hcut hqv hA
              have hqceil : q.numVerts ⌈/⌉ k = b - Mper k := by
                rw [hb]; exact suffix_blockCeil hk1 hcut hqv
              have hlt : excess q < E := by omega
              have hGq := ih (excess q) hlt q hqe q.numVerts_pos rfl
              rw [hqceil] at hGq
              have hmono : G k (excess q) ≤ G k (E - (k - 2)) := G_mono hk (by omega)
              have hper : G k E = G k (E - (k - 2)) + Mper k := G_period hk (by omega)
              omega
            · -- step B: chart drop of `N = (k−1)(k−2)` blocks
              have hlowB : frontPay p ((k - 1) * (k - 2) - 1) ≤ k - 3 := by
                have hMval : Mper k = (k - 1) * (k - 2) - 1 := rfl
                rw [← hMval]; omega
              have hcutN : k * ((k - 1) * (k - 2)) < p.numVerts :=
                mul_lt_numVerts_of_lt_ceil hk1 (by rw [← hb]; exact hNb)
              have hbwN : 4 ≤ bw p ((k - 1) * (k - 2)) :=
                chart_heavy_of_frontLow hprof hk hp hcutN hlowB
              have hfloor : k - 3 ≤ frontPay p ((k - 1) * (k - 2) - 1) :=
                frontPay_window_ge hk hp hcutN
              -- frontPay at `N` telescopes from `N−1`
              have hNeq : (k - 1) * (k - 2) - 1 + 1 = (k - 1) * (k - 2) := by omega
              have hsucc := frontPay_succ p ((k - 1) * (k - 2) - 1)
              rw [hNeq] at hsucc
              have hpayN : k - 1 ≤ frontPay p ((k - 1) * (k - 2)) := by omega
              have hfple : frontPay p ((k - 1) * (k - 2)) ≤ excess p := frontPay_le_excess hk hcutN
              have hEge' : k - 1 ≤ E := by omega
              obtain ⟨q, hqv, hqe⟩ :=
                ProofsChart.suffix_exitless hk1 hp ⟨(k - 1) * (k - 2), rfl⟩ hcutN
              have hxq : excess q ≤ excess p - (k - 1) :=
                suffix_excess_le_of_frontPay hk1 hp hcutN hqv hpayN
              have hqceil : q.numVerts ⌈/⌉ k = b - (k - 1) * (k - 2) := by
                rw [hb]; exact suffix_blockCeil hk1 hcutN hqv
              have hlt : excess q < E := by omega
              have hGq := ih (excess q) hlt q hqe q.numVerts_pos rfl
              rw [hqceil] at hGq
              have hmono : G k (excess q) ≤ G k (E - (k - 1)) := G_mono hk (by omega)
              have hdrop := G_drop_N hk hEge'
              omega
  exact main (excess p) p hp h0 rfl

/-! ## §6 (reverse bridge). `ExcessBlockCeil → TightJumpFree`

The repository has only the forward `TightJumpFree → ExcessBlockCeil`
(`ProofsEndgame.excessBlockCeil_of_tightJumpFree`).  Since the §5 induction proves
`ExcessBlockCeil` directly, we add the reverse bridge to export `TightJumpFreeAll`. -/

theorem tightJumpFree_of_excessBlockCeil (hk : 4 ≤ k)
    (hbc : ProofsRigid.ExcessBlockCeil k) : ProofsEndgame.TightJumpFree k := by
  intro p hp h0 hjump
  set T := (p.numVerts - 1) / k with hT
  have hceil : p.numVerts ⌈/⌉ k = T + 1 := Proved.ceilDiv_succ_pred h0 (by omega)
  have hb := hbc p hp h0
  rw [hceil, hjump] at hb
  omega

theorem tightJumpFreeAll_of_excessBlockCeilAll
    (h : ProofsEndgame.ExcessBlockCeilAll) : ProofsEndgame.TightJumpFreeAll :=
  fun k hk => tightJumpFree_of_excessBlockCeil hk (h k hk)

/-! ## §6. Assembly — `ExcessBlockCeil`/`TightJumpFreeAll` conditional on `ProfileHyp`. -/

/-- `ExcessBlockCeil k` at a fixed `k`, from the strong induction (needs `ProfileHyp`). -/
theorem excessBlockCeil_frontChart (hprof : ProfileHyp) (hk : 4 ≤ k) :
    ProofsRigid.ExcessBlockCeil k := by
  rw [ProofsRigid.blockCeil_iff_G hk]
  exact fun p hp h0 => blockCeil_le_G_excess_frontChart hprof hk hp h0

/-- The global crisp block residual, conditional on `ProfileHyp`. -/
theorem excessBlockCeilAll_frontChart (hprof : ProfileHyp) :
    ProofsEndgame.ExcessBlockCeilAll :=
  fun _k hk => excessBlockCeil_frontChart hprof hk

/-- **The endgame kernel `TightJumpFreeAll`, factored through `ProfileHyp`.** The theorem
`profileHyp_holds` below discharges that interface unconditionally. -/
theorem tightJumpFreeAll_of_profile (hprof : ProfileHyp) :
    ProofsEndgame.TightJumpFreeAll :=
  tightJumpFreeAll_of_excessBlockCeilAll (excessBlockCeilAll_frontChart hprof)

/-- **`ProfileHyp` discharged** by the sibling LINK-1 development
(`Hunter.ProofsProfile.run_profile_of_front_low`).  Its `hlow` is `Finset.sum`-defeq to `frontPay`. -/
theorem profileHyp_holds : ProfileHyp := by
  intro m p hp hN hlow
  exact ProofsProfile.run_profile_of_front_low hp hN hlow

end ProofsLink2

/-! ## The unconditional endgame kernel and headline capstones -/

namespace Proved

/-- **The endgame kernel `TightJumpFreeAll`, UNCONDITIONAL** — the sharp jump-tightness residual of
Hunter's Theorem 2, closed by the §4 excess strong-induction (`ProofsLink2`) with the LINK-1 chart
profile (`ProofsProfile`) discharged. -/
theorem tightJumpFree : ProofsEndgame.TightJumpFreeAll :=
  ProofsLink2.tightJumpFreeAll_of_profile ProofsLink2.profileHyp_holds

/-- **Theorem 2** (`Statements.thm2` conclusion, whole range `k ≥ 3`), UNCONDITIONAL. -/
theorem thm2_unconditional : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  ProofsQED.thm2_final tightJumpFree

/-- The crisp opened-block residual `ExcessBlockCeilAll`, UNCONDITIONAL. -/
theorem excessBlockCeilAll : ProofsEndgame.ExcessBlockCeilAll :=
  ProofsQED.excessBlockCeilAll_of_residual tightJumpFree

end Proved

end Hunter

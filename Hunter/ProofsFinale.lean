/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsChartEq
import Hunter.ProofsChart

/-!
# Hunter Theorem 2 — the FINALE plumbing (`Hunter/ProofsFinale.lean`)

Cross-file assembly over the proved kernels of `ProofsChartEq` (the word-level global rigidity
`tight_is_chart` / `chart_continuation_heavy`, the block-extraction bridge
`blockWord`/`bw_eq_bwt`/`blockWord_distinct`) and the graph-level machinery
(`ProofsChart.excess_split`, `ProofsRigid.Dfr` arithmetic).

This pass delivers the **concrete `HPath` form of the §3 closure**: an exitless path whose first
`N = (k−1)(k−2)` blocks carry the deterministic chart's boundary-weight profile (`k−2` maximal
door runs of `k−1` blocks joined by `k−3` weight-3 τ₃ boundaries) enters its `(N)`-th block by a
boundary of weight `≥ 4`.  This is `chart_continuation_heavy` transported from the word level to
the ledger `bw`, and is exactly the object PROOF.md §4's excess-induction consumes.

Namespace `Hunter.ProofsFinale`.  **Zero `sorry`, zero new axioms.**
-/

namespace Hunter.ProofsFinale

open Hunter ProofsChartEq ProofsRigidity2 ProofsLedger HPath

/-! ## §1. The `HPath`-level §3 closure

`hpath_chart_heavy`: writing `k = m + 4` (so `k−3 = m+1`, `k−2 = m+2`, `k−1 = m+3`,
`N = (k−1)(k−2) = (m+3)(m+2)`), an exitless path whose block boundaries carry the chart's weight
profile on its first `N` blocks — every within-run boundary is a door (`bw = 2`) and every one of
the `k−3` run boundaries is weight `3` — is forced by `chart_continuation_heavy` to enter block
`N` (the first block past the completed chart) by a boundary of weight `≥ 4`. -/

theorem hpath_chart_heavy {m : ℕ} {p : HPath (m + 4)} (hp : p.Exitless)
    (hN : (m + 4) * ((m + 3) * (m + 2)) < p.numVerts)
    (hbw2 : ∀ j i, j ≤ m + 1 → i < m + 2 → bw p (j * (m + 3) + i + 1) = 2)
    (hbw3 : ∀ j, j < m + 1 → bw p (j * (m + 3) + (m + 2) + 1) = 3) :
    4 ≤ bw p ((m + 3) * (m + 2)) := by
  have hk4 : 4 ≤ m + 4 := by omega
  have hk1 : 1 ≤ m + 4 := by omega
  set N := (m + 3) * (m + 2) with hNdef
  -- split the first block's word `w0 = A' ++ [z, b, c]` with `|A'| = m + 1`.
  set w0 := (p.vert 0 : List ℕ) with hw0
  have hw0pw : IsPermWord (m + 4) w0 := (p.vert 0).2
  have hw0len : w0.length = m + 4 := hw0pw.length
  set A' := w0.take (m + 1) with hA'
  have hA'len : A'.length = m + 1 := by rw [hA', List.length_take, hw0len]; omega
  have hdroplen : (w0.drop (m + 1)).length = 3 := by rw [List.length_drop, hw0len]; omega
  obtain ⟨z, b, c, hbc⟩ := List.length_eq_three.mp hdroplen
  have hw0split : w0 = A' ++ [z, b, c] := by
    rw [hA', ← hbc, List.take_append_drop]
  -- the block-entry word function
  set q : ℕ → List ℕ := fun s => blockWord p s with hq
  have hq0 : q 0 = A' ++ [z, b, c] := by
    rw [hq]; show blockWord p 0 = A' ++ [z, b, c]
    rw [blockWord, Nat.mul_zero]; exact hw0split
  -- perm-word at every block
  have hperm : ∀ s, IsPermWord (A'.length + 3) (q s) := by
    intro s; rw [hA'len]
    show IsPermWord (m + 4) (blockWord p s); exact blockWord_isPermWord p s
  -- start is a perm word
  have hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]) := by
    rw [hA'len, ← hw0split]; exact hw0pw
  -- distinctness of block classes (from `no_reentry`)
  have hdist : ∀ s t, s < (A'.length + 2) * (A'.length + 1) →
      t < (A'.length + 2) * (A'.length + 1) → s ≠ t → rotClass (q s) ≠ rotClass (q t) := by
    intro s t hsl htl hst
    rw [hA'len] at hsl htl
    have hsN : (m + 4) * s < p.numVerts := lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left (show s < N by rw [hNdef]; exact hsl) (by omega)) (le_of_lt hN)
    have htN : (m + 4) * t < p.numVerts := lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left (show t < N by rw [hNdef]; exact htl) (by omega)) (le_of_lt hN)
    exact blockWord_distinct hk1 hp hsN htN hst
  -- weight-2 within-run profile
  have hw2 : ∀ j i, j ≤ A'.length → i < A'.length + 1 →
      bwt (A'.length + 3) (q (j * (A'.length + 2) + i)) (q (j * (A'.length + 2) + i + 1)) = 2 := by
    intro j i hj hi
    rw [hA'len] at hj hi ⊢
    have htlt : (m + 4) * (j * (m + 3) + i + 1) < p.numVerts := by
      have hidx : j * (m + 3) + i + 1 ≤ N := by
        have h1 : j * (m + 3) ≤ (m + 1) * (m + 3) := Nat.mul_le_mul_right _ hj
        rw [hNdef]; nlinarith [hj, hi]
      calc (m + 4) * (j * (m + 3) + i + 1) ≤ (m + 4) * N :=
            Nat.mul_le_mul_left _ hidx
        _ < p.numVerts := hN
    have hbe := bw_eq_bwt hk1 hp (t := j * (m + 3) + i + 1) (by omega) htlt
    have : bw p (j * (m + 3) + i + 1) = 2 := hbw2 j i hj hi
    rw [this] at hbe
    rw [show j * (m + 3) + i + 1 - 1 = j * (m + 3) + i from by omega] at hbe
    simp only [hq]; exact hbe.symm
  -- weight-3 run boundaries
  have hw3 : ∀ j, j < A'.length →
      bwt (A'.length + 3) (q (j * (A'.length + 2) + (A'.length + 1)))
        (q (j * (A'.length + 2) + (A'.length + 1) + 1)) = 3 := by
    intro j hj
    rw [hA'len] at hj ⊢
    have htlt : (m + 4) * (j * (m + 3) + (m + 2) + 1) < p.numVerts := by
      have hidx : j * (m + 3) + (m + 2) + 1 ≤ N := by
        have h1 : j * (m + 3) ≤ m * (m + 3) := Nat.mul_le_mul_right _ (by omega)
        rw [hNdef]; nlinarith [hj]
      calc (m + 4) * (j * (m + 3) + (m + 2) + 1) ≤ (m + 4) * N := Nat.mul_le_mul_left _ hidx
        _ < p.numVerts := hN
    have hbe := bw_eq_bwt hk1 hp (t := j * (m + 3) + (m + 2) + 1) (by omega) htlt
    have : bw p (j * (m + 3) + (m + 2) + 1) = 3 := hbw3 j hj
    rw [this] at hbe
    rw [show j * (m + 3) + (m + 2) + 1 - 1 = j * (m + 3) + (m + 2) from by omega] at hbe
    simp only [hq]; exact hbe.symm
  -- freshness of the continuation block `q N`
  have hfresh : ∀ t, t < (A'.length + 2) * (A'.length + 1) →
      rotClass (q ((A'.length + 2) * (A'.length + 1))) ≠ rotClass (q t) := by
    intro t htl
    rw [hA'len] at htl ⊢
    have hNlt : (m + 4) * N < p.numVerts := hN
    have htN : (m + 4) * t < p.numVerts := lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left (show t < N by rw [hNdef]; exact htl) (by omega)) (le_of_lt hN)
    have htlt2 : t < N := by rw [hNdef]; exact htl
    have hne : N ≠ t := by omega
    have := blockWord_distinct hk1 hp hNlt htN hne
    simp only [hq]; simpa [hNdef] using this
  -- fire `chart_continuation_heavy`
  have hheavy := chart_continuation_heavy (A' := A') (z := z) (b := b) (c := c)
    (by rw [hA'len]; omega) hs (q := q) hperm hq0 hdist hw2 hw3 hfresh
  rw [hA'len] at hheavy
  -- transport `bwt` back to the ledger `bw`
  have hNlt : (m + 4) * N < p.numVerts := hN
  have hNeq : (m + 1 + 2) * (m + 1 + 1) = N := by rw [hNdef]
  have hbe := bw_eq_bwt hk1 hp (t := N) (by rw [hNdef]; nlinarith) hNlt
  rw [hNeq, show (m + 1 + 2) * (m + 1 + 1) - 1 = N - 1 from by rw [hNeq]] at hheavy
  simp only [hq] at hheavy
  rw [hbe]
  exact hheavy

end Hunter.ProofsFinale

/-! ## Axiom audit -/
#print axioms Hunter.ProofsFinale.hpath_chart_heavy

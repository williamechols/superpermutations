/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Words
import Hunter.Graph
import Hunter.ProofsExitless
import Hunter.ProofsGreedy2
import Hunter.ProofsClosure3
import Hunter.ProofsRigidity2
import Hunter.ProofsLedger

/-!
# Hunter Theorem 2 — the GLOBAL RIGIDITY INDUCTION (`Hunter/ProofsChartEq.lean`)

This file threads the single-step kernels of `ProofsRigidity2` (weight-2 determinism
`fresh_w2_forced`, the forced step `forced_step`, the counting pigeonhole `runlen_pigeonhole`,
the intra-run assembly `run_forced`) and the closure lemma of `ProofsClosure3`
(`chart_closure`) into the two global facts of `PROOF_S2.md`:

1. **Chart distinctness** (`chart_distinct`): the `(k−1)(k−2)` chart entries
   `C_{j,i} = chartWord A' z b c j i`, `j ≤ n = k−3`, `i ≤ m = k−2`, lie in pairwise distinct
   rotation classes.  Route: the unique marker `c` (last letter) pins the outer rotation, the
   unique marker `b` pins the middle rotation and the index `i`, and `rotate_injOn_lt` on the
   nodup word `A = A' ++ [z]` pins the run index `j` — the two-level `marker_pins` pattern of
   `ProofsGreedy2.gV2_inj`.

2. **The induction** (`tight_is_chart`): an exitless word-path of `N = (k−1)(k−2)` blocks with
   excess exactly `k−3` and pairwise-distinct block classes equals the deterministic chart from
   its start (`PROOF_S2 §4`).

All conventions match `ProofsClosure3`/`ProofsRigidity2`:
`chartWord A' z b c j i = ((A.rotate j ++ [b]).rotate i) ++ [c]` with `A = A' ++ [z]`,
`n := A'.length = k − 3`, `m := n + 1 = k − 2`, `k = A'.length + 3`.

All results are `sorry`-free and introduce no new axioms.
-/

namespace Hunter.ProofsChartEq

open List Hunter
open ProofsClosure3 ProofsRigidity2 ProofsExitless

/-! ## §0. `chartWord` is a permutation word, and the marker letters are fresh -/

/-- `chartWord A' z b c j i` is a list-permutation of the start `A' ++ [z, b, c]`. -/
theorem chartWord_perm (A' : List ℕ) (z b c : ℕ) (j i : ℕ) :
    chartWord A' z b c j i ~ A' ++ [z, b, c] := by
  unfold chartWord
  have h1 : ((A' ++ [z]).rotate j ++ [b]).rotate i ++ [c]
      ~ ((A' ++ [z]).rotate j ++ [b]) ++ [c] :=
    (List.perm_append_right_iff _).mpr (List.rotate_perm _ i)
  refine h1.trans ?_
  have h2 : (A' ++ [z]).rotate j ~ A' ++ [z] := List.rotate_perm _ j
  calc (A' ++ [z]).rotate j ++ [b] ++ [c]
      ~ (A' ++ [z]) ++ [b] ++ [c] := ((h2.append_right [b]).append_right [c])
    _ = A' ++ [z, b, c] := by simp

/-- `chartWord` entries are permutation words when the start is. -/
theorem chartWord_isPermWord {A' : List ℕ} {z b c : ℕ}
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c])) (j i : ℕ) :
    IsPermWord (A'.length + 3) (chartWord A' z b c j i) :=
  hs.perm (chartWord_perm A' z b c j i).symm

/-- The letters split: `A' ++ [z, b, c] = (A' ++ [z]) ++ [b, c]`. -/
theorem start_split (A' : List ℕ) (z b c : ℕ) :
    A' ++ [z, b, c] = (A' ++ [z]) ++ [b, c] := by simp

/-- From a permutation-word start, `A = A' ++ [z]` is duplicate-free. -/
theorem A_nodup {A' : List ℕ} {z b c : ℕ}
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c])) : (A' ++ [z]).Nodup := by
  have hnd := hs.nodup
  rw [start_split] at hnd
  exact (List.nodup_append.mp hnd).1

/-- From a permutation-word start, `b ∉ A = A' ++ [z]`. -/
theorem b_notMem_A {A' : List ℕ} {z b c : ℕ}
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c])) : b ∉ (A' ++ [z]) := by
  have hnd := hs.nodup
  rw [start_split] at hnd
  have hdisj := (List.nodup_append.mp hnd).2.2
  intro hmem
  exact hdisj b hmem b (by simp) rfl

/-! ## §1. Chart distinctness (`PROOF_S2 §4`, the marker-pinning argument) -/

/-- **Chart distinctness.**  The `(k−1)(k−2)` chart entries `chartWord A' z b c j i`
(`j ≤ n = A'.length`, `i ≤ m = A'.length + 1`) lie in pairwise-distinct rotation classes:
if two share a rotation class, their indices coincide.

Route (`PROOF_S2 §4`): the marker `c` is last in every chart entry `W ++ [c]` with `|W| = k−1`,
so equality of rotation classes pins the outer rotation and gives `W = W'`
(`ProofsGreedy2.marker_pins`); the marker `b` is last in `A.rotate j ++ [b]`, so `W = W'`
pins `i = i'` and `A.rotate j = A.rotate j'`; finally `rotate_injOn_lt` on the nodup word
`A = A' ++ [z]` pins `j = j'`. -/
theorem chart_distinct {A' : List ℕ} {z b c : ℕ}
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {j i j' i' : ℕ} (hi : i ≤ A'.length + 1) (hi' : i' ≤ A'.length + 1)
    (hj : j ≤ A'.length) (hj' : j' ≤ A'.length)
    (heq : rotClass (chartWord A' z b c j i) = rotClass (chartWord A' z b c j' i')) :
    j = j' ∧ i = i' := by
  set k := A'.length + 3 with hk
  set A := A' ++ [z] with hA
  have hAlen : A.length = A'.length + 1 := by rw [hA]; simp
  have hAnd : A.Nodup := A_nodup hs
  have hbA : b ∉ A := b_notMem_A hs
  -- outer marker `c`: get `W := (A.rotate j ++ [b]).rotate i = (A.rotate j' ++ [b]).rotate i'`.
  set W := (A.rotate j ++ [b]).rotate i with hW
  set W' := (A.rotate j' ++ [b]).rotate i' with hW'
  have hWlen : W.length = A'.length + 2 := by
    rw [hW, List.length_rotate, List.length_append, List.length_rotate, hAlen]; simp
  have hW'len : W'.length = A'.length + 2 := by
    rw [hW', List.length_rotate, List.length_append, List.length_rotate, hAlen]; simp
  have hcw : chartWord A' z b c j i = W ++ [c] := rfl
  have hcw' : chartWord A' z b c j' i' = W' ++ [c] := rfl
  have hnd_c : (W ++ [c]).Nodup := by rw [← hcw]; exact (chartWord_isPermWord hs j i).nodup
  -- from rotClass equality: `∃ t, (W ++ [c]).rotate t = W' ++ [c]`.
  rw [hcw, hcw'] at heq
  obtain ⟨t, ht⟩ := rotClass_eq_iff.mp heq
  have hlen_c : (W ++ [c]).length = k := by rw [List.length_append, hWlen, hk]; simp
  -- reduce the rotation to `t % k ≤ |W|` and apply `marker_pins`.
  have htmod : (W ++ [c]).rotate (t % k) = (W ++ [c]).rotate t := by
    conv_rhs => rw [← List.rotate_mod (W ++ [c]) t]
    rw [hlen_c]
  have ha_le : t % k ≤ W.length := by
    have : t % k < k := Nat.mod_lt _ (by omega)
    rw [hWlen]; omega
  have houter : (W ++ [c]).rotate (t % k) = (W' ++ [c]).rotate 0 := by
    rw [htmod, ht, List.rotate_zero]
  obtain ⟨_, hWW⟩ := ProofsGreedy2.marker_pins hnd_c (hWlen.trans hW'len.symm)
    ha_le (by omega) houter
  -- middle marker `b`: `(A.rotate j ++ [b]).rotate i = (A.rotate j' ++ [b]).rotate i'`.
  rw [hW, hW'] at hWW
  have hnd_b : (A.rotate j ++ [b]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.rotate_perm A j).nodup_iff.mpr hAnd, List.nodup_singleton b, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy; subst hy
    intro hxy; subst hxy
    exact hbA ((List.rotate_perm A j).mem_iff.mp hx)
  have hrjlen : (A.rotate j).length = (A.rotate j').length := by
    rw [List.length_rotate, List.length_rotate]
  have hi_le : i ≤ (A.rotate j).length := by rw [List.length_rotate, hAlen]; omega
  have hi'_le : i' ≤ (A.rotate j').length := by rw [List.length_rotate, hAlen]; omega
  obtain ⟨hii, hAjj⟩ := ProofsGreedy2.marker_pins hnd_b hrjlen hi_le hi'_le hWW
  -- inner: `rotate_injOn_lt` on the nodup `A` pins `j`.
  have hj_lt : j < A.length := by rw [hAlen]; omega
  have hj'_lt : j' < A.length := by rw [hAlen]; omega
  exact ⟨rotate_injOn_lt hAnd hj_lt hj'_lt hAjj, hii⟩

/-! ## §2. Intra-run iteration (the `τ₂` engine, `PROOF_S2 §1`)

`run_iter` is the raw iterate of `fresh_w2_forced`: a block window with pairwise-fresh weight-2
boundaries is `q (t₀ + i) = τ₂ⁱ (q t₀)`.  Unlike `ProofsRigidity2.run_forced` it does *not*
require the start to be in `A ++ [b, c]` form, so it also discharges the freshness of would-be
next-run blocks (`forced_step`'s `hlast`). -/

/-- **Intra-run `τ₂` iteration.**  A window `q t₀, …, q (t₀ + M)` of permutation words whose
consecutive boundaries all have weight `2` and whose consecutive classes are all distinct is
`q (t₀ + i) = τ₂ⁱ (q t₀)`. -/
theorem run_iter {k : ℕ} (hk : 2 ≤ k) {q : ℕ → List ℕ} (t₀ M : ℕ)
    (hperm : ∀ s, IsPermWord k (q s))
    (hdist : ∀ i, i < M → rotClass (q (t₀ + i + 1)) ≠ rotClass (q (t₀ + i)))
    (hw2 : ∀ i, i < M → bwt k (q (t₀ + i)) (q (t₀ + i + 1)) = 2) :
    ∀ i, i ≤ M → q (t₀ + i) = (tau2 k)^[i] (q t₀) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnM : n < M := by omega
    have hstep : q (t₀ + n + 1) = tau2 k (q (t₀ + n)) :=
      fresh_w2_forced hk (hperm _) (hperm _) (hw2 n hnM) (hdist n hnM)
    rw [show t₀ + (n + 1) = t₀ + n + 1 from by ring, hstep, ih (by omega),
      Function.iterate_succ_apply' (tau2 k) n (q t₀)]

/-- `chartWord` in `runW` form (`chartWord A' z b c j i = runW (A.rotate j) b c i`). -/
theorem chartWord_eq_runW (A' : List ℕ) (z b c j i : ℕ) :
    chartWord A' z b c j i = runW ((A' ++ [z]).rotate j) b c i := rfl

/-! ## §3. The induction — a tight exitless block-path IS the chart (`PROOF_S2 §4`)

Given: `N = (k−1)(k−2)` blocks with pairwise-distinct classes, all within-run boundaries weight
`2` and all `k−3` run boundaries weight `3` (the output of the counting layer, `PROOF_S2 §2`),
the whole block-path equals the deterministic τ₂/τ₃ chart from its start.  The run starts satisfy
`q (j·(k−1)) = A.rotate j ++ [b, c] = chartWord … j 0`, with the τ₃ transition supplied by
`ProofsRigidity2.forced_step` (freshness discharged from the global distinctness) and the
intra-run entries by `run_iter`. -/
theorem tight_is_chart {A' : List ℕ} {z b c : ℕ}
    {q : ℕ → List ℕ}
    (hperm : ∀ s, IsPermWord (A'.length + 3) (q s))
    (hstart : q 0 = A' ++ [z, b, c])
    (hdist : ∀ s t, s < (A'.length + 2) * (A'.length + 1) →
        t < (A'.length + 2) * (A'.length + 1) → s ≠ t → rotClass (q s) ≠ rotClass (q t))
    (hw2 : ∀ j i, j ≤ A'.length → i < A'.length + 1 →
        bwt (A'.length + 3) (q (j * (A'.length + 2) + i)) (q (j * (A'.length + 2) + i + 1)) = 2)
    (hw3 : ∀ j, j < A'.length →
        bwt (A'.length + 3) (q (j * (A'.length + 2) + (A'.length + 1)))
          (q (j * (A'.length + 2) + (A'.length + 1) + 1)) = 3) :
    ∀ j i, j ≤ A'.length → i ≤ A'.length + 1 →
      q (j * (A'.length + 2) + i) = chartWord A' z b c j i := by
  set n := A'.length with hn
  set A := A' ++ [z] with hA
  have hk2 : 2 ≤ n + 3 := by omega
  have hAlen : A.length = n + 1 := by
    rw [hA]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  -- polynomial bound: every chart block index is `< N`.
  have hpolyN : (n + 2) * (n + 1) = n * (n + 2) + (n + 1) + 1 := by ring
  have hblt : ∀ jj i, jj ≤ n → i ≤ n + 1 → jj * (n + 2) + i < (n + 2) * (n + 1) := by
    intro jj i hjj hi
    have h1 : jj * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right _ hjj
    omega
  -- `runW`/`chartWord` are permutation words at each run start (via `hperm ∘ hstart`).
  have hAjpw : ∀ jj, IsPermWord (n + 3) (A.rotate jj ++ [b, c]) := by
    intro jj
    have hstart' : IsPermWord (n + 3) (A ++ [b, c]) := by
      have := hperm 0; rw [hstart] at this; rw [hA]; simpa using this
    have hperm2 : A.rotate jj ++ [b, c] ~ A ++ [b, c] :=
      ((List.rotate_perm A jj).append_right [b, c])
    exact hstart'.perm hperm2.symm
  have hArotlen : ∀ jj, (A.rotate jj).length = n + 1 := by
    intro jj; rw [List.length_rotate, hAlen]
  have hArotlen2 : ∀ jj, (A.rotate jj).length = n + 3 - 2 := by
    intro jj; rw [hArotlen jj]; omega
  -- intra-run τ₂ iteration for run `jj`.
  have hiter : ∀ jj, jj ≤ n → ∀ i, i ≤ n + 1 →
      q (jj * (n + 2) + i) = (tau2 (n + 3))^[i] (q (jj * (n + 2))) := by
    intro jj hjj
    refine run_iter hk2 (jj * (n + 2)) (n + 1) hperm ?_ ?_
    · intro i hi
      exact hdist _ _ (hblt jj (i + 1) hjj (by omega)) (hblt jj i hjj (by omega)) (by omega)
    · intro i hi; exact hw2 jj i hjj hi
  -- run entries in `runW` form given the run start value.
  have hEntry : ∀ jj, jj ≤ n → q (jj * (n + 2)) = A.rotate jj ++ [b, c] →
      ∀ i, i ≤ n + 1 → q (jj * (n + 2) + i) = runW (A.rotate jj) b c i := by
    intro jj hjj hst i hi
    rw [hiter jj hjj i hi, hst, ← runW_eq_iter hk2 (hArotlen2 jj) b c i]
  -- the run-start recurrence.
  have hrun : ∀ jj, jj ≤ n → q (jj * (n + 2)) = A.rotate jj ++ [b, c] := by
    intro jj
    induction jj with
    | zero => intro _; rw [Nat.zero_mul, List.rotate_zero, hstart, hA]; simp
    | succ j ih =>
      intro hj1
      have hjn : j < n := by omega
      have hjle : j ≤ n := by omega
      have hst_j : q (j * (n + 2)) = A.rotate j ++ [b, c] := ih hjle
      -- run j entries
      have hEj : ∀ i, i ≤ n + 1 → q (j * (n + 2) + i) = runW (A.rotate j) b c i :=
        hEntry j hjle hst_j
      -- destructure `A.rotate j = a₁ :: As`
      obtain ⟨a₁, As, hAj⟩ : ∃ a₁ As, A.rotate j = a₁ :: As := by
        rcases hr : A.rotate j with _ | ⟨a₁, As⟩
        · exfalso; have := hArotlen j; rw [hr] at this; simp at this
        · exact ⟨a₁, As, rfl⟩
      have hAslen : As.length = n := by
        have := hArotlen j; rw [hAj] at this; simpa using this
      -- `v := q ((j+1)·(n+2))` is the next run's start; note `(j+1)(n+2) = j(n+2)+(n+1)+1`.
      have hnextidx : (j + 1) * (n + 2) = j * (n + 2) + (n + 1) + 1 := by ring
      set v := q ((j + 1) * (n + 2)) with hvdef
      -- run j+1 entries (for `hlast`)
      have hEj1 : ∀ i, i ≤ n + 1 → q ((j + 1) * (n + 2) + i) = (tau2 (n + 3))^[i] v :=
        hiter (j + 1) hj1
      -- last entry of run j and its exit `c :: b :: A.rotate j`.
      have hlastentry : q (j * (n + 2) + (n + 1)) = runW (A.rotate j) b c (n + 1) :=
        hEj (n + 1) (le_refl _)
      have hbexit : bexit (n + 3) (runW (A.rotate j) b c (n + 1)) = c :: b :: A.rotate j := by
        have := bexit_runW_last (k := n + 3) (A := A.rotate j) hk2 (hArotlen2 j) b c
        rwa [hArotlen j] at this
      -- perm word of the exit
      have hrunWpw : IsPermWord (n + 3) (runW (A.rotate j) b c (n + 1)) :=
        isPermWord_runW (hAjpw j) (n + 1)
      have hepw : IsPermWord (n + 3) (c :: b :: a₁ :: As) := by
        have := isPermWord_bexit hrunWpw
        rw [hbexit, hAj] at this; exact this
      -- weight-3 boundary ⇒ overlap
      have hwt3 : wt (n + 3) (c :: b :: a₁ :: As) v = 3 := by
        have h := hw3 j hjn
        rw [bwt, hlastentry, hbexit, hAj] at h
        rw [show j * (n + 2) + (n + 1) + 1 = (j + 1) * (n + 2) from by rw [hnextidx]] at h
        exact h
      have hover : (c :: b :: a₁ :: As).drop 3 = v.take As.length := by
        have hlen : (c :: b :: a₁ :: As).length ≤ n + 3 := by simp [hAslen]
        have hsp := (wt_spec (u := c :: b :: a₁ :: As) (v := v) (by omega) hlen).2.2
        rw [hwt3] at hsp
        rw [hAslen]; simpa using hsp
      -- freshness of `v` (hvfresh) and of `τ₂^{n} v` (hlast) from global distinctness
      have hvfresh : ¬ RunVisited (a₁ :: As) b c (rotClass v) := by
        rintro ⟨ii, hii, hiiv⟩
        rw [List.length_cons, hAslen] at hii
        have hqii : runW (a₁ :: As) b c ii = q (j * (n + 2) + ii) := by
          rw [← hAj, ← hEj ii hii]
        rw [hqii] at hiiv
        exact hdist ((j + 1) * (n + 2)) (j * (n + 2) + ii)
          (by simpa using hblt (j + 1) 0 hj1 (by omega))
          (hblt j ii hjle hii) (by rw [hnextidx]; omega) hiiv
      have hlast : ¬ RunVisited (a₁ :: As) b c
          (rotClass ((tau2 (As.length + 3))^[As.length] v)) := by
        rw [hAslen,
          show (tau2 (n + 3))^[n] v = q ((j + 1) * (n + 2) + n) from (hEj1 n (by omega)).symm]
        rintro ⟨ii, hii, hiiv⟩
        rw [List.length_cons, hAslen] at hii
        have hqii : runW (a₁ :: As) b c ii = q (j * (n + 2) + ii) := by
          rw [← hAj, ← hEj ii hii]
        rw [hqii] at hiiv
        exact hdist ((j + 1) * (n + 2) + n) (j * (n + 2) + ii)
          (hblt (j + 1) n hj1 (by omega)) (hblt j ii hjle hii)
          (by rw [hnextidx]; omega) hiiv
      -- apply the forced step
      have hkey := forced_step (As := As) (a₁ := a₁)
        (show IsPermWord (As.length + 3) (c :: b :: a₁ :: As) by rw [hAslen]; exact hepw)
        (v := v)
        (show IsPermWord (As.length + 3) v by rw [hAslen]; exact hperm ((j + 1) * (n + 2)))
        hover hvfresh hlast
      -- τ₃ target is the next run start
      rw [hkey, runW_zero, ← hAj, List.rotate_rotate]
  -- assemble the full chart equality
  intro j i hj hi
  rw [hEntry j hj (hrun j hj) i hi, chartWord_eq_runW]

/-- **Tight chart ⇒ heavy continuation** (the `TightJumpFree` mechanism at word level).  A tight
`N = (k−1)(k−2)`-block chart whose `(N+1)`-st block `q N` lands in a *fresh* class (distinct from
all `N` chart classes — automatic on a simple path, `blockWord_distinct`) is forced to enter it by
a boundary of weight `≥ 4`: the last chart block's exit is `finalExit`, and `chart_closure` closes
its orbit.  This is exactly the "+2 excess over the demand jump" that refutes tightness. -/
theorem chart_continuation_heavy {A' : List ℕ} {z b c : ℕ}
    (hn : 1 ≤ A'.length)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {q : ℕ → List ℕ}
    (hperm : ∀ s, IsPermWord (A'.length + 3) (q s))
    (hstart : q 0 = A' ++ [z, b, c])
    (hdist : ∀ s t, s < (A'.length + 2) * (A'.length + 1) →
        t < (A'.length + 2) * (A'.length + 1) → s ≠ t → rotClass (q s) ≠ rotClass (q t))
    (hw2 : ∀ j i, j ≤ A'.length → i < A'.length + 1 →
        bwt (A'.length + 3) (q (j * (A'.length + 2) + i)) (q (j * (A'.length + 2) + i + 1)) = 2)
    (hw3 : ∀ j, j < A'.length →
        bwt (A'.length + 3) (q (j * (A'.length + 2) + (A'.length + 1)))
          (q (j * (A'.length + 2) + (A'.length + 1) + 1)) = 3)
    (hfresh : ∀ t, t < (A'.length + 2) * (A'.length + 1) →
        rotClass (q ((A'.length + 2) * (A'.length + 1))) ≠ rotClass (q t)) :
    4 ≤ bwt (A'.length + 3) (q ((A'.length + 2) * (A'.length + 1) - 1))
          (q ((A'.length + 2) * (A'.length + 1))) := by
  set n := A'.length with hn'
  have hpolyN : (n + 2) * (n + 1) = n * (n + 2) + (n + 1) + 1 := by ring
  have hLidx : (n + 2) * (n + 1) - 1 = n * (n + 2) + (n + 1) := by omega
  have hblt : ∀ jj i, jj ≤ n → i ≤ n + 1 → jj * (n + 2) + i < (n + 2) * (n + 1) := by
    intro jj i hjj hi
    have h1 : jj * (n + 2) ≤ n * (n + 2) := Nat.mul_le_mul_right _ hjj
    omega
  have hchart := tight_is_chart hperm hstart hdist hw2 hw3
  have hlast : q (n * (n + 2) + (n + 1)) = chartWord A' z b c n (n + 1) :=
    hchart n (n + 1) (le_refl _) (le_refl _)
  -- the last chart block's exit is the `finalExit`.
  have hbexit_last :
      bexit (n + 3) (chartWord A' z b c n (n + 1)) = ProofsClosure3.finalExit A' z b c := by
    have hlen : (ProofsClosure3.finalExit A' z b c).length = n + 3 := by
      simp [ProofsClosure3.finalExit]; omega
    rw [bexit, ← ProofsClosure3.finalExit_rotate1, List.rotate_rotate,
      show 1 + (n + 3 - 1) = (ProofsClosure3.finalExit A' z b c).length by rw [hlen]; omega,
      List.rotate_length]
  -- the fresh continuation is not a visited chart class.
  have hvis : ¬ ProofsClosure3.VisitedByChart A' z b c (rotClass (q ((n + 2) * (n + 1)))) := by
    rintro ⟨j, i, hj, hi, hK⟩
    rw [← hchart j i hj hi] at hK
    exact hfresh (j * (n + 2) + i) (hblt j i hj hi) hK
  rw [hLidx, hlast, bwt, hbexit_last]
  exact ProofsClosure3.chart_closure A' z b c hn hs (hperm _) hvis

/-! ## §4. The concrete `HPath` block extraction (the "block-extraction packaging")

For an exitless `HPath p` the block-entry word at block `t` is `q t := (p.vert (k·t) : List ℕ)`.
This section discharges the three word-level hypotheses of `tight_is_chart` from the concrete
graph object: `q t` is a permutation word (trivially), consecutive block boundaries transport to
the word-level `bwt` (via `block_is_full_cycle` + `sigma_iter_val` — the exit `p.vert (k·t−1)` is
the right rotation of the block start), and distinct blocks land in distinct rotation classes
(`no_reentry`).  These are exactly the ingredients the prior passes recorded as "not assembled
in-tree" (`PROGRESS-qed §5 piece 1`). -/

/-- The block-entry word of an `HPath` at block `t`. -/
def blockWord {k : ℕ} (p : HPath k) (t : ℕ) : List ℕ := (p.vert (k * t) : List ℕ)

/-- `blockWord` is a permutation word. -/
theorem blockWord_isPermWord {k : ℕ} (p : HPath k) (t : ℕ) :
    IsPermWord k (blockWord p t) := (p.vert (k * t)).2

/-- **Boundary-weight bridge.**  The ledger boundary weight `bw p t` equals the word-level
`bwt k (q (t−1)) (q t)`: the last vertex of block `t−1` is the right rotation `bexit` of that
block's entry, so `ProofsLedger.bw` (an `ew` between the last vertex of block `t−1` and the entry
of block `t`) *is* `wt (bexit (q (t−1))) (q t)`. -/
theorem bw_eq_bwt {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts) :
    ProofsLedger.bw p t = bwt k (blockWord p (t - 1)) (blockWord p t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hms : k * (t' + 1) = k * t' + k := by ring
  have hB : k * t' + (k - 1) < p.numVerts := by omega
  -- the exit vertex `p.vert (k·t − 1) = σ^{k−1}(p.vert (k·t'))`.
  have hcyc : p.vert (k * t' + (k - 1)) = sigma^[k - 1] (p.vert (k * t')) :=
    block_is_full_cycle hk hp (B := k * t') (r := k - 1) ⟨t', rfl⟩ (by omega) hB
  have hidx : k * t' + (k - 1) = k * (t' + 1) - 1 := by omega
  rw [hidx] at hcyc
  have hexitword : (p.vert (k * (t' + 1) - 1) : List ℕ) = bexit k (p.vert (k * t') : List ℕ) := by
    rw [hcyc, sigma_iter_val]; rfl
  simp only [ProofsLedger.bw, bwt, ew, blockWord, Nat.add_sub_cancel]
  rw [hexitword]

/-- **Distinct block classes** (from path `Nodup`, via `no_reentry`).  Distinct blocks of an
exitless path land in distinct rotation classes. -/
theorem blockWord_distinct {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {s t : ℕ}
    (hs : k * s < p.numVerts) (ht : k * t < p.numVerts) (hst : s ≠ t) :
    rotClass (blockWord p s) ≠ rotClass (blockWord p t) := by
  wlog hlt : s < t generalizing s t
  · exact (this ht hs hst.symm (by omega)).symm
  have hle : k * s + k ≤ k * t := by
    have h := Nat.mul_le_mul (le_refl k) (show s + 1 ≤ t from by omega)
    simpa [Nat.mul_succ] using h
  have := no_reentry hk hp (B := k * s) (B' := k * t) ⟨s, rfl⟩ hle ht
  simpa [blockWord] using this

end Hunter.ProofsChartEq

/-! ## Axiom audit — every result depends on exactly `{propext, Classical.choice, Quot.sound}` -/

#print axioms Hunter.ProofsChartEq.chart_distinct
#print axioms Hunter.ProofsChartEq.tight_is_chart
#print axioms Hunter.ProofsChartEq.chart_continuation_heavy
#print axioms Hunter.ProofsChartEq.run_iter
#print axioms Hunter.ProofsChartEq.bw_eq_bwt
#print axioms Hunter.ProofsChartEq.blockWord_distinct

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLedger2
import Hunter.ProofsRunExtract
import Hunter.ProofsMF

/-!
# Theorem 2 — the ASSEMBLY (Wave 4)

This file wires the Wave-3 counting deliverables (`ProofsMeta6.window_heavy_count` /
`windowExcess_ge_km3`, the `k−3` floor; `ProofsLedger2.window_incomplete_slack` = L8) into the
σ-frame residual `(MF) = FrontierTightHeavy k`, discharging every case of `(MF)` **except** the
fully-saturated top window.  What remains is a single, strictly smaller named residual
`SaturatedTightHeavy k`.

Namespace `Hunter.ProofsAssembly`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsAssembly

open ProofsSynthesis ProofsMeta6 ProofsLedger ProofsLedger2 ProofsRunExtract ProofsMF
open ProofsRecursion ProofsMeta3 ProofsWindow ProofsConfinement ProofsExcess
open HPath

variable {k : ℕ}

/-! ## §1. The window block-index and the master excess-split identity -/

/-- The first block index of the top `ℓ₀`-window of a recursion-region path: `a = (n−1)/k`
where `n = |p| − ℓ₀` is the prefix length (mirrors `ProofsMeta6.window_heavy3_ge`'s `a`). -/
noncomputable def winA (p : HPath k) : ℕ := (p.numVerts - ell0 k - 1) / k

/-- **Master window-excess split.**  The top `ℓ₀`-window pays at least the sum, over its `M`
block boundaries `a+1 … a+M` (`a = winA p`, `M = (k−1)(k−2)−1`), of each boundary's excess
contribution `bw − 2`:  `excess q + Σ (bw p (a+j) − 2) ≤ excess p`.

Proof: `excess = Σ_i (ew_i − 2)` (`ProofsMeta3.excess_eq_sum_edgeWeight`) splits at the prefix
boundary into `excess q + Σ_{i ∈ [n−1, N−1)} (ew_i − 2)`; the `M` block-boundary edges inject
into `[n−1, N−1)` and every summand `ew_i − 2` is `≥ 0`, so the block-boundary subsum is
dominated. -/
theorem excess_window_split (hk : 3 ≤ k) {p q : HPath k}
    (hlt : k * (k - 1) * (k - 2) < p.numVerts)
    (hprefix : q.verts = p.verts.take (p.numVerts - ell0 k)) :
    excess q + ∑ j ∈ Finset.Icc 1 ((k - 1) * (k - 2) - 1), (bw p (winA p + j) - 2) ≤ excess p := by
  set N := p.numVerts with hNdef
  set n := N - ell0 k with hndef
  set M := (k - 1) * (k - 2) - 1 with hMdef
  -- ℓ₀ facts (as in window_heavy3_ge)
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hkprod : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hPk : k ≤ k * (k - 1) * (k - 2) := by
    have h1 : k * 1 ≤ k * (k - 1) := Nat.mul_le_mul (le_refl k) (by omega)
    have h2 : k * (k - 1) * 1 ≤ k * (k - 1) * (k - 2) := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  have he0lt : ell0 k < N := by rw [he0val]; omega
  have hNsum : N = n + ell0 k := by rw [hndef]; omega
  have hn1 : k < n := by rw [hndef, he0val]; omega
  have hnle : n ≤ N := by omega
  have hqn : q.numVerts = n := by
    have hlen : q.verts.length = (p.verts.take (N - ell0 k)).length := by rw [hprefix]
    have hNl : p.verts.length = N := rfl
    rw [List.length_take, hNl] at hlen
    show q.verts.length = n
    rw [hlen, hndef]; omega
  have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
  have hkM : k * M = ell0 k := by
    have hB1 : (k - 1) * (k - 2) - 1 + 1 = (k - 1) * (k - 2) := by
      have : 1 ≤ (k - 1) * (k - 2) := by nlinarith [show 1 ≤ k - 1 by omega, show 1 ≤ k - 2 by omega]
      omega
    have hstep : k * ((k - 1) * (k - 2) - 1) + k = k * (k - 1) * (k - 2) := by
      calc k * ((k - 1) * (k - 2) - 1) + k = k * ((k - 1) * (k - 2) - 1 + 1) := by ring
        _ = k * ((k - 1) * (k - 2)) := by rw [hB1]
        _ = k * (k - 1) * (k - 2) := by ring
    rw [hMdef, he0val]; omega
  set a := winA p with hadef
  have hn_eq : n - 1 = p.numVerts - ell0 k - 1 := by omega
  have haval : a = (n - 1) / k := by
    rw [hadef]; unfold winA; rw [hn_eq]
  have hdivmod : k * a + (n - 1) % k = n - 1 := by rw [haval]; exact Nat.div_add_mod (n - 1) k
  have hmodlt : (n - 1) % k < k := Nat.mod_lt (n - 1) (by omega)
  have hM_lt : k * (a + M) < N := by
    have hexp : k * (a + M) = k * a + ell0 k := by rw [Nat.mul_add, hkM]
    omega
  -- per-edge summand
  set f : ℕ → ℕ := fun i => ew k (p.vert i) (p.vert (i + 1)) - 2 with hfdef
  -- excess p = Σ_{range (N-1)} f, excess q = Σ_{range (n-1)} f
  have hexcp : excess p = ∑ i ∈ Finset.range (N - 1), f i := excess_eq_sum_edgeWeight (by omega) p
  have hexcq : excess q = ∑ i ∈ Finset.range (n - 1), f i := by
    rw [excess_eq_sum_edgeWeight (by omega) q, hqn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hfdef]
    rw [prefix_vert_eq hprefix hnle (show i < n by omega),
        prefix_vert_eq hprefix hnle (show i + 1 < n by omega)]
  -- split the p-sum at n-1
  have hsplit : ∑ i ∈ Finset.range (N - 1), f i
      = ∑ i ∈ Finset.range (n - 1), f i + ∑ i ∈ Finset.Ico (n - 1) (N - 1), f i := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le (n - 1)) (by omega : n - 1 ≤ N - 1)]
  -- the window sum dominates the block-boundary subsum
  set g : ℕ → ℕ := fun j => k * (a + j) - 1 with hgdef
  have hginj : ∀ x ∈ Finset.Icc 1 M, ∀ y ∈ Finset.Icc 1 M, g x = g y → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    have h1 : 0 < k * (a + x) := Nat.mul_pos (by omega) (by omega)
    have h2 : 0 < k * (a + y) := Nat.mul_pos (by omega) (by omega)
    rw [hgdef] at hxy; dsimp only at hxy
    have : k * (a + x) = k * (a + y) := by omega
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) this
    omega
  have hgsub : (Finset.Icc 1 M).image g ⊆ Finset.Ico (n - 1) (N - 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hjIcc, hij⟩ := hi
    rw [Finset.mem_Icc] at hjIcc
    rw [Finset.mem_Ico, ← hij, hgdef]; dsimp only
    have hlo : k * (a + 1) ≤ k * (a + j) := Nat.mul_le_mul (le_refl k) (by omega)
    have hhi : k * (a + j) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
    have ha1 : k * (a + 1) = k * a + k := by ring
    constructor <;> omega
  have himg : ∑ j ∈ Finset.Icc 1 M, (bw p (a + j) - 2)
      = ∑ i ∈ (Finset.Icc 1 M).image g, f i := by
    rw [Finset.sum_image hginj]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    have e1 : k * (a + j) - 1 + 1 = k * (a + j) := by
      have : 1 ≤ k * (a + j) := by
        have := Nat.mul_pos (show 0 < k by omega) (show 0 < a + j by omega); omega
      omega
    simp only [hfdef, hgdef, bw]
    rw [e1]
  have hle : ∑ i ∈ (Finset.Icc 1 M).image g, f i ≤ ∑ i ∈ Finset.Ico (n - 1) (N - 1), f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hgsub (fun _ _ _ => Nat.zero_le _)
  rw [hexcp, hsplit, ← hexcq, himg]
  omega

/-- The `M = (k−1)(k−2)−1` block boundaries `a+1 … a+M` of the top window all lie below
`numVerts` (`k·(a+M) < |p|`).  This is the range side-condition consumed by `window_heavy_count`
and `window_incomplete_slack`. -/
theorem winA_range (hk : 3 ≤ k) {p : HPath k}
    (hlt : k * (k - 1) * (k - 2) < p.numVerts) :
    k * (winA p + ((k - 1) * (k - 2) - 1)) < p.numVerts := by
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hPk : k ≤ k * (k - 1) * (k - 2) := by
    have h1 : k * 1 ≤ k * (k - 1) := Nat.mul_le_mul (le_refl k) (by omega)
    have h2 : k * (k - 1) * 1 ≤ k * (k - 1) * (k - 2) := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  have he0lt : ell0 k < p.numVerts := by rw [he0val]; omega
  have hkM : k * ((k - 1) * (k - 2) - 1) = ell0 k := by
    have hB1 : (k - 1) * (k - 2) - 1 + 1 = (k - 1) * (k - 2) := by
      have : 1 ≤ (k - 1) * (k - 2) := by nlinarith [show 1 ≤ k - 1 by omega, show 1 ≤ k - 2 by omega]
      omega
    have hstep : k * ((k - 1) * (k - 2) - 1) + k = k * (k - 1) * (k - 2) := by
      calc k * ((k - 1) * (k - 2) - 1) + k = k * ((k - 1) * (k - 2) - 1 + 1) := by ring
        _ = k * ((k - 1) * (k - 2)) := by rw [hB1]
        _ = k * (k - 1) * (k - 2) := by ring
    rw [he0val]; omega
  have hae : winA p = (p.numVerts - ell0 k - 1) / k := rfl
  have hdm : k * winA p + (p.numVerts - ell0 k - 1) % k = p.numVerts - ell0 k - 1 := by
    rw [hae]; exact Nat.div_add_mod _ k
  have hmlt : (p.numVerts - ell0 k - 1) % k < k := Nat.mod_lt _ (by omega)
  have hka_le : k * winA p ≤ p.numVerts - ell0 k - 1 := by omega
  calc k * (winA p + ((k - 1) * (k - 2) - 1))
      = k * winA p + k * ((k - 1) * (k - 2) - 1) := by rw [Nat.mul_add]
    _ = k * winA p + ell0 k := by rw [hkM]
    _ ≤ (p.numVerts - ell0 k - 1) + ell0 k := by omega
    _ < p.numVerts := by omega

/-! ## §2. The saturated residual and the case reduction

The top `ℓ₀`-window is **saturated** when every one of its `M = (k−1)(k−2)−1` block boundaries
is (a) weight `≤ 3` — no heavy `≥ 4` — and (b) either a door or an ejection leaving a *complete*
2-loop (`doorDepth = k−2`).  Every non-saturated tight window is discharged below: a weight-`≥4`
boundary supplies the missing `+1` beyond the `k−3` floor (Case A), an *incomplete* ejection
forces `k−2` weight-`≥3` boundaries via L8 (Case B).  Only the saturated case is left, as the
named residual `SaturatedTightHeavy`. -/

/-- The top-window **saturation** predicate (see the section note). -/
def WindowSaturated (p : HPath k) (a M : ℕ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ M → bw p (a + j) ≤ 3) ∧
  (∀ j, 1 ≤ j → j ≤ M → IsDoor p (a + j) ∨ k - 2 ≤ doorDepth p (a + j - 1))

/-- **The saturated residual `SaturatedTightHeavy k`** — the single remaining case of `(MF)`.
Same hypotheses as `FrontierTightHeavy` plus the extra assumption that the top window is
`WindowSaturated`.  This is strictly weaker than `(MF)`: Cases A/B below discharge every window
that is *not* saturated, unconditionally. -/
def SaturatedTightHeavy (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q →
    WindowSaturated p (winA p) ((k - 1) * (k - 2) - 1) →
    excess q + (k - 2) ≤ excess p

/-- **The reduction of `(MF)` to the saturated residual.**  `SaturatedTightHeavy k` implies the
full `(MF) = FrontierTightHeavy k`.  The three cases of a tight top window:
* **Case A** — a weight-`≥4` boundary: the `k−3` floor plus that boundary's second unit of excess
  give `k−2` (via `excess_window_split` + `window_heavy_count`);
* **Case B** — an incomplete-loop ejection: L8 (`window_incomplete_slack`) forces `k−2`
  weight-`≥3` boundaries directly;
* **Case C** — saturated: handed to `SaturatedTightHeavy`. -/
theorem frontierTightHeavy_of_saturated (hk : 3 ≤ k)
    (hsat : SaturatedTightHeavy k) : FrontierTightHeavy k := by
  intro p q hpe hqe hlt hprefix htight
  set a := winA p with hadef
  set M := (k - 1) * (k - 2) - 1 with hMdef
  have hrange : k * (a + M) < p.numVerts := by rw [hadef, hMdef]; exact winA_range hk hlt
  -- the master split, with a = winA p folded in
  have hsplit := excess_window_split hk hlt hprefix
  rw [← hadef, ← hMdef] at hsplit
  -- the two window finsets (bw-form, defeq to the ew-form the library lemmas produce)
  set W3 := (Finset.filter (fun j => 3 ≤ bw p (a + j)) (Finset.Icc 1 M)).card with hW3
  set H4 := (Finset.filter (fun j => 4 ≤ bw p (a + j)) (Finset.Icc 1 M)).card with hH4
  -- winPay ≥ W3 + H4
  have hpay : W3 + H4 ≤ ∑ j ∈ Finset.Icc 1 M, (bw p (a + j) - 2) := by
    rw [hW3, hH4, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases h3 : 3 ≤ bw p (a + j) <;> by_cases h4 : 4 ≤ bw p (a + j) <;>
      simp only [h3, h4, if_true, if_false] <;> omega
  -- floor: k−3 ≤ W3
  have hfloor : k - 3 ≤ W3 := by
    have h := window_heavy_count hk hpe a M hrange
    rw [hMdef, windowM_ceilDiv hk] at h
    have hcard : (Finset.filter (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))
        (Finset.Icc 1 M)).card = W3 := rfl
    rw [hcard] at h; omega
  by_cases hA : ∃ j, 1 ≤ j ∧ j ≤ M ∧ 4 ≤ bw p (a + j)
  · -- Case A: a weight-≥4 boundary supplies H4 ≥ 1
    obtain ⟨j, hj1, hjM, hj4⟩ := hA
    have hH4pos : 1 ≤ H4 := by
      rw [hH4]
      apply Finset.one_le_card.mpr
      exact ⟨j, by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hj1, hjM⟩, hj4⟩⟩
    omega
  · by_cases hB : ∃ j, 1 ≤ j ∧ j ≤ M ∧ ¬ IsDoor p (a + j) ∧ doorDepth p (a + j - 1) ≤ k - 3
    · -- Case B: incomplete ejection ⇒ L8 gives W3 ≥ k−2
      obtain ⟨s₀, hs01, hs02, hnd, hinc⟩ := hB
      have h := window_incomplete_slack hk hpe a (by rw [← hMdef]; exact hrange)
        s₀ hs01 (by rw [← hMdef]; exact hs02) hnd hinc
      have hcard : (Finset.filter
          (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))
          (Finset.Icc 1 M)).card = W3 := rfl
      rw [← hMdef] at h
      rw [hcard] at h
      omega
    · -- Case C: the window is saturated
      apply hsat p q hpe hqe hlt hprefix htight
      rw [← hadef, ← hMdef]
      refine ⟨fun j hj1 hjM => ?_, fun j hj1 hjM => ?_⟩
      · by_contra hc
        exact hA ⟨j, hj1, hjM, by omega⟩
      · by_cases hd : IsDoor p (a + j)
        · exact Or.inl hd
        · exact Or.inr (by by_contra hc; exact hB ⟨j, hj1, hjM, hd, by omega⟩)

/-! ## §3. Capstones, conditional on the single named residual `SaturatedTightHeavyAll`

`SaturatedTightHeavyAll` (`∀ k ≥ 3, SaturatedTightHeavy k`) is the single Theorem-2-side
hypothesis, *strictly weaker* than the previous residual `FrontierTightHeavyAll = (MF)`: the
reduction `frontierTightHeavy_of_saturated` discharges every non-saturated tight window
unconditionally.  From it we recover, verbatim, the full `(MF)`-conditional capstone chain of
`ProofsMF`. -/

/-- The global saturated residual: `SaturatedTightHeavy k` for every `k ≥ 3`. -/
def SaturatedTightHeavyAll : Prop := ∀ k, 3 ≤ k → SaturatedTightHeavy k

/-- **The residual reduction, globally.**  `SaturatedTightHeavyAll → FrontierTightHeavyAll`. -/
theorem frontierTightHeavyAll_of_saturatedAll (hsat : SaturatedTightHeavyAll) :
    FrontierTightHeavyAll :=
  fun k hk => frontierTightHeavy_of_saturated hk (hsat k hk)

/-- **Theorem 2 from the saturated residual.**  Verbatim `Statements.thm2` conclusion
`j_k(ℓ) ≤ i_k(ℓ)` for every `k ≥ 3` and every `ℓ` with an exitless path. -/
theorem thm2_of_saturated (hsat : SaturatedTightHeavyAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  ProofsMF.thm2_of_MF (frontierTightHeavyAll_of_saturatedAll hsat)

/-- **thm1v2 from the saturated residual** (dashboard capstone, `L(k) ≥ coeff(k)·k! − O(1)`). -/
theorem thm1v2_of_saturated (hsat : SaturatedTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsMF.thm1v2_of_MF (frontierTightHeavyAll_of_saturatedAll hsat) hproof hexists

/-- **thm1v1 from the saturated residual** (superpermutation form,
`L*(k) ≥ coeff(k)·k! + k − O(1)`). -/
theorem thm1v1_of_saturated (hsat : SaturatedTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsMF.thm1v1_of_MF (frontierTightHeavyAll_of_saturatedAll hsat) hproof hexists

/-- **eq-weak from the saturated residual** — the factorial form
`L*(k) ≥ k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)! − O((k−6)!)`. -/
theorem eq_weak_of_saturated (hsat : SaturatedTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsMF.eq_weak_of_MF (frontierTightHeavyAll_of_saturatedAll hsat) hproof hexists

end ProofsAssembly

end Hunter

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsSPrime

/-!
# Theorem 2 — the deficit-band frontier reduced to one uniform window inequality

This file attacks `ExcessFrontierDeficit k` (`ProofsSPrime`), the sole remaining open
sub-goal of Hunter's Theorem 2 (`thm2_of_deficitFrontier` closes everything else).

The contribution is a **complete, sorry-free reduction** of the entire recursion-region
frontier — hence of `ExcessFrontierDeficit k`, hence of `thm2` for every `k` — to a single,
*uniform, local* inequality, `WindowExcess k`:

> every window of `ℓ₀ = k(k−1)(k−2) − k` consecutive vertices of an exitless path carries at
> least `k − 2` units of `≥3`-weight excess.

Concretely (`WindowExcess`): for an exitless `p` with `|p| > k(k−1)(k−2)` and the exitless
prefix `q` of `p` of length `|p| − ℓ₀`, `excess q + (k − 2) ≤ excess p`.

`excessFrontier_of_windowExcess` proves `WindowExcess k → ExcessFrontier k` by strong
induction on `|p|`: the base region is `excess_frontier_base`, and the recursion step peels
one `ℓ₀`-window off the front using the exact `D`-recursion `D(ℓ) = D(ℓ − ℓ₀) + (k − 2)`
(engine: `j_rec_unfold_one`, `k_dvd_ell0`, `ceilDiv_ell0`, `ceilDiv_add_dvd`, `prefix_exitless`).
All the `j`-recursion bookkeeping and the deficit-band case analysis are discharged here; what
remains is exactly the meta-confinement inequality `WindowExcess`, the paper's cut-off
`S'_k`/`α` step (the level-2 count already delivers `k − 3` per window — the eternal `+1`).

Everything below is sorry-free and axiom-clean; `WindowExcess k` is carried as an explicit
hypothesis wherever the (still-open) meta-confinement is needed.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsDeficit

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime Proved
open HPath

variable {k : ℕ}

/-! ## The uniform window inequality (the localized residue) -/

/-- **The window / meta-confinement inequality.**  For every exitless path `p` in the
recursion region and its exitless length-`(|p| − ℓ₀)` prefix `q`, the last `ℓ₀`-window carries
at least `k − 2` units of `≥3`-weight excess: `excess q + (k − 2) ≤ excess p`.

This is Hunter's cut-off `S'_k`/`α` step — the sole content missing for a complete Theorem 2.
The level-2 confinement (`excess_ge_Dbase`) already delivers `k − 3` units per `ℓ₀`-window;
`WindowExcess` is the extra `+1` (the meta-confinement one level up on `k − 1` letters). -/
def WindowExcess (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    excess q + (k - 2) ≤ excess p

/-! ## The reduction: `WindowExcess k → ExcessFrontier k` -/

/-- **The reduction (strong induction on `|p|`).**  `WindowExcess k` implies the full
`ExcessFrontier k`.  Base region: `excess_frontier_base`.  Recursion step: peel one
`ℓ₀`-window, apply the induction hypothesis to the prefix, and close with the exact
`D`-recursion arithmetic (`j_rec_unfold_one`, `ceilDiv_add_dvd`, `ceilDiv_ell0`,
`k_dvd_ell0`). -/
theorem excessFrontier_of_windowExcess (hk : 3 ≤ k) (hw : WindowExcess k) :
    ExcessFrontier k := by
  have main : ∀ ℓ : ℕ, ∀ p : HPath k, p.Exitless → p.numVerts = ℓ →
      j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro p hpe hpℓ
      have h0 : 0 < p.numVerts := p.numVerts_pos
      by_cases hbase : p.numVerts ≤ k * (k - 1) * (k - 2)
      · exact excess_frontier_base hk hpe h0 hbase
      · rw [Nat.not_le] at hbase
        -- arithmetic facts about ℓ₀ and P = k(k-1)(k-2)
        have he0pos : 0 < ell0 k := ell0_pos hk
        have hm : 2 ≤ (k - 1) * (k - 2) := by
          have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
          omega
        have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
        have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
        have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
        have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
        have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
        -- the prefix window
        set n := p.numVerts - ell0 k with hn
        have hn1 : 1 ≤ n := by rw [hn]; omega
        have hnle : n ≤ p.numVerts := by rw [hn]; omega
        have hnlt : n < p.numVerts := by rw [hn]; omega
        have hNsum : p.numVerts = n + ell0 k := by rw [hn]; omega
        obtain ⟨q, hqv, hqe⟩ := prefix_exitless hpe hn1 hnle
        have hqnv : q.numVerts = n := by
          have hlen : p.verts.length = p.numVerts := rfl
          show q.verts.length = n
          rw [hqv, List.length_take, hlen]; omega
        -- induction hypothesis on the prefix
        have hnltℓ : n < ℓ := by rw [← hpℓ]; exact hnlt
        have hIH := ih n hnltℓ q hqe hqnv
        rw [hqnv] at hIH
        -- the window inequality
        have hwin : excess q + (k - 2) ≤ excess p := by
          apply hw p q hpe hqe hbase
          rw [hqv, hn]
        -- j values and ceiling splits
        have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
        have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
          rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd,
              ceilDiv_ell0 hk]
        have hsplit : p.numVerts ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
          rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
        have hjrec : j k p.numVerts = j k n + j k (ell0 k) + 3 := by
          have hr := j_rec_unfold_one hk hbase
          rw [← hn] at hr; exact hr
        -- lower bounds guarding ℕ-subtraction
        have hXn1 : 1 ≤ n ⌈/⌉ k := by
          rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
        have hXe1 : 1 ≤ ell0 k / k :=
          (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
        omega
  intro q hqe h0
  exact main q.numVerts q hqe rfl

/-! ## Consequences: `ExcessFrontierDeficit`, and `thm2` conditional on `WindowExcess` -/

/-- **`WindowExcess k → ExcessFrontierDeficit k`.**  The deficit-band frontier is a weakening
of the full `ExcessFrontier k` (it adds the deficit-band hypothesis `jbase < j`), so it
follows immediately from `excessFrontier_of_windowExcess`.  Discharging `WindowExcess k`
therefore discharges the sole remaining open sub-goal of Theorem 2. -/
theorem excessFrontierDeficit_of_windowExcess (hk : 3 ≤ k) (hw : WindowExcess k) :
    ExcessFrontierDeficit k := by
  intro q hqe h0 _
  exact excessFrontier_of_windowExcess hk hw q hqe h0

/-- **`thm2` conditional on `WindowExcess`.**  Hunter's Theorem 2 (`j_k(ℓ) ≤ i_k(ℓ)`, the
verbatim `Statements.thm2` conclusion) for every `ℓ`, assuming the single meta-confinement
inequality `WindowExcess k`.  This is the exact residue: a sorry-free proof of `WindowExcess k`
completes Theorem 2 for all `k`. -/
theorem thm2_of_windowExcess {k ℓ : ℕ} (hk : 3 ≤ k) (hw : WindowExcess k)
    (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (excessFrontier_of_windowExcess hk hw) hℓ

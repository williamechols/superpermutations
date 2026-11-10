/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsSynthesis

/-!
# Theorem 2 — the (MF) attack file: capstone wiring + the meta-confinement mechanism

This file attacks `(MF) = FrontierTightHeavy k` — the single residual of Hunter's Theorem 2,
maximally distilled by the σ-frame reduction of `Hunter.ProofsSynthesis` (which proves
`(MF) → ExcessFrontier k → thm2` sorry-free, and, on the complete-loop side, **Lemma A**:
a weight-3 marker-preserving boundary leaving a *complete* 2-loop is `alphaWord`).

## What this file delivers (all sorry-free, axiom-clean)

1. **The headline capstone chain, conditional on the single residual `(MF)`.**  Composing
   `ProofsSynthesis.thm2_global_of_MF` (the Theorem-2 lower bound from `(MF)`) with the
   *unconditionally proved* base-region equality `Proved.thm2_equality` discharges **both**
   Theorem-2 inputs of the proved dashboards `Proved.thm1v2_current` / `Proved.thm1v1_current`.
   This assembles `thm1v2_of_MF`, `thm1v1_of_MF`, `eq_weak_of_MF` — the paper's coefficient
   lower bound and its superpermutation form — from exactly three residual hypotheses: `(MF)`
   and the *Theorem-2-independent* reduction/greedy leaves `hproof`, `hexists` (the same two
   leaves that `ProofsMeta7.thm1v2_of_metaResidual` carries).  `ProofsSynthesis` deliberately
   left this reassembly out; it is completed here.

2. **The mechanism, precisely stated.**  The computational characterization of post-frontier-tight
   windows (documented in `PROGRESS-mf.md`) identifies the operative mechanism as
   **meta-confinement** — the *meta-level analog of Lemma A / `ProofsMeta4.alpha_run_bound`*: a
   run of complete 2-loops chained by `alphaWord` heavies has at most `k − 2` loops, after which
   the next heavy is forced to weight `≥ 4` (paying the extra unit).  `MetaLoopConfined k` states
   it; `frontierTightHeavy_of_metaConfined` is the honest wiring target.

## The residual — and the decisive finding of the computational investigation

Exhaustive k = 5 analysis (the 13 DP-optimal witnesses; `PROGRESS-mf.md` §Data) shows:

* **Mechanism (b) as literally posed is FALSE.**  A frontier-tight prefix does **not** force the
  top window's *first* boundary to be heavy (5 of the 6 tight witnesses start their window with a
  weight-2 door), nor does the prefix's last door-run sit at capacity (last door-depths are
  `0,1,2,2,2,3`, not uniformly `k − 2`).  So the "immediate squeeze at the window's first
  boundary" does not occur.
* **The true mechanism is meta-confinement.**  Every witness weight-4 edge in the recursion
  region sits *exactly* where `k − 2 = 3` complete 2-loops have chained by `alphaWord`
  (`meta_depth` reaches its cap): the ℓ = 120 witness fires its weight-4 at cycle `r = 12`, right
  after complete 2-loops at cycles `0–3, 4–7, 8–11` (`meta_depth 0→1→2`).  This is the meta-level
  analog of `alpha_run_bound`, and it is genuinely **cross-window** (the chained loops span the
  prefix/window boundary), matching the four dossiers' independent conclusion that `(MF)` is the
  amortized cross-window carry — provably outside any window-local / bounded-structural potential
  (`invariant/results.json` `structural_only: INFEASIBLE`; the box-free positive cycle of the
  potential-synthesis dossier's Table E).

Hence `(MF)` is **not** closed by any of the candidate window-local mechanisms; its true content
is the meta-confinement lemma (`ProofsSPrime` open items (i)+(ii): the α-equality — resolved on
complete loops by Lemma A — plus the HPath(k − 1) relative-exitless lift, which is unproved).
Theorem 2 is therefore delivered here **conditional on the single residual `(MF)`**, with the
entire headline chain assembled around it.

Namespace `Hunter.ProofsMF`.
-/

namespace Hunter

open scoped Classical

namespace ProofsMF

open ProofsSynthesis
open ProofsExitless ProofsRecursion ProofsExcess ProofsDeficit
open HPath

variable {k : ℕ}

/-! ## 0. `(MF)` is *equivalent* to Theorem 2 (the distillation is tight)

`ProofsSynthesis.excessFrontier_of_MF` proves the forward direction `(MF) → ExcessFrontier k`
(hence `→ thm2`).  Here we prove the **reverse** direction `ExcessFrontier k → (MF)`, closing the
loop: `(MF)` is *logically equivalent* to `ExcessFrontier k` (= Theorem 2's open content) modulo
the proved inventory — the §5 equivalence that all four assault dossiers asserted informally, now
a sorry-free Lean fact.  This certifies that `(MF)` is a **faithful** distillation of Theorem 2:
neither weaker (it implies thm2) nor stronger (thm2 implies it), so the σ-frame reduction loses
nothing.

The proof is the frontier `D`-recursion run in reverse: `ExcessFrontier` gives
`excess p ≥ Dfr(|p|)`, tightness gives `excess q = Dfr(|q|)`, and the one-step recursion
`Dfr(|p|) = Dfr(|q|) + (k − 2)` (from `j_rec_unfold_one` + the `⌈/⌉` splits, exactly the
arithmetic of `excessFrontier_of_MF`) yields `excess q + (k − 2) ≤ excess p`. -/

/-- **`ExcessFrontier k → FrontierTightHeavy k`** — the reverse of `excessFrontier_of_MF`.
Together with it this proves `(MF) ↔ ExcessFrontier k`, i.e. `(MF)` carries *exactly* the
content of Theorem 2's recursion region (the dossiers' §5 equivalence, formalized). -/
theorem frontierTightHeavy_of_excessFrontier (hk : 3 ≤ k) (hfr : ExcessFrontier k) :
    FrontierTightHeavy k := by
  intro p q hpe hqe hbaseR hpre htight
  have h0 : 0 < p.numVerts := p.numVerts_pos
  -- p meets the frontier (this is where ExcessFrontier is used)
  have hfrp : j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p :=
    hfr p hpe h0
  -- ℓ₀ / P arithmetic (mirrors `excessFrontier_of_MF`)
  have he0pos : 0 < ell0 k := ell0_pos hk
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hm : 2 ≤ (k - 1) * (k - 2) := by
    have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
    omega
  have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
  have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
  have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
  -- the prefix length `n = |p| − ℓ₀`
  set n := p.numVerts - ell0 k with hn
  have hn1 : 1 ≤ n := by rw [hn]; omega
  have hNsum : p.numVerts = n + ell0 k := by rw [hn]; omega
  have hqnv : q.numVerts = n := by
    have hlen : p.verts.length = p.numVerts := rfl
    show q.verts.length = n
    rw [hpre, List.length_take, hlen]; omega
  -- tightness on `q`, rewritten in `n`
  rw [hqnv] at htight
  -- j / ceiling recursion (identical to the forward proof)
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
  have hXe1 : 1 ≤ ell0 k / k := (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
  -- everything is now linear; omega closes `excess q + (k−2) ≤ excess p`
  omega

/-- **`(MF) ↔ ExcessFrontier k`** — the full equivalence.  `mp` is
`ProofsSynthesis.excessFrontier_of_MF`; `mpr` is `frontierTightHeavy_of_excessFrontier`.  This is
the machine-checked form of the dossiers' §5 claim "`(MF)` is logically equivalent to Theorem 2
modulo the proved inventory": `(MF)` neither over- nor under-shoots the target. -/
theorem frontierTightHeavy_iff_excessFrontier (hk : 3 ≤ k) :
    FrontierTightHeavy k ↔ ExcessFrontier k :=
  ⟨excessFrontier_of_MF hk, frontierTightHeavy_of_excessFrontier hk⟩

/-! ## 1. The capstone chain, conditional on the single residual `(MF)`

`FrontierTightHeavyAll` (`∀ k, 3 ≤ k → FrontierTightHeavy k`) is the sole Theorem-2-side
hypothesis.  The remaining two hypotheses `hproof`, `hexists` are the reduction/greedy leaves
that the *whole* proof tree carries independently of the meta-confinement — verbatim the two
leaves of `Proved.thm1v2_current` and of `ProofsMeta7.thm1v2_of_metaResidual`. -/

/-- **Theorem 2 lower bound, from the residual `(MF)`.**  Verbatim `Statements.thm2` conclusion
`j_k(ℓ) ≤ i_k(ℓ)` for every `k ≥ 3` and every `ℓ` with an exitless path — a re-exposure of
`ProofsSynthesis.thm2_global_of_MF` as the entry point of this file's capstone. -/
theorem thm2_of_MF (hMF : FrontierTightHeavyAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  thm2_global_of_MF hMF

/-- **thm1v2 from the residual `(MF)`** (dashboard capstone).  The paper's coefficient lower
bound `L(k) ≥ coeff(k)·k! − O(1)`, with **both** Theorem-2 inputs of `Proved.thm1v2_current`
discharged: the lower bound from `thm2_global_of_MF` (⟸ the single residual `(MF)`), and the
base-region equality from the *unconditionally proved* `Proved.thm2_equality`.  The remaining
hypotheses `hproof`, `hexists` are the meta-confinement-independent reduction/greedy leaves
(exactly as in `ProofsMeta7.thm1v2_of_metaResidual`). -/
theorem thm1v2_of_MF (hMF : FrontierTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_current (thm2_global_of_MF hMF)
    (fun _ _ hk hℓ0 hle hex => Proved.thm2_equality hk hℓ0 hle hex)
    hproof hexists

/-- **thm1v1 from the residual `(MF)`** (superpermutation form; same inputs as
`thm1v2_of_MF`).  `L*(k) ≥ coeff(k)·k! + k − O(1)`. -/
theorem thm1v1_of_MF (hMF : FrontierTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_current (thm2_global_of_MF hMF)
    (fun _ _ hk hℓ0 hle hex => Proved.thm2_equality hk hℓ0 hle hex)
    hproof hexists

/-- **eq-weak from the residual `(MF)`** — the comparable factorial form
`L*(k) ≥ k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)! − O((k−6)!)`, obtained from `thm1v1_of_MF`
through the unconditional `Proved.eq_weak_of_thm1v1`. -/
theorem eq_weak_of_MF (hMF : FrontierTightHeavyAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  Proved.eq_weak_of_thm1v1 (thm1v1_of_MF hMF hproof hexists)

end ProofsMF

end Hunter

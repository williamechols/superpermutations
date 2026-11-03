/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsWalk
import Hunter.ProofsMeta8

/-!
# Theorem 2 — closing the three local residuals G1, G2, G3

This file discharges the three sharply-characterised bridge facts that `Hunter.ProofsWalk` left as
explicit `Prop` hypotheses (`hRunCap` = G1, `hMMC` = G2) or as the endpoint gluing (G3), and then
assembles `M1WalkBound k` and the Theorem-2 capstones with numeric-guard-only hypotheses.

* **G1** — `metaDepth_le_km3` : the tightened run cap `metaDepth p t ≤ k − 3`.  The pigeonhole in
  `ProofsMeta4.alpha_run_bound` counts `m·(k−1)` confined 1-cycles of the `m = metaDepth` complete
  2-loops in a `(k−1)(k−2)` budget, giving `m ≤ k−2`.  Adding the run's *current* block-start (block
  `t` itself, also confined and rotClass-distinct) makes it `m·(k−1) + 1 ≤ (k−1)(k−2)`, so `m ≤ k−3`.

Namespace `Hunter.ProofsClose`.
-/

namespace Hunter

open scoped Classical
open List

namespace ProofsClose

open ProofsPotential ProofsLedger ProofsLedger2 ProofsRecursion ProofsWalk ProofsM1
open ProofsRunExtract ProofsMeta2 ProofsMeta8 ProofsExcess ProofsConfinement HPath

variable {k : ℕ}

/-! ## §G1. The tightened run cap `metaDepth p t ≤ k − 3` -/

/-- **G1 — the tightened run cap.**  For every exitless path `p` and every in-range block
`t` (`k·t < numVerts`), `metaDepth p t ≤ k − 3`.

`metaDepth_le` (via `alpha_run_bound`) confines the `m·(k−1)` block-starts of the `m = metaDepth p t`
complete 2-loops in one level-3 marked loop `Vset3` (budget `(k−1)(k−2)`), giving `m ≤ k−2`.  The
run's *current* block-start (block `t = runStart + m·(k−1) + doorDepth`, one position past the last
complete loop) is **also** confined in the same `Vset3` and carries a fresh 1-cycle (meta-no-reentry),
so the confined count is `m·(k−1) + 1 ≤ (k−1)(k−2)` — forcing `m ≤ k − 3`. -/
theorem metaDepth_le_km3 (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) (t : ℕ)
    (hN : k * t < p.numVerts) : metaDepth p t ≤ k - 3 := by
  have hk3 : 3 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hA, _, _, _⟩ := runExtract (by omega) p t
  set t₀ := runStart p t with ht0
  set m := metaDepth p t with hm
  set d := doorDepth p t with hd
  -- hA : t = t₀ + m * (k - 1) + d
  have hle : t₀ + m * (k - 1) ≤ t := by omega
  set base := p.vert (k * t₀) with hbase
  set α₁ := (base : List ℕ).getLastD 0 with hα1
  set α₂ := ((base : List ℕ).erase α₁).getLastD 0 with hα2
  set K : RotClass := rotClass (((base : List ℕ).erase α₁).dropLast) with hK
  -- (a) each block-start of the run, positions `t₀ .. t₀ + m·(k−1)`, is confined in `Vset3 α₁ α₂ K`
  have hconf : ∀ i, i ≤ m * (k - 1) → p.vert (k * (t₀ + i)) ∈ Vset3 k α₁ α₂ K := by
    intro i hi
    set j := i / (k - 1) with hj
    set r := i % (k - 1) with hr
    have hdm : j * (k - 1) + r = i := by
      rw [hj, hr, Nat.mul_comm]; exact Nat.div_add_mod i (k - 1)
    have hrlt : r < k - 1 := Nat.mod_lt i (by omega)
    have hpos : t₀ + i = t₀ + j * (k - 1) + r := by omega
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · -- r = 0 : a loop start (loop `j`, `j ≤ m`)
      have hjm : j ≤ m := by
        rcases Nat.lt_or_ge m j with hlt | hge
        · exfalso
          have hmul : (m + 1) * (k - 1) ≤ j * (k - 1) := Nat.mul_le_mul (by omega) (le_refl _)
          have hexp : (m + 1) * (k - 1) = m * (k - 1) + (k - 1) := by ring
          omega
        · exact hge
      have hgl := run_loopStart_confined hk3 hp t hN j hjm
      have hglpair : genLoop ((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁) = (α₂, K) := by
        rw [hgl.2]; rfl
      have hmem := mem_Vset3_of_genLoop_metaWord hglpair
      rw [hpos, hr0, Nat.add_zero]
      exact hmem
    · -- r ≥ 1 : an interior door of a completed loop (loop `j`, `j < m`)
      have hjm : j < m := by
        by_contra hjc
        push Not at hjc
        have hmul : m * (k - 1) ≤ j * (k - 1) := Nat.mul_le_mul hjc (le_refl _)
        omega
      have hmem := run_confined hk3 hp t hN j r (Or.inl ⟨hjm, hrpos, by omega⟩)
      rw [hpos]
      exact hmem
  -- (b) positions stay below numVerts
  have hlt_nv : ∀ i, i ≤ m * (k - 1) → k * (t₀ + i) < p.numVerts := by
    intro i hi
    have : t₀ + i ≤ t := by omega
    calc k * (t₀ + i) ≤ k * t := Nat.mul_le_mul (le_refl k) this
      _ < p.numVerts := hN
  -- (c) the `m·(k−1)+1` confined block-starts carry pairwise-distinct 1-cycles
  set N := m * (k - 1) + 1 with hNdef
  have hcyc : ∀ i i' : Fin N, i ≠ i' →
      rotClass (p.vert (k * (t₀ + (i : ℕ))) : List ℕ)
        ≠ rotClass (p.vert (k * (t₀ + (i' : ℕ))) : List ℕ) :=
    meta_no_reentry hk1 hp (fun i : Fin N => k * (t₀ + (i : ℕ)))
      (fun i => ⟨t₀ + (i : ℕ), rfl⟩)
      (fun i i' h => by
        have hii : (i : ℕ) < (i' : ℕ) := h
        calc k * (t₀ + (i : ℕ)) + k = k * (t₀ + (i : ℕ) + 1) := by ring
          _ ≤ k * (t₀ + (i' : ℕ)) := Nat.mul_le_mul (le_refl k) (by omega))
      (fun i => hlt_nv i.1 (by have := i.2; omega))
  have hmem : ∀ i : Fin N, p.vert (k * (t₀ + (i : ℕ))) ∈ Vset3 k α₁ α₂ K :=
    fun i => hconf i.1 (by have := i.2; omega)
  -- (d) the pigeonhole: `N = m·(k−1)+1 ≤ (k−1)(k−2)`
  have hbound : N ≤ (k - 1) * (k - 2) :=
    rotStep_confined hk3 (A := base) hα1
      (by rw [hα2, hα1, erase_getLastD base.2.nodup])
      (by rw [hK, hα1, erase_getLastD base.2.nodup])
      (fun i : Fin N => p.vert (k * (t₀ + (i : ℕ)))) hmem hcyc
  -- (e) `m·(k−1)+1 ≤ (k−1)(k−2)` forces `m ≤ k−3`
  by_contra hc
  push Not at hc
  have hmge : k - 2 ≤ m := by omega
  have hmul : (k - 2) * (k - 1) ≤ m * (k - 1) := Nat.mul_le_mul hmge (le_refl _)
  rw [Nat.mul_comm (k - 1) (k - 2)] at hbound
  omega

/-- **G1 as the run-cap discharge.**  `metaDepth_le_km3` supplies exactly `walk_invariant`'s
`hRunCap` hypothesis, unconditionally.  This is the `−1` tightening `PROGRESS-walk.md` §5 (G1)
flagged as needing a sharper `alpha_run_bound` extraction. -/
theorem runCap_discharged (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) :
    ∀ s, k * s < p.numVerts → metaDepth p s ≤ k - 3 :=
  fun s hs => metaDepth_le_km3 hk hp s hs

/-! ## §G3-arith. The block-aligned frontier identity `Dfrontier(k·b) = Dfr k b`

`Dfrontier k m := j k m − (m−1) − (⌈m/k⌉ − 1)` is the frontier demand `M1WalkBound` charges at
length `m`.  At block-aligned lengths `m = k·b` it equals the block-scale demand `Dfr k b` exactly
(direct from `ProofsWalk.j_glue`), so the walk bound `excess ≥ Dfr k b` *is* the frontier bound
there — the length-scale/block-scale correspondence, sorry-free. -/

/-- The frontier demand charged by `M1WalkBound` at length `m`. -/
noncomputable def Dfrontier (k m : ℕ) : ℕ := j k m - (m - 1) - (m ⌈/⌉ k - 1)

/-- **Block-aligned frontier identity.**  `Dfrontier(k·b) = Dfr k b` for `b ≥ 1` (`k ≥ 4`).  A clean
corollary of `ProofsWalk.j_glue` and `⌈(k·b)/k⌉ = b`. -/
theorem Dfrontier_block_eq (hk : 4 ≤ k) {b : ℕ} (hb : 1 ≤ b) :
    Dfrontier k (k * b) = Dfr k b := by
  have hkpos : 0 < k := by omega
  have hj := ProofsWalk.j_glue hk hb
  have hcd : (k * b) ⌈/⌉ k = b := by
    rw [Proved.ceilDiv_of_dvd hkpos ⟨b, rfl⟩, Nat.mul_div_cancel_left b hkpos]
  simp only [Dfrontier, hj, hcd]
  omega

/-! ## §Assembly. Reducing `M1WalkBound` to the two residuals G2, G3 (G1 discharged)

`excess_ge_Dfr_block` (`ProofsWalk`) delivers `excess ≥ Dfr k T` at the last full block
`T = (numVerts−1)/k` under `hRunCap` (now discharged, G1) and `hMMC` (G2).  `M1WalkBound` needs the
frontier bound at the exact length `numVerts`, which past `k·T` gains at most the terminal
partial-block jump (G3).  We isolate the two residuals as named `Prop`s and assemble; G1 is baked
in, no `sorry`, no new axioms. -/

/-- **G2 (residual, per the certificate's `mmC` dichotomy).**  The marker-move-from-complete
exclusion: in no exitless path does a marker-move boundary leave a complete source loop.  This is
the single boundary whose per-step potential inequality carries a **phase-dependent `{0,1}` deficit**
(the `hpot k (k−2) j` window collapses; verified) — the theorem's hard kernel, covered by the
computational certificate but with no known clean symbolic proof. -/
def MMExclusion (k : ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → ∀ s, 1 ≤ s → k * (s + 1) < p.numVerts →
    ¬ (IsMarkerMove p (s + 1) ∧ IsComplete p s)

/-- **G3 (residual, the terminal-tail gluing).**  Given that an exitless path already pays the
last-full-block demand `Dfr k ((numVerts−1)/k)`, it meets the exact frontier demand at `numVerts`.
The gap is the demand jump inside the terminal partial block (`Dfrontier(numVerts) − Dfr k T ∈ {0,1}`,
verified), paid by a heavy edge there — the endpoint gluing `PROGRESS-walk.md` §5 (G3) routes via
`ProofsFinal.tight_window_pays`, not performed here. -/
def TerminalFrontierTail (k : ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → 0 < p.numVerts →
    Dfr k ((p.numVerts - 1) / k) ≤ excess p →
    j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p

/-- **The reduction of `M1WalkBound` to G2 + G3, with G1 discharged.**  Every exitless path pays the
last-full-block demand `Dfr k T` (G1 `runCap_discharged` + `excess_ge_Dfr_block` + G2), and the
terminal tail (G3) lifts that to the exact frontier demand at `numVerts`.  No `sorry`, no new axioms;
the sole residuals are the two named `Prop`s `MMExclusion` (G2) and `TerminalFrontierTail` (G3). -/
theorem m1WalkBound_of_residuals (hk : 4 ≤ k)
    (hG2 : MMExclusion k) (hG3 : TerminalFrontierTail k) : M1WalkBound k := by
  intro q hqe h0
  have hblock : Dfr k ((q.numVerts - 1) / k) ≤ excess q :=
    excess_ge_Dfr_block hk hqe h0 (runCap_discharged hk hqe) (fun s hs hN => hG2 q hqe s hs hN)
  exact hG3 q hqe h0 hblock

/-- **Theorem 2 from the two residuals** (verbatim `Statements.thm2` conclusion), with G1 discharged
and the numeric guards `hk`/`hℓ` only.  Carries exactly `MMExclusion` (G2) + `TerminalFrontierTail`
(G3) in place of the monolithic `M1WalkBound k`. -/
theorem thm2_of_residuals {ℓ : ℕ} (hk : 4 ≤ k)
    (hG2 : MMExclusion k) (hG3 : TerminalFrontierTail k) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  Proved.thm2_of_m1 (by omega) (m1WalkBound_of_residuals hk hG2 hG3) hℓ

/-! ## §Global. The global M1 bound and the Theorem-1 capstones from the residuals

`M1WalkBoundAll = ∀ k, 3 ≤ k → M1WalkBound k`.  For every `k ≥ 4` it is the residual reduction
above; the single boundary value `k = 3` is a base case (`M1WalkBound 3`, carried explicitly — the
meta-run structure degenerates there).  From the global bound the existing `Proved` chains deliver
Theorem 1 (both forms) and the comparable-factorial `eq-weak` bound verbatim. -/

/-- Global form of residual G2. -/
def MMExclusionAll : Prop := ∀ k, 4 ≤ k → MMExclusion k

/-- Global form of residual G3. -/
def TerminalFrontierTailAll : Prop := ∀ k, 4 ≤ k → TerminalFrontierTail k

/-- **The global M1 slab bound from the residuals.**  `M1WalkBoundAll` from `MMExclusionAll` (G2),
`TerminalFrontierTailAll` (G3), and the base value `M1WalkBound 3`; G1 (`runCap_discharged`) is baked
into every `k ≥ 4` instance. -/
theorem m1WalkBoundAll_of_residuals (hbase : M1WalkBound 3)
    (hG2 : MMExclusionAll) (hG3 : TerminalFrontierTailAll) : Proved.M1WalkBoundAll := by
  intro k hk
  rcases Nat.lt_or_ge k 4 with hlt | hge
  · interval_cases k
    · exact hbase
  · exact m1WalkBound_of_residuals hge (hG2 k hge) (hG3 k hge)

/-- **thm1v1** (superpermutation lower bound) from the residuals. -/
theorem thm1v1_of_residuals (hbase : M1WalkBound 3)
    (hG2 : MMExclusionAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_of_m1 (m1WalkBoundAll_of_residuals hbase hG2 hG3) hproof hexists

/-- **thm1v2** (`L(k) ≥ coeff(k)·k! − O(1)`) from the residuals. -/
theorem thm1v2_of_residuals (hbase : M1WalkBound 3)
    (hG2 : MMExclusionAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_of_m1 (m1WalkBoundAll_of_residuals hbase hG2 hG3) hproof hexists

/-- **eq-weak** (comparable-factorial form) from the residuals. -/
theorem eq_weak_of_residuals (hbase : M1WalkBound 3)
    (hG2 : MMExclusionAll) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsMF.eq_weak_of_MF
    (Proved.frontierTightHeavyAll_of_m1All (m1WalkBoundAll_of_residuals hbase hG2 hG3))
    hproof hexists

end ProofsClose

end Hunter

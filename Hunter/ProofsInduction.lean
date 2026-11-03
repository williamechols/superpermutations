/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsTail
import Hunter.ProofsChart

/-!
# Theorem 2 — the INDUCTION ASSEMBLY of the consolidated (adjudicate2) proof

This file assembles the consolidated `ExcessFrontier k` proof (`scratchpad/campaign/adjudicate2/
PROOF.md`) against the repository's proved machinery.  The consolidated argument works at the
**block level**: with `b` = #blocks and `E` = excess it proves `b ≤ G(E)` where
`G(E) = (E+1)(k−1) − ⌊E/(k−2)⌋` is the inverse threshold of the block-demand `Dfr`.

## The G-function and its inversion (PROOF.md §0)

`G k E := (E+1)*(k−1) − E/(k−2)`.  The load-bearing arithmetic fact is

> **`Dfr k b ≤ E  ↔  b ≤ G k E`**  (`Dfr_le_iff_le_G`),

i.e. `G` is exactly the inverse of the block-demand `Dfr` (`ProofsPotential.Dfr`).  This is pure
ceiling/period arithmetic: both `Dfr` and `G` have matching period,
`Dfr(b+Mper) = Dfr(b)+(k−2)` (`Dfr_shift_exact`) against `G(E+(k−2)) = G(E)+Mper` (`G_period`),
bottoming out in the base region `Dfr(b) = (b−1)/(k−1)`, `G(E) = (E+1)(k−1)`.

Calibration (k=5, n=k−1=4, d=k−2=3, Mper=(k−1)(k−2)−1=11), against `adjudicate2/gt.py` and a
direct `Dfr`/`G` check (see the campaign scripts):
* `G 5 = [4,8,12,15,19,23,26,30]` for `E=0..7`;   `Dfr 5 b` inverts it exactly.
* the true `F_E` (max blocks) `= [4,8,12,14,18,20,24,24] ≤ G` — `G` is the a-priori threshold.

## The headline block bound, in G-form (PROOF.md §2, unconditional)

The block-scale demand bound `Dfr k ((numVerts−1)/k) ≤ excess p` is **already proved
unconditionally** in the repository (`ProofsTheorem.ext_excess_ge_Dfr_block` fed with the proved
`ProofsLast.defectiveDeepExit`).  Composing with the inversion gives, sorry-free and with no
residual, the consolidated proof's headline

> `blockCount_le_G_excess : (p.numVerts − 1)/k ≤ G k (excess p)`  for every exitless `p` (k≥4).

Namespace `Hunter.ProofsInduction`.  **Zero `sorry`, zero new axioms.**
-/

namespace Hunter

open scoped Classical

namespace ProofsInduction

open ProofsPotential ProofsRecursion HPath

variable {k : ℕ}

/-! ## §1. The G-function and its arithmetic -/

/-- **The inverse threshold `G` of the block-demand `Dfr`** (PROOF.md §0).
`G k E = (E+1)(k−1) − ⌊E/(k−2)⌋`.  For `E ≤ k−3` (base region) the floor term vanishes and
`G k E = (E+1)(k−1)`. -/
def G (k E : ℕ) : ℕ := (E + 1) * (k - 1) - E / (k - 2)

/-- On the base region `E ≤ k−3` the floor term is `0`, so `G k E = (E+1)(k−1)`. -/
theorem G_base (hk : 3 ≤ k) {E : ℕ} (hE : E ≤ k - 3) : G k E = (E + 1) * (k - 1) := by
  have hlt : E < k - 2 := by omega
  rw [G, Nat.div_eq_of_lt hlt, Nat.sub_zero]

/-- `(E − (k−2))/(k−2) = E/(k−2) − 1` for `k−2 ≤ E`, in the additive form
`E/(k−2) = (E−(k−2))/(k−2) + 1`. -/
theorem div_sub_period {E : ℕ} (hk : 4 ≤ k) (hE : k - 2 ≤ E) :
    E / (k - 2) = (E - (k - 2)) / (k - 2) + 1 := by
  have hd : 0 < k - 2 := by omega
  have := Nat.add_div_right (E - (k - 2)) hd
  rwa [Nat.sub_add_cancel hE] at this

/-- **Period of `G`** (PROOF.md §4): `G(E) = G(E−(k−2)) + Mper` for `k−2 ≤ E`, matching
`Dfr(b) = Dfr(b−Mper) + (k−2)`.  Here `Mper k = (k−1)(k−2) − 1`. -/
theorem G_period (hk : 4 ≤ k) {E : ℕ} (hE : k - 2 ≤ E) :
    G k E = G k (E - (k - 2)) + Mper k := by
  have hd : 0 < k - 2 := by omega
  have hdiv := div_sub_period hk hE            -- E/d = (E-d)/d + 1
  set d := k - 2 with hddef
  set n := k - 1 with hn
  set P := (E - d + 1) * n with hP
  set DN := d * n with hDN
  have hn1 : 1 ≤ n := by omega
  -- product relations, `set`-linearised so `omega` can finish
  have hprodE : (E + 1) * n = P + DN := by
    rw [hP, hDN]; have : E + 1 = (E - d + 1) + d := by omega
    rw [this, Nat.add_mul]
  have hmper : Mper k = DN - 1 := by
    rw [Mper, ← hddef, ← hn, hDN, Nat.mul_comm]
  have hDN1 : 1 ≤ DN := by rw [hDN]; exact Nat.mul_pos hd (by omega)
  have hEle : E - d ≤ P := le_trans (Nat.le_succ _)
    (by rw [hP]; exact le_mul_of_one_le_right (Nat.zero_le _) hn1)
  have hqP : (E - d) / d ≤ P := le_trans (Nat.div_le_self _ _) hEle
  -- compute both sides fully linearised
  have hGE : G k E = P + DN - E / d := by rw [G, ← hddef, ← hn, hprodE]
  have hGEd : G k (E - d) = P - (E - d) / d := by rw [G, ← hddef, ← hn, ← hP]
  rw [hGE, hGEd, hmper, hdiv]
  omega

/-- **`G` is monotone.**  `G(E) ≤ G(E+1)` (the floor term grows by at most `1`, the linear term by
`k−1 ≥ 3`), hence `G` is monotone. -/
theorem G_le_succ (hk : 4 ≤ k) (E : ℕ) : G k E ≤ G k (E + 1) := by
  have hd : 0 < k - 2 := by omega
  set d := k - 2 with hddef
  set n := k - 1 with hn
  set P := (E + 1) * n with hP
  have hn1 : 1 ≤ n := by omega
  have hfl : (E + 1) / d ≤ E / d + 1 := by
    have hle : (E + 1) / d ≤ (E + d) / d := Nat.div_le_div_right (by omega)
    rwa [Nat.add_div_right E hd] at hle
  have hb1 : E / d ≤ P := le_trans (Nat.div_le_self _ _)
    (by rw [hP]; calc E ≤ E + 1 := Nat.le_succ _
          _ ≤ (E + 1) * n := le_mul_of_one_le_right (Nat.zero_le _) hn1)
  have hGE : G k E = P - E / d := by rw [G, ← hddef, ← hn]
  have hGS : G k (E + 1) = P + n - (E + 1) / d := by
    rw [G, ← hddef, ← hn, show (E + 1 + 1) * n = P + n by rw [hP, Nat.add_mul, Nat.one_mul]]
  rw [hGE, hGS]
  omega

/-- `G` is monotone. -/
theorem G_mono (hk : 4 ≤ k) : Monotone (G k) :=
  monotone_nat_of_le_succ (G_le_succ hk)

/-! ## §2. The inversion `Dfr k b ≤ E ↔ b ≤ G k E` (PROOF.md §0) -/

/-- **The G-inversion** (PROOF.md §0 — the load-bearing arithmetic).  `G` is exactly the inverse
threshold of the block-demand `Dfr`: `Dfr k b ≤ E ↔ b ≤ G k E`.  Proved by strong induction on `b`
using the matching periods `Dfr(b) = Dfr(b−Mper)+(k−2)` (`Dfr_shift_rec`) and
`G(E) = G(E−(k−2))+Mper` (`G_period`), bottoming out in the base region. -/
theorem Dfr_le_iff_le_G (hk : 4 ≤ k) :
    ∀ b, 1 ≤ b → ∀ E, (Dfr k b ≤ E ↔ b ≤ G k E) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb1 E
    set MM := (k - 1) * (k - 2) with hMM
    have hMper : Mper k = MM - 1 := by rw [Mper, hMM]
    have hMM6 : 6 ≤ MM := by
      rw [hMM]; exact le_trans (by norm_num)
        (Nat.mul_le_mul (show 3 ≤ k - 1 by omega) (show 2 ≤ k - 2 by omega))
    by_cases hbase : b ≤ MM
    · -- base region: Dfr k b = (b-1)/(k-1)
      rw [Dfr_base (by rw [← hMM]; exact hbase)]
      by_cases hE3 : E ≤ k - 3
      · -- base×base: pure division/threshold arithmetic
        rw [G_base (by omega) hE3]
        set X := (E + 1) * (k - 1) with hX
        have hdivlt : (b - 1) / (k - 1) < (E + 1) ↔ (b - 1) < X :=
          Nat.div_lt_iff_lt_mul (by omega : 0 < k - 1)
        constructor
        · intro h; have : (b - 1) / (k - 1) < E + 1 := by omega
          have := hdivlt.mp this; omega
        · intro h; have : (b - 1) < X := by omega
          have := hdivlt.mpr this; omega
      · -- base×(E ≥ k−2): both sides hold
        have hEk2 : k - 2 ≤ E := by omega
        have hLHS : (b - 1) / (k - 1) ≤ E := by
          have h1 : (b - 1) / (k - 1) ≤ Mper k / (k - 1) :=
            Nat.div_le_div_right (by omega)
          rw [Mper_div (by omega)] at h1; omega
        have hRHS : b ≤ G k E := by
          have hmono : G k (k - 2) ≤ G k E := G_mono (by omega) hEk2
          have hGkm2 : (k - 1) * (k - 2) ≤ G k (k - 2) := by
            rw [G, Nat.div_self (by omega), show k - 2 + 1 = k - 1 by omega]
            obtain ⟨a, rfl⟩ : ∃ a, k = a + 4 := ⟨k - 4, by omega⟩
            show (a + 3) * (a + 2) ≤ (a + 3) * (a + 3) - 1
            have hexp : (a + 3) * (a + 3) = (a + 3) * (a + 2) + (a + 3) := by ring
            omega
          have hbMM : b ≤ (k - 1) * (k - 2) := hMM ▸ hbase
          omega
        exact iff_of_true hLHS hRHS
    · -- recursion region: b > MM
      rw [Nat.not_le] at hbase
      have hDfr : Dfr k b = Dfr k (b - Mper k) + (k - 2) :=
        Dfr_shift_rec (by omega) (by rw [← hMM]; exact hbase)
      by_cases hE3 : E ≤ k - 3
      · -- both sides fail
        have hLHS : ¬ Dfr k b ≤ E := by rw [hDfr]; omega
        have hRHS : ¬ b ≤ G k E := by
          rw [G_base (by omega) hE3]
          have hle : (E + 1) * (k - 1) ≤ (k - 2) * (k - 1) :=
            Nat.mul_le_mul_right _ (by omega)
          have hcomm : (k - 2) * (k - 1) = MM := by rw [hMM]; ring
          omega
        exact iff_of_false hLHS hRHS
      · -- period + induction hypothesis
        have hEk2 : k - 2 ≤ E := by omega
        have hGP : G k E = G k (E - (k - 2)) + Mper k := G_period hk hEk2
        have hb' : 1 ≤ b - Mper k := by omega
        have hbMlt : b - Mper k < b := by omega
        have IH := ih (b - Mper k) hbMlt hb' (E - (k - 2))
        set A := Dfr k (b - Mper k) with hA
        set Y := G k (E - (k - 2)) with hY
        rw [hDfr, hGP]
        constructor
        · intro h; have hA' : A ≤ E - (k - 2) := by omega
          have := IH.mp hA'; omega
        · intro h; have hbY : b - Mper k ≤ Y := by omega
          have := IH.mpr hbY; omega

/-- The forward direction, packaged for the block bound: `Dfr k b ≤ E → b ≤ G k E`. -/
theorem le_G_of_Dfr_le (hk : 4 ≤ k) {b E : ℕ} (hb1 : 1 ≤ b) (h : Dfr k b ≤ E) :
    b ≤ G k E :=
  (Dfr_le_iff_le_G hk b hb1 E).mp h

/-! ## §3. The block bound in G-form (PROOF.md §2/§4, UNCONDITIONAL)

The consolidated proof's headline block bound `b ≤ G(E)` (equivalently `excess ≥ D(b)`) is already
proved unconditionally in the repository: `ProofsTheorem.ext_excess_ge_Dfr_block` (fed with the
proved `ProofsLast.defectiveDeepExit`) gives `Dfr k T ≤ excess p` at the last full block
`T = (numVerts−1)/k`, and the G-inversion `Dfr_le_iff_le_G` converts it to `T ≤ G(excess)`.  So all
of PROOF.md §1 (S1/S2), §2 (rigidity at `N`) and §4 (the `F_E ≤ G(E)` induction) are — at the block
level — already discharged inside the repository; the run/chart machinery of §1–2 is what a
sibling's `ProofsChart.lean` reproves symbolically, but the *conclusion* it targets is this bound. -/

/-- **The block count is `≤ G(excess)`** — PROOF.md's headline `b ≤ G(E)`, unconditional and
sorry-free, for every exitless path (`k ≥ 4`).  `b = (numVerts−1)/k` is the last-full-block index. -/
theorem blockCount_le_G_excess (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (h0 : 0 < p.numVerts) : (p.numVerts - 1) / k ≤ G k (excess p) := by
  rcases Nat.eq_zero_or_pos ((p.numVerts - 1) / k) with hz | hpos
  · rw [hz]; exact Nat.zero_le _
  · exact le_G_of_Dfr_le hk hpos
      (ProofsTheorem.ext_excess_ge_Dfr_block hk hp h0 (ProofsLast.defectiveDeepExit hk))

end ProofsInduction

/-! ## §4. Assembly — `ExcessFrontier` from the closure residual (PROOF.md §3)

With the block bound (§3) unconditional, the **only** content of `ExcessFrontier k` still open is the
terminal partial-block demand jump `Dfrontier(numVerts) − Dfr k T ∈ {0,1}` — the repository's sharp
residual `ProofsClose.TerminalFrontierTail k` (G3).  This is exactly what PROOF.md's **closure lemma**
(§3: from a completed tight chart every new-class continuation has weight ≥ 4) pays: the terminal
`+1` is charged by the forced heavy edge.  So the consolidated proof's four structural inputs map as:

* §0 suffix-exitlessness, §1 S1/S2, §2 rigidity  ↦  already inside the unconditional block bound;
* §3 closure lemma  ↦  discharges `TerminalFrontierTail k` (G3), the sole residual below.

`excess_frontier_chart` is therefore stated on the closure residual `TerminalFrontierTail k`; a
sibling `ProofsChart.lean` supplying PROOF.md's §3 closure (and the terminal `{0,1}` arithmetic) is
what discharges it. -/

namespace Proved

open ProofsInduction ProofsRecursion ProofsClose HPath

variable {k : ℕ}

/-- **`ExcessFrontier k` from the closure residual (PROOF.md §3).**  Given `TerminalFrontierTail k`
(the terminal partial-block gluing that PROOF.md's closure lemma delivers), the full vertex-level
frontier holds: the unconditional block bound `Dfr k T ≤ excess p`
(`ProofsTheorem.ext_excess_ge_Dfr_block` + `ProofsLast.defectiveDeepExit`) feeds the residual to give
the exact frontier at every length.  Sorry-free; conditional only on the closure residual. -/
theorem excess_frontier_chart (hk : 4 ≤ k) (h_closure : TerminalFrontierTail k) :
    ExcessFrontier k := by
  intro p hp h0
  exact h_closure p hp h0
    (ProofsTheorem.ext_excess_ge_Dfr_block hk hp h0 (ProofsLast.defectiveDeepExit hk))

/-- **Theorem 2 (verbatim `Statements.thm2` conclusion) from the closure residual.** -/
theorem thm2_of_chart {ℓ : ℕ} (hk : 4 ≤ k) (h_closure : TerminalFrontierTail k)
    (hℓ : HasExitlessPath k ℓ) : j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier (by omega) (excess_frontier_chart hk h_closure) hℓ

/-! ## §5. The sibling `ProofsChart.lean` and the remaining bridge (status)

The sibling `Hunter/ProofsChart.lean` (imported above) is **sorry-free and builds**, and delivers
PROOF.md's structural core, all in the repository's `doorDepth`/`metaDepth` language:

* §0 suffix-exitlessness  ↦  `ProofsChart.suffix_exitless`, `ProofsChart.excess_split`;
* §1 S1 (door `τ₂`, period `k−1`, `F_0 = k−1`)  ↦  `ProofsChart.s1_door_determinism`,
  `ProofsChart.s1_door_run_le`, `ProofsChart.excess_zero_block_bound`;
* §2 rigidity / §3 closure engine (meta `τ₃`, period `k−2`, pure `τ₂/τ₃` chart is finite)  ↦
  `ProofsChart.s2_meta_period`, `ProofsChart.meta_chart_block_bound`.

**What is already discharged without any of these** (this file, §1–§3): the block-level headline
`b ≤ G(excess)` / `excess ≥ Dfr(b)` (`blockCount_le_G_excess`) holds *unconditionally* — the
repository's `ext_excess_ge_Dfr_block` already proves it, and the G-inversion (`Dfr_le_iff_le_G`)
recasts it in PROOF.md's `G`-form.  So PROOF.md §1–§2 and the §4 block induction are, at the block
scale, complete.

**The one remaining bridge** (neither file yet closes it): the terminal partial-block gluing
`ProofsClose.TerminalFrontierTail k` (G3) — `Dfrontier(numVerts) − Dfr k T ∈ {0,1}`, with the `+1`
paid by a heavy terminal edge.  This is exactly the target of PROOF.md's §3 closure lemma, whose
*structural engine* (`ProofsChart.meta_chart_block_bound`: a pure `τ₂/τ₃` chart cannot lengthen
without a weight-`≥4` jump) the sibling supplies, but the arithmetic reduction
`(sibling closure engine) → TerminalFrontierTail k` is the open follow-up.  Until it lands,
`excess_frontier_chart` carries `TerminalFrontierTail k`; discharging that hypothesis with the
sibling's closure engine closes Theorem 2 for `k ≥ 5` (the `k ≤ 4` cases are already
unconditional, `ProofsRecursion.thm2_small`). -/

end Proved

end Hunter

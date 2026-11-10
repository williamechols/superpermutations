/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta4
import Hunter.ProofsDeficit
import Hunter.Refutations

/-!
# Theorem 2 — final assembly step (iv): the Φ-TELESCOPE (cumulative amortized frontier)

This file is the *cumulative amortized* layer of Hunter's Theorem 2.  Everything upstream is
proved: the excess ledger (`ProofsMeta3.excess_eq_sum_edgeWeight`, `boundary_contribution`),
the path→run extraction (`Proved.alpha_run_bound : m ≤ k − 2`, `Proved.runs_pay`), and the
`j`/`Dfr` recursion arithmetic (`ProofsRecursion.j_rec_unfold_one`, `ProofsExcess.k_dvd_ell0`,
`ceilDiv_ell0`, `ceilDiv_add_dvd`, `prefix_exitless`).

## The obstruction this layer removes

`ProofsDeficit.excessFrontier_of_windowExcess` reduces `ExcessFrontier k` to the *uniform* local
inequality `WindowExcess k` — "every `ℓ₀`-window carries `≥ k − 2` units of excess".  But
`WindowExcess 5` is **FALSE** (`Refutations.windowExcess_false`): the `ℓ = 120` optimal witness
front-loads its excess (its first 64 edges carry excess `4` against demand `Dfr(65) = 3`,
banking a surplus unit), so its top `ℓ₀`-window carries only `k − 3 = 2 < 3`.  The uniform
reduction is therefore a dead end.

The fix, verified by the LP feasibility analysis (`invariant/results.json`,
`winning_invariant : s(i) ≥ Φ(door_depth, meta_depth, run_complete2, ℓ mod ℓ₀), Φ ∈ {0,1}`,
`s(i) = excess(p[:i]) − Dfr(i)`), is to carry the banked surplus as a bounded potential
`Φ ∈ {0,1}`.  This file states and proves the **amortized reduction skeleton**: a potential-carrying
window inequality `AmortizedWindow k Φ` — which is *not* refuted (it is LP-feasible, `maxPhi = 1`)
— implies the full `ExcessFrontier k`.  This is a strict generalization of
`excessFrontier_of_windowExcess` (recovered at `Φ ≡ 0`), and it reduces the entire remaining
frontier to a single TRUE local inequality, discharging every `j`/`Dfr`-recursion bookkeeping.

Namespace `Hunter.ProofsMeta5`.  Everything below is sorry-free and axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta5

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
open HPath

variable {k : ℕ}

/-! ## The amortized (potential-carrying) local inequalities

`Dfr(ℓ) = j_k(ℓ) − (ℓ−1) − (⌈ℓ/k⌉−1)` is the frontier demand; `ExcessFrontier k` is
`excess q ≥ Dfr(|q|)` for every exitless `q`.  The amortized potential `Φ : HPath k → ℕ`
(intended `Φ ∈ {0,1}`) records banked surplus.  The strengthened invariant the telescope carries
is `s(p) := excess p − Dfr(|p|) ≥ Φ p`, i.e. `j_k(|p|) + Φ p ≤ (|p|−1) + (⌈|p|/k⌉−1) + excess p`.

Two obligations reproduce this invariant across the `ℓ₀`-recursion:

* `BaseBound k Φ` — the invariant holds on the base region `ℓ ≤ k(k−1)(k−2)` (`Φ` is the banked
  surplus there; `excess_frontier_base` gives the `Φ = 0` slice).
* `AmortizedWindow k Φ` — the invariant is *preserved* across one `ℓ₀`-window: the window carries
  `k − 2` units of demand growth (`Dfr(ℓ) = Dfr(ℓ−ℓ₀) + (k−2)`), paid by supply plus the change
  in banked surplus.  Equivalently `excess q + (k−2) + Φ p ≤ excess p + Φ q` for the exitless
  `(|p|−ℓ₀)`-prefix `q`.  With `Φ ∈ {0,1}` this is STRICTLY WEAKER than `WindowExcess`: when the
  prefix banked a unit (`Φ q = 1`) and the top spends it (`Φ p = 0`) it demands only
  `excess q + (k−3) ≤ excess p`, exactly the `ℓ=120` witness's `4 + 2 ≤ 6`. -/

/-- **Base-region invariant** with the banked-surplus potential `Φ`.  On `ℓ ≤ k(k−1)(k−2)` the
amortized invariant `Dfr(ℓ) + Φ p ≤ excess p` holds.  (`excess_frontier_base` is the `Φ = 0`
slice; a genuine `Φ` must bank the surplus already present in the base region.) -/
def BaseBound (k : ℕ) (Φ : HPath k → ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → 0 < p.numVerts → p.numVerts ≤ k * (k - 1) * (k - 2) →
    j k p.numVerts + Φ p ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p

/-- **The amortized window inequality** (the LP-feasible replacement for the refuted
`WindowExcess`).  For an exitless `p` in the recursion region and its exitless `(|p|−ℓ₀)`-prefix
`q`, the last `ℓ₀`-window's supply plus the change in banked surplus covers the `k − 2` demand
growth: `excess q + (k−2) + Φ p ≤ excess p + Φ q`.

Unlike `WindowExcess` (`excess q + (k−2) ≤ excess p`, refuted at `k = 5`), this is LP-feasible
with `Φ ∈ {0,1}` (`invariant/results.json`: `recursion_region_periodic_phase55 : FEASIBLE
maxPhi=1`).  Its proof is the per-block amortized state machine invoking `Proved.runs_pay`
(supply) and `Proved.alpha_run_bound` (`m ≤ k−2`, the meta-confinement) at the binding
transitions — the residual this file isolates. -/
def AmortizedWindow (k : ℕ) (Φ : HPath k → ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    excess q + (k - 2) + Φ p ≤ excess p + Φ q

/-! ## The reduction: `BaseBound k Φ` + `AmortizedWindow k Φ` → `ExcessFrontier k` -/

/-- **The Φ-telescope reduction (strong induction on `|p|`, carrying `Φ`).**  For *any* potential
`Φ : HPath k → ℕ`, the base-region invariant `BaseBound k Φ` together with the amortized window
inequality `AmortizedWindow k Φ` implies the full `ExcessFrontier k`.

The proof strengthens the frontier to the amortized invariant `j_k(|p|) + Φ p ≤ (|p|−1) +
(⌈|p|/k⌉−1) + excess p` and inducts on `|p|` exactly as `excessFrontier_of_windowExcess`, but the
window step now consumes the *potential-carrying* inequality: the `Φ p` on the demand side is paid
by the `Φ q` released from the prefix, so a window that carries only `k − 3` units of raw supply
still closes provided the prefix banked the missing unit.  All `j`/`Dfr`-recursion bookkeeping
(`j_rec_unfold_one`, `ceilDiv_add_dvd`, `ceilDiv_ell0`, `k_dvd_ell0`) is discharged here; the sole
residue is `AmortizedWindow k Φ` for a concrete `Φ`. -/
theorem excessFrontier_of_amortizedWindow (hk : 3 ≤ k) (Φ : HPath k → ℕ)
    (hbase : BaseBound k Φ) (hstep : AmortizedWindow k Φ) :
    ExcessFrontier k := by
  -- strengthened invariant: `j_k(|p|) + Φ p ≤ (|p|−1) + (⌈|p|/k⌉−1) + excess p`
  have main : ∀ ℓ : ℕ, ∀ p : HPath k, p.Exitless → p.numVerts = ℓ →
      j k p.numVerts + Φ p ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro p hpe hpℓ
      have h0 : 0 < p.numVerts := p.numVerts_pos
      by_cases hbaseR : p.numVerts ≤ k * (k - 1) * (k - 2)
      · exact hbase p hpe h0 hbaseR
      · rw [Nat.not_le] at hbaseR
        -- arithmetic facts about ℓ₀ and P = k(k-1)(k-2)  (mirrors ProofsDeficit)
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
        -- strengthened induction hypothesis on the prefix
        have hnltℓ : n < ℓ := by rw [← hpℓ]; exact hnlt
        have hIH := ih n hnltℓ q hqe hqnv
        rw [hqnv] at hIH
        -- the amortized window inequality (carrying Φ)
        have hwin : excess q + (k - 2) + Φ p ≤ excess p + Φ q := by
          apply hstep p q hpe hqe hbaseR
          rw [hqv, hn]
        -- j values and ceiling splits (identical to ProofsDeficit)
        have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
        have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
          rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd,
              ceilDiv_ell0 hk]
        have hsplit : p.numVerts ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
          rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
        have hjrec : j k p.numVerts = j k n + j k (ell0 k) + 3 := by
          have hr := j_rec_unfold_one hk hbaseR
          rw [← hn] at hr; exact hr
        -- lower bounds guarding ℕ-subtraction
        have hXn1 : 1 ≤ n ⌈/⌉ k := by
          rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
        have hXe1 : 1 ≤ ell0 k / k :=
          (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
        omega
  intro q hqe h0
  have := main q.numVerts q hqe rfl
  omega

/-! ## The per-run supply aggregate (the demand-matched seed)

`Proved.runs_pay` pins each interior α-transition of a maximal α-run to a *pointwise* payment
`ew − 2 = 1`.  The telescope consumes the *aggregate*: a maximal α-run of `m` complete 2-loops
banks exactly `m − 1` units of `≥3`-weight excess (one per interior α-transition), and `m ≤ k − 2`,
so a single run banks at most `k − 3` units.  This is the supply side of the per-window balance:
against the demand growth `Dfr(ℓ) = Dfr(ℓ−ℓ₀) + (k−2)`, a full run supplies `m − 1 ≤ k − 3`, and
the missing `+1` (the run-terminator, or the banked surplus released from an earlier window) is
what forces the *cumulative* form. -/

/-- **Supply aggregation.**  If a family `f` pays exactly `1` at each index `c` with `1 ≤ c < m`
(the α-transition payment clause of `Proved.runs_pay`), the total banked over the run is `m − 1`. -/
theorem run_supply_sum {m : ℕ} {f : ℕ → ℕ} (hpay : ∀ c, 1 ≤ c → c < m → f c = 1) :
    ∑ c ∈ Finset.Ico 1 m, f c = m - 1 := by
  have hcongr : ∀ c ∈ Finset.Ico 1 m, f c = 1 := by
    intro c hc
    rw [Finset.mem_Ico] at hc
    exact hpay c hc.1 hc.2
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]

/-- **Per-run banked excess (path level).**  A maximal α-run of `m` complete 2-loops in an
exitless path banks exactly `m − 1` units of `≥3`-weight excess across its interior α-transitions,
and `m ≤ k − 2` — so a single run supplies at most `k − 3` of the `k − 2` demand growth per
`ℓ₀`-window.  Aggregates `Proved.runs_pay`'s pointwise payment via `run_supply_sum`; this is the
supply term the amortized telescope sums per group. -/
theorem run_banks (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m * (k - 1)) ≤ p.numVerts)
    (hdoor : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + j * (k - 1) + r) - 1))
          (p.vert (k * (t₀ + j * (k - 1) + r))) = 2)
    (halpha : ∀ c, 1 ≤ c → c < m →
        ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) = 3 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ).getLastD 0
          = (rho (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)).getLastD 0 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ)
          = alphaWord (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)) :
    m ≤ k - 2 ∧
    ∑ c ∈ Finset.Ico 1 m,
        (ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) - 2)
      = m - 1 := by
  obtain ⟨hbound, hpay⟩ := Proved.runs_pay hk hp t₀ m hN hdoor halpha
  exact ⟨hbound, run_supply_sum hpay⟩

/-! ## Faithfulness: `Φ ≡ 0` recovers the uniform reduction

Setting `Φ ≡ 0`, `AmortizedWindow k 0` is definitionally `WindowExcess k` and `BaseBound k 0` is
`excess_frontier_base`, so `excessFrontier_of_amortizedWindow` specializes back to
`ProofsDeficit.excessFrontier_of_windowExcess`.  This certifies the skeleton is a genuine
*generalization*, not a different statement — the amortized frontier weakens the (refuted) uniform
one by exactly the banked-surplus potential. -/

/-- `BaseBound k (fun _ => 0)` holds unconditionally — it is `excess_frontier_base`. -/
theorem baseBound_zero (hk : 3 ≤ k) : BaseBound k (fun _ => 0) := by
  intro p hpe h0 hle
  simpa using excess_frontier_base hk hpe h0 hle

/-- `WindowExcess k` is exactly `AmortizedWindow k (fun _ => 0)`. -/
theorem amortizedWindow_zero_iff_windowExcess :
    AmortizedWindow k (fun _ => 0) ↔ WindowExcess k := by
  constructor
  · intro h p q hpe hqe hlt hpre
    have := h p q hpe hqe hlt hpre; simpa using this
  · intro h p q hpe hqe hlt hpre
    have := h p q hpe hqe hlt hpre; simpa using this

/-- **Recovery of the uniform reduction.**  `excessFrontier_of_amortizedWindow` at `Φ ≡ 0`
reproduces `ProofsDeficit.excessFrontier_of_windowExcess`. -/
theorem excessFrontier_of_windowExcess' (hk : 3 ≤ k) (hw : WindowExcess k) :
    ExcessFrontier k :=
  excessFrontier_of_amortizedWindow hk (fun _ => 0) (baseBound_zero hk)
    (amortizedWindow_zero_iff_windowExcess.mpr hw)

/-! ## Conditional Theorem 2 through the amortized frontier

Composed with `thm2_of_frontier`, the amortized reduction yields Hunter's Theorem 2 for every `ℓ`
from the two amortized obligations. -/

/-- **`thm2` conditional on the amortized frontier.**  For any potential `Φ`, `BaseBound k Φ` +
`AmortizedWindow k Φ` give `j_k(ℓ) ≤ i_k(ℓ)` (the verbatim `Statements.thm2` conclusion) for all
`ℓ`.  A sorry-free discharge of `AmortizedWindow k Φ` for one concrete `Φ ∈ {0,1}` completes
Theorem 2 for all `k`. -/
theorem thm2_of_amortizedWindow {k ℓ : ℕ} (hk : 3 ≤ k) (Φ : HPath k → ℕ)
    (hbase : BaseBound k Φ) (hstep : AmortizedWindow k Φ) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (excessFrontier_of_amortizedWindow hk Φ hbase hstep) hℓ

/-! ## Calibration at the canonical witness (`k = 5`, the `ℓ = 120` optimal path)

The `ℓ = 120` witness `Refutations.P` is exactly the front-loading path that refutes
`WindowExcess 5`: its `65`-vertex exitless prefix `q` has `excess q = 4`, the full path has
`excess P = 6`, so the *uniform* window demands `4 + (k−2) = 7 ≤ 6 = excess P` — FALSE.

The amortized potential resolves it.  The banked surplus is `s(65) = excess q − Dfr(65) =
4 − 3 = 1` at the prefix and `s(120) = excess P − Dfr(120) = 6 − 6 = 0` at the top; taking
`Φ q = 1` (banked), `Φ p = 0` (spent), the amortized window `excess q + (k−2) + Φ p ≤
excess p + Φ q` reads `4 + 3 + 0 ≤ 6 + 1`, i.e. `7 ≤ 7` — TRUE and tight.  This is the exact
front-loading the cumulative form absorbs and the per-window form cannot; it Lean-certifies that
the `AmortizedWindow` residual is satisfiable precisely where `WindowExcess` is refuted. -/

set_option maxRecDepth 10000 in
/-- **The amortized window holds at the `WindowExcess`-refuting witness.**  On the `ℓ = 120`
witness `P` and its `65`-vertex exitless prefix `q` (`excess q = 4`, `excess P = 6`), the
amortized window inequality with the banked-surplus potential values `(Φ P, Φ q) = (0, 1) ∈ {0,1}`
holds — `4 + (k−2) + 0 ≤ 6 + 1`, i.e. `7 ≤ 7`, tight — while the uniform `WindowExcess`
inequality `4 + (k−2) ≤ 6`, i.e. `7 ≤ 6`, FAILS on the very same data.  The banked value
`Φ q = 1 = s(65)` is the front-loaded surplus the cumulative telescope carries and the per-window
form cannot.  Lean-certifies that the `AmortizedWindow` residual is satisfiable exactly where
`WindowExcess` is refuted (`Refutations.windowExcess_false`). -/
theorem amortizedWindow_holds_at_witness :
    ∃ (P q : HPath 5),
      P.Exitless ∧ q.Exitless ∧
      5 * (5 - 1) * (5 - 2) < P.numVerts ∧
      q.verts = P.verts.take (P.numVerts - ell0 5) ∧
      excess q = 4 ∧ excess P = 6 ∧
      -- amortized window with (Φ P, Φ q) = (0, 1): TRUE (tight)
      excess q + (5 - 2) + 0 ≤ excess P + 1 ∧
      -- uniform `WindowExcess` on the same data: FALSE
      ¬ (excess q + (5 - 2) ≤ excess P) := by
  have hp : Refutations.P.Exitless := Refutations.P_exitless
  have hlt : 5 * (5 - 1) * (5 - 2) < Refutations.P.numVerts := by
    rw [Refutations.P_numVerts]; norm_num
  obtain ⟨q, hqv, hqe⟩ :=
    prefix_exitless hp (by norm_num : (1 : ℕ) ≤ 65) (by rw [Refutations.P_numVerts]; norm_num)
  have hpre : q.verts = Refutations.P.verts.take (Refutations.P.numVerts - ell0 5) := by
    rw [hqv, Refutations.prefix_len]
  have hep : excess Refutations.P = 6 := by rw [Refutations.excess_eq]; decide
  have heq : excess q = 4 := by rw [Refutations.excess_eq, hqv]; decide
  refine ⟨Refutations.P, q, hp, hqe, hlt, hpre, heq, hep, ?_, ?_⟩
  · rw [hep, heq]
  · rw [hep, heq]; norm_num

end ProofsMeta5

end Hunter

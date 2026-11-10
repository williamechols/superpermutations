/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsM1

/-!
# Theorem 2 — the EXPLICIT POTENTIAL CERTIFICATE (`Hunter.ProofsPotential`)

This file formalises the **explicit feasible potential** for the M1 slab certificate — the closing
arithmetic of Hunter's Theorem 2.  It supplies, sorry-free and axiom-clean, the demand-side closed
form `Dfr` and the four per-transition inequalities that the M1 walk induction consumes.

## The certificate (from `scratchpad/campaign/potential/certificate.py`, verified symbolically for
general `k` and numerically at `k = 5 … 12`)

* Period `M = (k−1)(k−2) − 1`.  The frontier demand per block, `Dfr(a)`, has the closed form
  (`slab.Dfr_block`): reduce `a` by `M` (each reduction adds `k−2`) down to the base window
  `a ≤ (k−1)(k−2)`, where `Dfr(a) = ⌈a/(k−1)⌉ − 1 = (a−1)/(k−1)` (`Nat` floor division).

* The **potential** on DP state `(d, j)` (door-depth `d ∈ 0..k−2`, α-run slabs done `j ∈ 0..k−3`):
    `W(d,j) := (k−1)(k−2−j) − 1 − d`      (blocks left in the current run)
    `h(d,j,b) := Dfr(b + W) − Dfr(b) − (k−3−j)`      (jumps ahead minus α-credits still owed).

* **Structural lemmas** (GAP / L1): the demand jumps have gaps in `{k−2, k−1}`, equivalently every
  `k−1` consecutive blocks carry `≥ 1` jump — giving the floor lower bound
  `Dfr(b+W) − Dfr(b) ≥ W/(k−1)` and, from a jump, `+1` more.  These make the `ℕ`-truncated `h`
  honest (`h_nonneg`).

* **SHIFT**: `Dfr(x+M) − Dfr(x) = k−2` for `x ≥ 2` (and `= k−3` at `x = 1`).

* The **four transition inequalities** (`certificate.py`): DOOR (telescope, equality), ALPHA
  (telescope + credit), HEAVY (`2 + h ≥ …` via SHIFT), RESET (the `a_i ≤ b + i(k−1)` induction under
  the guard `d ≤ k−3`), each `Dfr`/floor arithmetic over the proved API.

## Scope and the honest residual

`M1WalkBound k` is *definitionally* `ExcessFrontier k` (`ProofsM1.m1WalkBound_iff_excessFrontier`),
the project's central open bound.  This file discharges the **arithmetic core** of the potential
certificate.  The remaining bridge — that every exitless path induces an M1-legal block walk whose
per-block excess accumulates against `Dfr` — is carried at path level by the Lean ledger
(`ProofsLedger`, `ProofsRunExtract.metaDepth_le`) together with the reset-from-complete exclusion
(`ProofsFill`/`ProofsFillPath`).  Until that bridge lands, the Theorem-2 capstones below are threaded
through the existing `ProofsM1` chains carrying the hypothesis `M1WalkBound k` (resp. its global
form); the potential certificate here is exactly what a future walk induction consumes to discharge
it.  See `PROGRESS-potential.md`.

Namespace `Hunter.ProofsPotential`; capstones re-exported in `Hunter.Proved`.
-/

namespace Hunter

open scoped Classical

namespace ProofsPotential

variable {k : ℕ}

/-! ## §1. The demand-side closed form `Dfr`

`Dfr k a` is the block-indexed frontier demand of `certificate.py`.  In the base window
`a ≤ (k−1)(k−2)` it is `(a−1)/(k−1)` (`= ⌈a/(k−1)⌉ − 1`); above it the quasi-period `M = (k−1)(k−2)−1`
lifts the value by `k−2` (the SHIFT).  The guard `2 ≤ (k−1)(k−2)` in the recursive branch keeps the
definition well-founded for *every* `k` (it is vacuous for `k ≥ 3`, where `(k−1)(k−2) ≥ 2`). -/

/-- The demand period `M = (k−1)(k−2) − 1`. -/
def Mper (k : ℕ) : ℕ := (k - 1) * (k - 2) - 1

/-- **Block-indexed frontier demand** (`certificate.py`'s `Dfr_block`).  Base window
`a ≤ (k−1)(k−2)`: `(a−1)/(k−1)`.  Above: `Dfr(a − M) + (k−2)`. -/
def Dfr (k : ℕ) (a : ℕ) : ℕ :=
  if h : (k - 1) * (k - 2) < a ∧ 2 ≤ (k - 1) * (k - 2) then
    Dfr k (a - ((k - 1) * (k - 2) - 1)) + (k - 2)
  else
    (a - 1) / (k - 1)
termination_by a
decreasing_by
  obtain ⟨h1, h2⟩ := h
  omega

/-- **Base-window value.**  For `a ≤ (k−1)(k−2)`, `Dfr k a = (a−1)/(k−1)`. -/
theorem Dfr_base {a : ℕ} (ha : a ≤ (k - 1) * (k - 2)) : Dfr k a = (a - 1) / (k - 1) := by
  rw [Dfr]
  rw [dif_neg]
  rintro ⟨h1, _⟩
  omega

/-- **SHIFT (recursion branch).**  For `(k−1)(k−2) < a` and `k ≥ 3`,
`Dfr k a = Dfr k (a − M) + (k−2)`. -/
theorem Dfr_shift_rec (hk : 3 ≤ k) {a : ℕ} (ha : (k - 1) * (k - 2) < a) :
    Dfr k a = Dfr k (a - Mper k) + (k - 2) := by
  have h2 : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  rw [Dfr]
  rw [dif_pos ⟨ha, h2⟩]
  rfl

/-- `Dfr k 0 = 0`. -/
@[simp] theorem Dfr_zero : Dfr k 0 = 0 := by
  rw [Dfr_base (Nat.zero_le _)]; simp

/-- `Dfr k 1 = 0`. -/
@[simp] theorem Dfr_one (hk : 3 ≤ k) : Dfr k 1 = 0 := by
  have h2 : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  rw [Dfr_base (by omega)]; simp

/-! ## §2. Structural lemmas of `Dfr` — GAP / SHIFT / floor bounds

These are the two-distance ("gap `∈ {k−2, k−1}`") structural facts of `certificate.py` PART B,
recast as arithmetic on the closed form.  We keep them under `4 ≤ k`, where `(k−1)(k−2) ≥ 6 ≥ k`
so a single `M`-window peel always lands back inside the base window — this is the honest verified
range (`k = 5 … 12` numerically) and is immaterial to the delivered capstones, which carry
`M1WalkBound` as a hypothesis regardless of this internal range. -/

/-- `0 < Mper k` for `k ≥ 3`. -/
theorem Mper_pos (hk : 3 ≤ k) : 0 < Mper k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [Mper]
  have h2 : (m + 3 - 1) * (m + 3 - 2) = m * m + 3 * m + 2 := by
    have : (m + 3 - 1) * (m + 3 - 2) = (m + 2) * (m + 1) := by
      congr 1
    rw [this]; ring
  omega

/-- **`Mper k / (k−1) = k − 3`.**  The demand rises by `k−2` over `Mper` blocks, i.e. one short of a
full `(k−1)`-quotient — the arithmetic root of the extra `{1}` demand phase. -/
theorem Mper_div (hk : 3 ≤ k) : Mper k / (k - 1) = k - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [Mper]
  have hm : (m + 3 - 1) * (m + 3 - 2) - 1 = (m + 1) + (m + 2) * m := by
    have : (m + 3 - 1) * (m + 3 - 2) = (m + 1) + (m + 2) * m + 1 := by
      have e : (m + 3 - 1) * (m + 3 - 2) = (m + 2) * (m + 1) := by
        congr 1
      rw [e]; ring
    omega
  have hk1 : m + 3 - 1 = m + 2 := by omega
  rw [hm, hk1, Nat.add_mul_div_left _ _ (by omega : 0 < m + 2), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  omega

/-- **`Mper k % (k−1) = k − 2`** (companion to `Mper_div`). -/
theorem Mper_mod (hk : 3 ≤ k) : Mper k % (k - 1) = k - 2 := by
  have hdm := Nat.div_add_mod (Mper k) (k - 1)
  rw [Mper_div hk] at hdm
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [Mper] at hdm ⊢
  have e : (m + 3 - 1) * (m + 3 - 2) - 1 = (m + 1) + (m + 2) * m := by
    have h2 : (m + 3 - 1) * (m + 3 - 2) = (m + 1) + (m + 2) * m + 1 := by
      have ee : (m + 3 - 1) * (m + 3 - 2) = (m + 2) * (m + 1) := by
        congr 1
      rw [ee]; ring
    omega
  rw [e] at hdm ⊢
  simp only [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 3 = m from by omega,
    show m + 3 - 2 = m + 1 from by omega] at hdm ⊢
  omega

/-- `6 ≤ (k−1)(k−2)` for `k ≥ 4` — the base-window lower bound the `omega` steps rely on. -/
theorem prod_ge (hk : 4 ≤ k) : 6 ≤ (k - 1) * (k - 2) := by
  have := Nat.mul_le_mul (show 3 ≤ k - 1 by omega) (show 2 ≤ k - 2 by omega); omega

/-- `Dfr k 2 = 0` for `k ≥ 4` (base-window, `1/(k−1) = 0`). -/
theorem Dfr_two (hk : 4 ≤ k) : Dfr k 2 = 0 := by
  rw [Dfr_base (by have := prod_ge hk; omega)]
  exact Nat.div_eq_of_lt (by omega)

/-- **Exact SHIFT.**  `Dfr(x + M) = Dfr(x) + (k−2)` for `x ≥ 2` — one full period lifts the demand by
exactly `k−2` (`certificate.py`'s SHIFT for `x ≥ 2`). -/
theorem Dfr_shift_exact (hk : 3 ≤ k) {x : ℕ} (hx : 2 ≤ x) :
    Dfr k (x + Mper k) = Dfr k x + (k - 2) := by
  have hlt : (k - 1) * (k - 2) < x + Mper k := by simp only [Mper]; omega
  rw [Dfr_shift_rec hk hlt]
  congr 2
  simp only [Mper]; omega

/-- **Single-step monotonicity** `Dfr k a ≤ Dfr k (a+1)`. -/
theorem Dfr_le_succ (hk : 4 ≤ k) (a : ℕ) : Dfr k a ≤ Dfr k (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have hP := prod_ge hk
    have hMdef : Mper k = (k - 1) * (k - 2) - 1 := rfl
    by_cases hbase : a + 1 ≤ (k - 1) * (k - 2)
    · rw [Dfr_base (by omega), Dfr_base hbase]
      exact Nat.div_le_div_right (by omega)
    · by_cases hbig : (k - 1) * (k - 2) < a
      · rw [Dfr_shift_rec (by omega) hbig,
            Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < a + 1)]
        have hmp := Mper_pos (show 3 ≤ k by omega)
        have hMlt : Mper k ≤ a := by omega
        have hdec : a - Mper k < a := by omega
        have hstep : a + 1 - Mper k = (a - Mper k) + 1 := by omega
        rw [hstep]
        exact Nat.add_le_add_right (ih (a - Mper k) hdec) _
      · have haeq : a = (k - 1) * (k - 2) := by omega
        have hlhs : Dfr k a = k - 3 := by
          rw [Dfr_base (le_of_eq haeq), haeq]; exact Mper_div (by omega)
        have hrhs : Dfr k (a + 1) = k - 2 := by
          rw [Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < a + 1)]
          have : a + 1 - Mper k = 2 := by simp only [Mper]; omega
          rw [this, Dfr_two hk, Nat.zero_add]
        omega

/-- **Single-step increment bound** `Dfr k (a+1) ≤ Dfr k a + 1` — the demand rises by at most one
per block (companion to `Dfr_le_succ`; used by the HEAVY inequality). -/
theorem Dfr_succ_le (hk : 4 ≤ k) (a : ℕ) : Dfr k (a + 1) ≤ Dfr k a + 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have hP := prod_ge hk
    have hMdef : Mper k = (k - 1) * (k - 2) - 1 := rfl
    by_cases hbase : a + 1 ≤ (k - 1) * (k - 2)
    · rw [Dfr_base hbase, Dfr_base (show a ≤ (k - 1) * (k - 2) by omega)]
      calc (a + 1 - 1) / (k - 1) ≤ ((a - 1) + (k - 1)) / (k - 1) :=
            Nat.div_le_div_right (by omega)
        _ = (a - 1) / (k - 1) + 1 := Nat.add_div_right _ (by omega)
    · by_cases hbig : (k - 1) * (k - 2) < a
      · rw [Dfr_shift_rec (by omega) hbig,
            Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < a + 1)]
        have hmp := Mper_pos (show 3 ≤ k by omega)
        have hMlt : Mper k ≤ a := by omega
        have hdec : a - Mper k < a := by omega
        have hstep : a + 1 - Mper k = (a - Mper k) + 1 := by omega
        rw [hstep]
        have := ih (a - Mper k) hdec
        omega
      · have haeq : a = (k - 1) * (k - 2) := by omega
        have hlhs : Dfr k a = k - 3 := by
          rw [Dfr_base (le_of_eq haeq), haeq]; exact Mper_div (by omega)
        have hrhs : Dfr k (a + 1) = k - 2 := by
          rw [Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < a + 1)]
          have : a + 1 - Mper k = 2 := by omega
          rw [this, Dfr_two hk, Nat.zero_add]
        omega

/-- **Monotonicity** `a ≤ b → Dfr k a ≤ Dfr k b`. -/
theorem Dfr_mono (hk : 4 ≤ k) {a b : ℕ} (h : a ≤ b) : Dfr k a ≤ Dfr k b := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (Dfr_le_succ hk n)

/-- **The window step (GAP / L1).**  Every `k−1` consecutive blocks carry `≥ 1` demand jump:
`Dfr(x) + 1 ≤ Dfr(x + (k−1))` for `x ≥ 1`.  The max-gap-`k−1` fact of `certificate.py` PART B. -/
theorem Dfr_window (hk : 4 ≤ k) {x : ℕ} (hx : 1 ≤ x) :
    Dfr k x + 1 ≤ Dfr k (x + (k - 1)) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hP := prod_ge hk
    have hMdef : Mper k = (k - 1) * (k - 2) - 1 := rfl
    by_cases hbase : x + (k - 1) ≤ (k - 1) * (k - 2)
    · rw [Dfr_base (by omega), Dfr_base hbase]
      have he : x + (k - 1) - 1 = (x - 1) + (k - 1) := by omega
      rw [he, Nat.add_div_right _ (by omega : 0 < k - 1)]
    · by_cases hbig : (k - 1) * (k - 2) < x
      · rw [Dfr_shift_rec (by omega) hbig,
            Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < x + (k - 1))]
        have hmp := Mper_pos (show 3 ≤ k by omega)
        have hMlt : Mper k ≤ x := by omega
        have hstep : x + (k - 1) - Mper k = (x - Mper k) + (k - 1) := by omega
        rw [hstep]
        have hdec : x - Mper k < x := by omega
        have hpos : 1 ≤ x - Mper k := by omega
        have := ih (x - Mper k) hdec hpos
        omega
      · -- crossing: x ≤ (k-1)(k-2) < x + (k-1)
        have hlhs : Dfr k x ≤ k - 3 := by
          rw [Dfr_base (by omega)]
          calc (x - 1) / (k - 1) ≤ ((k - 1) * (k - 2) - 1) / (k - 1) :=
                Nat.div_le_div_right (by omega)
            _ = k - 3 := Mper_div (by omega)
        have hrhs : k - 2 ≤ Dfr k (x + (k - 1)) := by
          rw [Dfr_shift_rec (by omega) (by omega : (k - 1) * (k - 2) < x + (k - 1))]
          omega
        omega

/-- **Floor lower bound.**  For `x ≥ 1`, `Dfr(x + W) ≥ Dfr(x) + W/(k−1)` — iterating the window
step.  This is the demand-side workhorse behind `h_nonneg` and the HEAVY / RESET inequalities. -/
theorem Dfr_floor (hk : 4 ≤ k) {x : ℕ} (hx : 1 ≤ x) (W : ℕ) :
    Dfr k x + W / (k - 1) ≤ Dfr k (x + W) := by
  have key : ∀ q : ℕ, Dfr k x + q ≤ Dfr k (x + (k - 1) * q) := by
    intro q
    induction q with
    | zero => simp
    | succ n ih =>
      have hstep : x + (k - 1) * (n + 1) = (x + (k - 1) * n) + (k - 1) := by ring
      rw [hstep]
      have hw := Dfr_window hk (show 1 ≤ x + (k - 1) * n by omega)
      omega
  have hq := key (W / (k - 1))
  have hle : W / (k - 1) * (k - 1) ≤ W := Nat.div_mul_le_self W (k - 1)
  have hmono := Dfr_mono hk (show x + (k - 1) * (W / (k - 1)) ≤ x + W by
    rw [Nat.mul_comm]; omega)
  omega

/-! ## §3. The explicit potential `h` and its honesty (`ℕ`-truncation is vacuous)

`W(d,j) = (k−1)(k−2−j) − 1 − d` is the number of blocks left in the current α-run from DP state
`(d,j)`; `h(d,j,b) = Dfr(b+W) − Dfr(b) − (k−3−j)`.  The α-credit `k−3−j` never exceeds the jumps
`Dfr(b+W) − Dfr(b)` in the window (`Dfr_add_Wpot_ge`, from `Dfr_floor` + `Wpot_ge`), so the outer
subtraction in `h` never truncates — recorded as the additive identity `hpot_val`. -/

/-- Blocks left in the current α-run: `W(d,j) = (k−1)(k−2−j) − 1 − d`. -/
def Wpot (k d j : ℕ) : ℕ := (k - 1) * (k - 2 - j) - 1 - d

/-- The explicit potential `h(d,j,b) = Dfr(b + W(d,j)) − Dfr(b) − (k−3−j)`. -/
def hpot (k d j b : ℕ) : ℕ := Dfr k (b + Wpot k d j) - Dfr k b - (k - 3 - j)

/-- **Window-length lower bound.**  `(k−1)(k−3−j) ≤ W(d,j)` for `j ≤ k−3`, `d ≤ k−2`.  This is the
`(k−1)`-multiple that `Dfr_floor` converts into the `k−3−j` α-credits. -/
theorem Wpot_ge (hk : 4 ≤ k) {d j : ℕ} (hj : j ≤ k - 3) (hd : d ≤ k - 2) :
    (k - 1) * (k - 3 - j) ≤ Wpot k d j := by
  have hWdef : Wpot k d j = (k - 1) * (k - 2 - j) - 1 - d := rfl
  have hsplit : (k - 1) * (k - 2 - j) = (k - 1) * (k - 3 - j) + (k - 1) := by
    rw [show k - 2 - j = (k - 3 - j) + 1 from by omega, Nat.mul_add, Nat.mul_one]
  omega

/-- **`h_nonneg` (additive honesty core).**  `Dfr(b) + (k−3−j) ≤ Dfr(b + W(d,j))` for `b ≥ 1`,
`j ≤ k−3`, `d ≤ k−2` — the α-credits are covered by the window's jumps, so the subtractions in `h`
are honest.  Proved from `Dfr_floor` and `Wpot_ge`. -/
theorem Dfr_add_Wpot_ge (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) (hj : j ≤ k - 3) (hd : d ≤ k - 2) :
    Dfr k b + (k - 3 - j) ≤ Dfr k (b + Wpot k d j) := by
  have hfloor := Dfr_floor hk hb (Wpot k d j)
  have hWlb := Wpot_ge hk hj hd
  have hdiv : (k - 3 - j) ≤ Wpot k d j / (k - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < k - 1)]
    calc (k - 3 - j) * (k - 1) = (k - 1) * (k - 3 - j) := by ring
      _ ≤ Wpot k d j := hWlb
  omega

/-- **The value of `h` in truncation-free additive form.**
`h(d,j,b) + (k−3−j) + Dfr(b) = Dfr(b + W(d,j))`.  Everything below manipulates `h` through this
identity, so the `ℕ` subtractions never bite. -/
theorem hpot_val (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) (hj : j ≤ k - 3) (hd : d ≤ k - 2) :
    hpot k d j b + (k - 3 - j) + Dfr k b = Dfr k (b + Wpot k d j) := by
  have h := Dfr_add_Wpot_ge hk hb hj hd
  have hm : Dfr k b ≤ Dfr k (b + Wpot k d j) :=
    Dfr_mono hk (by omega)
  simp only [hpot]
  omega

/-! ## §4. The four per-transition inequalities (`certificate.py`)

Each is stated in the additive, truncation-free form of the per-transition requirement
`cost + h(s,b) − h(s′,b+1) ≥ Dfr(b+1) − Dfr(b)`, rearranged to
`h(s′,b+1) + Dfr(b+1) ≤ cost + h(s,b) + Dfr(b)`.  DOOR and ALPHA are pure index telescopes (the
`Dfr(b+W)` terms cancel); HEAVY and RESET consume `Dfr_shift_exact` + `Dfr_floor`, RESET using the
incompleteness guard `d ≤ k−3` for the extra credit.  All manipulate `h` only through `hpot_val`. -/

/-- `h(0,0,b+1) = 1` — the reset/heavy target's bonus is exactly one (via `Dfr_shift_exact`). -/
theorem hpot_00 (hk : 4 ≤ k) {b : ℕ} (hb : 1 ≤ b) : hpot k 0 0 (b + 1) = 1 := by
  have hv := hpot_val hk (show 1 ≤ b + 1 by omega) (show (0 : ℕ) ≤ k - 3 by omega)
    (show (0 : ℕ) ≤ k - 2 by omega)
  have hW : Wpot k 0 0 = Mper k := by simp only [Wpot, Mper, Nat.sub_zero]
  rw [hW, Dfr_shift_exact (show 3 ≤ k by omega) (show 2 ≤ b + 1 by omega)] at hv
  omega

/-- **DOOR** (cost `0`, `d < k−2`): pure telescope, equality.  `(b+1)+W(d+1,j) = b+W(d,j)` so the
window demand cancels and `door` carries exactly the block's own demand jump. -/
theorem door_ineq (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) (hd : d < k - 2) (hj : j ≤ k - 3) :
    hpot k (d + 1) j (b + 1) + Dfr k (b + 1) ≤ hpot k d j b + Dfr k b := by
  have hAlb : k - 1 ≤ (k - 1) * (k - 2 - j) := Nat.le_mul_of_pos_right (k - 1) (by omega)
  have h1 : Wpot k d j = (k - 1) * (k - 2 - j) - 1 - d := rfl
  have h2 : Wpot k (d + 1) j = (k - 1) * (k - 2 - j) - 1 - (d + 1) := rfl
  have hidx : (b + 1) + Wpot k (d + 1) j = b + Wpot k d j := by omega
  have v1 := hpot_val hk hb hj (by omega : d ≤ k - 2)
  have v2 := hpot_val hk (show 1 ≤ b + 1 by omega) hj (by omega : d + 1 ≤ k - 2)
  rw [hidx] at v2
  omega

/-- **ALPHA** (cost `1`, `d = k−2`, `j+2 ≤ k−2`): telescope + one α-credit, equality.
`(b+1)+W(0,j+1) = b+W(k−2,j)`. -/
theorem alpha_ineq (hk : 4 ≤ k) {b j : ℕ} (hb : 1 ≤ b) (hj : j ≤ k - 4) :
    hpot k 0 (j + 1) (b + 1) + Dfr k (b + 1) ≤ 1 + hpot k (k - 2) j b + Dfr k b := by
  have hsplit : (k - 1) * (k - 2 - j) = (k - 1) * (k - 3 - j) + (k - 1) := by
    rw [show k - 2 - j = (k - 3 - j) + 1 from by omega, Nat.mul_add, Nat.mul_one]
  have hQlb : k - 1 ≤ (k - 1) * (k - 3 - j) := Nat.le_mul_of_pos_right (k - 1) (by omega)
  have h1 : Wpot k (k - 2) j = (k - 1) * (k - 2 - j) - 1 - (k - 2) := rfl
  have h2 : Wpot k 0 (j + 1) = (k - 1) * (k - 2 - (j + 1)) - 1 - 0 := rfl
  have h3 : k - 2 - (j + 1) = k - 3 - j := by omega
  rw [h3] at h2
  have hidx : (b + 1) + Wpot k 0 (j + 1) = b + Wpot k (k - 2) j := by
    rw [h1, h2, hsplit]; omega
  have v1 := hpot_val hk hb (by omega : j ≤ k - 3) (by omega : k - 2 ≤ k - 2)
  have v2 := hpot_val hk (show 1 ≤ b + 1 by omega) (by omega : j + 1 ≤ k - 3)
    (by omega : (0 : ℕ) ≤ k - 2)
  rw [hidx] at v2
  have hcred : k - 3 - j = (k - 3 - (j + 1)) + 1 := by omega
  omega

/-- **HEAVY** (cost `2`, any state): always affordable.  `h(0,0,b+1) = 1`, `h ≥ 0`, and
`Dfr(b+1) ≤ Dfr(b) + 1` leave a unit of slack. -/
theorem heavy_ineq (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) (_hd : d ≤ k - 2)
    (_hj : j ≤ k - 3) :
    hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 2 + hpot k d j b + Dfr k b := by
  have h00 := hpot_00 hk hb
  have hle := Dfr_succ_le hk b
  omega

/-- **RESET** (cost `1`, `d ≤ k−3`, i.e. *incomplete*): the guard supplies the extra credit.
`W(d,j) − 1 ≥ (k−1)(k−3−j)`, so `Dfr_floor` from `b+1` gives `Dfr(b+W) ≥ Dfr(b+1) + (k−3−j)`, exactly
matching `h(d,j,b)`'s owed credit. -/
theorem reset_ineq (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) (hd : d ≤ k - 3) (hj : j ≤ k - 3) :
    hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 1 + hpot k d j b + Dfr k b := by
  have h00 := hpot_00 hk hb
  have v1 := hpot_val hk hb hj (by omega : d ≤ k - 2)
  have hsplit : (k - 1) * (k - 2 - j) = (k - 1) * (k - 3 - j) + (k - 1) := by
    rw [show k - 2 - j = (k - 3 - j) + 1 from by omega, Nat.mul_add, Nat.mul_one]
  have hWdef : Wpot k d j = (k - 1) * (k - 2 - j) - 1 - d := rfl
  have hWval : Wpot k d j = (k - 1) * (k - 3 - j) + (k - 2 - d) := by rw [hWdef, hsplit]; omega
  have hWge1 : 1 ≤ Wpot k d j := by rw [hWval]; omega
  have hidx : b + Wpot k d j = (b + 1) + (Wpot k d j - 1) := by rw [hWval]; omega
  have hWm1 : (k - 1) * (k - 3 - j) ≤ Wpot k d j - 1 := by rw [hWval]; omega
  have hdiv : (k - 3 - j) ≤ (Wpot k d j - 1) / (k - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < k - 1)]
    calc (k - 3 - j) * (k - 1) = (k - 1) * (k - 3 - j) := by ring
      _ ≤ Wpot k d j - 1 := hWm1
  have hfloor := Dfr_floor hk (show 1 ≤ b + 1 by omega) (Wpot k d j - 1)
  rw [← hidx] at hfloor
  omega

/-! ## §5. The certificate bundle

The four per-transition inequalities of `certificate.py`, all sorry-free, packaged as one statement in
the additive per-transition form
`h(s′,b+1) + Dfr(b+1) ≤ cost + h(s,b) + Dfr(b)`.  This is the complete arithmetic core the M1 walk
induction consumes at each ledger-classified boundary; `hpot_val` records that the `ℕ`-truncated `h`
is honest throughout. -/

/-- **The explicit potential certificate** (all four transition inequalities). -/
theorem potential_certificate (hk : 4 ≤ k) {b d j : ℕ} (hb : 1 ≤ b) :
    -- DOOR (cost 0, d < k−2)
    (d < k - 2 → j ≤ k - 3 →
      hpot k (d + 1) j (b + 1) + Dfr k (b + 1) ≤ hpot k d j b + Dfr k b) ∧
    -- ALPHA (cost 1, from complete, j+2 ≤ k−2)
    (j ≤ k - 4 →
      hpot k 0 (j + 1) (b + 1) + Dfr k (b + 1) ≤ 1 + hpot k (k - 2) j b + Dfr k b) ∧
    -- HEAVY (cost 2, any state)
    (d ≤ k - 2 → j ≤ k - 3 →
      hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 2 + hpot k d j b + Dfr k b) ∧
    -- RESET (cost 1, from incomplete d ≤ k−3)
    (d ≤ k - 3 → j ≤ k - 3 →
      hpot k 0 0 (b + 1) + Dfr k (b + 1) ≤ 1 + hpot k d j b + Dfr k b) :=
  ⟨fun hd hj => door_ineq hk hb hd hj,
   fun hj => alpha_ineq hk hb hj,
   fun hd hj => heavy_ineq hk hb hd hj,
   fun hd hj => reset_ineq hk hb hd hj⟩

end ProofsPotential

/-! ## §6. The `Hunter.Proved` endgame capstones

The M1 slab bound `M1WalkBound k` is *definitionally* `ExcessFrontier k`
(`ProofsM1.m1WalkBound_iff_excessFrontier`).  The explicit potential certificate of §1–§5 supplies the
arithmetic the M1 walk induction consumes; the remaining path-level bridge (every exitless path
induces an M1-legal block walk) is carried by the Lean ledger and the `ProofsFill`/`ProofsFillPath`
reset-from-complete exclusion.  Until that bridge lands, the capstones carry `M1WalkBound k` (resp. its
global form `M1WalkBoundAll`) — this is the sole remaining hypothesis beyond the numeric leaves
`hproof`/`hexists`, identical to the residual `ProofsM1` already isolates.  These re-exports give the
Theorem-2 / Theorem-1 statements their final `Hunter.Proved` names. -/

namespace Proved

open ProofsRecursion ProofsM1

/-- **`ExcessFrontier` from the M1 slab bound** (the explicit-potential route). -/
theorem excess_frontier_final {k : ℕ} (hM1 : M1WalkBound k) : ExcessFrontier k :=
  ProofsM1.excessFrontier_of_m1 hM1

/-- **Theorem 2** (verbatim `Statements.thm2` conclusion) from the M1 slab bound. -/
theorem thm2 {k ℓ : ℕ} (hk : 3 ≤ k) (hM1 : M1WalkBound k) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  Proved.thm2_of_m1 hk hM1 hℓ

/-- **thm1v1** (superpermutation form) from the global M1 slab bound. -/
theorem thm1v1_final (hM1 : Proved.M1WalkBoundAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Proved.thm1v1_of_m1 hM1 hproof hexists

/-- **thm1v2** (`L(k) ≥ coeff(k)·k! − O(1)`) from the global M1 slab bound. -/
theorem thm1v2_final (hM1 : Proved.M1WalkBoundAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Proved.thm1v2_of_m1 hM1 hproof hexists

/-- **eq-weak** (comparable factorial form) from the global M1 slab bound, through the
`FrontierTightHeavyAll` / `ProofsMF.eq_weak_of_MF` chain. -/
theorem eq_weak_final (hM1 : Proved.M1WalkBoundAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsMF.eq_weak_of_MF (Proved.frontierTightHeavyAll_of_m1All hM1) hproof hexists

end Proved

end Hunter

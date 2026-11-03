/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsAssembly

/-!
# Theorem 2 — the R-FRAME residual shrink (post-LP re-examination)

This file re-examines the `SaturatedTightHeavy k` residual (the single remaining case of Theorem 2,
see `ProofsAssembly`) in light of the LP-feasible absolute-`R` potential frame.

## What the re-run LP + the door telescope prove

The LP verdict was: **no bounded structural potential is feasible; the absolute demand-phase
coordinate `R` is required** (`Φ ∈ {0,1}`, `Φ = 1` = "start of a 2-loop holding banked surplus").
Re-reading that with today's proved ledger, the saturated window is *maximally rigid* and its
payment is pinned by pure `doorDepth` arithmetic:

* **`rSum_eq_complete`** — in a saturated window every ejection leaves a *complete* 2-loop, so the
  door-run depth just before each ejection is **exactly** `k−2` (not just `≤ k−2` as in the generic
  `rSum_le`).  Hence the reset sum is *exactly* `(#non-doors)·(k−2)`.
* **`windowSat_count`** — feeding that equality into `ProofsLedger2.doorTele` collapses to
  `W·(k−1) = doorDepth a + M − doorDepth (a+M)`.  With the two caps `doorDepth (a+M) ≤ k−2`
  (`doorDepth_le_km2`) and the single extra input `doorDepth a ≠ 0`, this gives `W·(k−1) ≥ (k−2)²`,
  hence the non-door count `W ≥ k−2`.
* **`saturatedHeavy_of_doorPos`** — therefore the saturated top window pays the full `k−2`
  **unconditionally on tightness**, as soon as the window's *first* block has positive door-depth.

So the whole residual `SaturatedTightHeavy k` reduces to the single, purely structural door-position
statement `TightLoopEntryFree k`:

    a frontier-tight `ℓ₀`-prefix `q` has `doorDepth (winA p) ≠ 0`.

i.e. **a frontier-tight recursion frontier never sits at a fresh 2-loop entry (door-depth 0).**
The re-run computation confirms this is exactly the LP's `Φ`-obstruction: door-depth 0 in the
recursion region forces a banked surplus `s ≥ 1` (verified `min s = 1` across 76k states), so it is
never tight.  What the pure ledger *cannot* see — and the LP flagged as the irreducible absolute-`R`
content — is the alignment of the door-phase (`runStart mod (k−1)`, an absolute coordinate) with the
demand-jump phase; see `PROGRESS-rframe.md`.

Namespace `Hunter.ProofsRFrame`.  Sorry-free, axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsRFrame

open ProofsLedger ProofsLedger2 ProofsAssembly ProofsSynthesis ProofsRecursion ProofsWindow
open HPath

variable {k : ℕ}

/-! ## §1. The saturated reset sum is *exact* -/

/-- **Exact reset sum for a saturated window.**  If every non-door boundary among blocks
`a+1 … a+e` leaves a *complete* 2-loop (`k−2 ≤ doorDepth` just before it — and the cap
`doorDepth ≤ k−2` pins equality), then the reset sum is *exactly* `(#non-doors)·(k−2)`.  This is the
equality strengthening of `ProofsLedger2.rSum_le`. -/
theorem rSum_eq_complete (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (a M : ℕ)
    (hM : k * (a + M) < p.numVerts)
    (hcomp : ∀ j, 1 ≤ j → j ≤ M → IsDoor p (a + j) ∨ k - 2 ≤ doorDepth p (a + j - 1)) :
    ∀ e, e ≤ M → rSum p a e = (e - dCount p a e) * (k - 2) := by
  intro e
  induction e with
  | zero => intro _; simp [rSum, dCount]
  | succ e ih =>
    intro heM
    have ihe := ih (by omega)
    have hdle := dCount_le p a e
    by_cases h : IsDoor p (a + (e + 1))
    · rw [rSum, dCount, if_pos h, if_pos h, Nat.add_zero]
      have hR : ((e + 1) - (dCount p a e + 1)) * (k - 2) = (e - dCount p a e) * (k - 2) := by
        congr 1; omega
      rw [hR]; exact ihe
    · rw [rSum, dCount, if_neg h, if_neg h]
      have hrange : k * (a + e) < p.numVerts := by
        have : k * (a + e) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
        omega
      have hup : doorDepth p (a + e) ≤ k - 2 := doorDepth_le_km2 hk hp (a + e) hrange
      have hlo : k - 2 ≤ doorDepth p (a + e) := by
        have := hcomp (e + 1) (by omega) heM
        have hidx : a + (e + 1) - 1 = a + e := by omega
        rcases this with hd | hc
        · exact absurd hd h
        · rw [hidx] at hc; exact hc
      have hdd : doorDepth p (a + e) = k - 2 := le_antisymm hup hlo
      have hR : ((e + 1) - dCount p a e) * (k - 2)
          = (e - dCount p a e) * (k - 2) + (k - 2) := by
        rw [show (e + 1) - dCount p a e = (e - dCount p a e) + 1 from by omega]; ring
      simp only [Nat.add_zero]
      rw [ihe, hdd, hR]

/-! ## §2. The non-door count of a saturated, door-open window is `≥ k − 2` -/

/-- **Saturated + door-open ⇒ `k−2` weight-≥3 boundaries.**  For an exitless `p` and the
`M = (k−1)(k−2)−1`-block window `(a, a+M]`, if the window is saturated (`bw ≤ 3` and every non-door
leaves a complete 2-loop) *and its first block has positive door-depth* (`doorDepth a ≠ 0`), then the
window carries at least `k−2` weight-≥3 boundaries — the full `k−2`, one above the `k−3` floor.

Proof: `doorTele` + `rSum_eq_complete` collapse to `W·(k−1) = doorDepth a + M − doorDepth (a+M)`;
`doorDepth a ≥ 1`, `doorDepth (a+M) ≤ k−2` give `W·(k−1) ≥ (k−2)² > (k−3)(k−1)`, so `W ≥ k−2`. -/
theorem windowSat_count (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (a : ℕ)
    (hM : k * (a + ((k - 1) * (k - 2) - 1)) < p.numVerts)
    (hsat : WindowSaturated p a ((k - 1) * (k - 2) - 1))
    (hpos : doorDepth p a ≠ 0) :
    k - 2 ≤ ((Finset.Icc 1 ((k - 1) * (k - 2) - 1)).filter
        (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))).card := by
  set M := (k - 1) * (k - 2) - 1 with hMdef
  set W := M - dCount p a M with hWdef
  have hdle := dCount_le p a M
  have htele := doorTele p a M
  have hrs := rSum_eq_complete hk hp a M hM hsat.2 M (le_refl M)
  rw [← hWdef] at hrs                               -- rSum p a M = W * (k - 2)
  have hfin : doorDepth p (a + M) ≤ k - 2 := doorDepth_le_km2 hk hp (a + M) hM
  have hpos1 : 1 ≤ doorDepth p a := by omega
  -- W ≥ k - 2 by the arithmetic collapse (mirrors window_incomplete_slack)
  have hWk : k - 2 ≤ W := by
    have hdc : dCount p a M + W = M := by omega
    have hWid : W * (k - 2) + W = W * (k - 1) := by
      rw [show k - 1 = (k - 2) + 1 from by omega]; ring
    -- from telescope+exact reset:  doorDepth a + M = doorDepth (a+M) + W*(k-1)
    have hcollapse : doorDepth p a + M = doorDepth p (a + M) + W * (k - 1) := by
      rw [hrs] at htele; omega
    have hM1 : M + 1 = (k - 1) * (k - 2) := by
      have hprodpos : 1 ≤ (k - 1) * (k - 2) := by
        calc 1 = 1 * 1 := by ring
          _ ≤ (k - 1) * (k - 2) := Nat.mul_le_mul (by omega) (by omega)
      rw [hMdef]; omega
    have hAid : (k - 1) * (k - 2) = (k - 3) * (k - 1) + (k - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, k - 3 = m := ⟨k - 3, rfl⟩
      have e1 : k - 1 = m + 2 := by omega
      have e2 : k - 2 = m + 1 := by omega
      rw [e1, e2, hm]; ring
    by_contra hlt
    have hWle : W ≤ k - 3 := by omega
    have hWmul : W * (k - 1) ≤ (k - 3) * (k - 1) := Nat.mul_le_mul_right _ hWle
    omega
  -- convert the non-door count W into the weight-≥3 count (verbatim window_incomplete_slack tail)
  have hWcard : W = ((Finset.Icc 1 M).filter (fun j => ¬ IsDoor p (a + j))).card := by
    have hdcard := dCount_eq_card p a M
    have hpart : ((Finset.Icc 1 M).filter (fun j => IsDoor p (a + j))).card
        + ((Finset.Icc 1 M).filter (fun j => ¬ IsDoor p (a + j))).card = M := by
      rw [Finset.card_filter_add_card_filter_not, Nat.card_Icc]; omega
    rw [hWdef, hdcard]; omega
  rw [hWcard] at hWk
  refine le_trans hWk (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
  obtain ⟨⟨hj1, hjM⟩, hjnd⟩ := hj
  refine ⟨⟨hj1, hjM⟩, ?_⟩
  have hN' : k * (a + j) < p.numVerts := by
    have : k * (a + j) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  have hkt : 1 ≤ k * (a + j) := Nat.mul_pos (by omega) (by omega)
  have hi1 : k * (a + j) - 1 + 1 = k * (a + j) := by omega
  have hin : (k * (a + j) - 1) + 1 < p.numVerts := by rw [hi1]; exact hN'
  have hd : k ∣ ((k * (a + j) - 1) + 1) := by rw [hi1]; exact ⟨a + j, rfl⟩
  have hge2 := ProofsWindow.boundary_ge_two (by omega : 1 ≤ k) hp hin hd
  rw [hi1] at hge2
  rw [IsDoor, bw] at hjnd
  omega

/-! ## §3. The saturated window pays `k − 2` as soon as its first block is door-open -/

/-- **Saturated + door-open top window ⇒ pays `k−2` (unconditional on tightness).**  Combining the
`k−2` non-door count (`windowSat_count`) with the master `excess_window_split` shows that a saturated
top window whose first block has positive door-depth pays the full `k−2` units of excess.  No
tightness hypothesis is used. -/
theorem saturatedHeavy_of_doorPos (hk : 3 ≤ k) {p q : HPath k}
    (hpe : p.Exitless) (_hqe : q.Exitless)
    (hlt : k * (k - 1) * (k - 2) < p.numVerts)
    (hprefix : q.verts = p.verts.take (p.numVerts - ell0 k))
    (hsat : WindowSaturated p (winA p) ((k - 1) * (k - 2) - 1))
    (hpos : doorDepth p (winA p) ≠ 0) :
    excess q + (k - 2) ≤ excess p := by
  set a := winA p with hadef
  set M := (k - 1) * (k - 2) - 1 with hMdef
  have hrange : k * (a + M) < p.numVerts := by rw [hadef, hMdef]; exact winA_range hk hlt
  have hsplit := excess_window_split hk hlt hprefix
  rw [← hadef, ← hMdef] at hsplit
  set W3 := (Finset.filter (fun j => 3 ≤ bw p (a + j)) (Finset.Icc 1 M)).card with hW3
  have hpay : W3 ≤ ∑ j ∈ Finset.Icc 1 M, (bw p (a + j) - 2) := by
    rw [hW3, Finset.card_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases h3 : 3 ≤ bw p (a + j) <;> simp only [h3, if_true, if_false] <;> omega
  have hcount : k - 2 ≤ W3 := by
    have h := windowSat_count hk hpe a (by rw [← hMdef]; exact hrange)
      (by rw [← hMdef]; exact hsat) hpos
    have hcard : (Finset.filter (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))
        (Finset.Icc 1 M)).card = W3 := rfl
    rw [← hMdef] at h; rw [hcard] at h; exact h
  omega

/-! ## §4. The shrunk residual `TightLoopEntryFree` and the capstone chain -/

/-- **The shrunk residual.**  A frontier-tight `ℓ₀`-prefix `q` of a recursion-region exitless `p`
never sits at a fresh 2-loop entry: its frontier block `winA p` has *positive door-depth*.  This is
strictly weaker than `SaturatedTightHeavy` — the entire window-counting content is discharged by
`saturatedHeavy_of_doorPos`; only this single door-position fact remains. -/
def TightLoopEntryFree (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    Hunter.j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q →
    doorDepth p (winA p) ≠ 0

/-- **The residual reduction.**  `TightLoopEntryFree k → SaturatedTightHeavy k`: the door-open fact
plus `saturatedHeavy_of_doorPos` closes the saturated case. -/
theorem saturatedTightHeavy_of_loopEntryFree (hk : 3 ≤ k)
    (hlef : TightLoopEntryFree k) : SaturatedTightHeavy k := by
  intro p q hpe hqe hlt hprefix htight hsat
  exact saturatedHeavy_of_doorPos hk hpe hqe hlt hprefix hsat
    (hlef p q hpe hqe hlt hprefix htight)

/-- The global shrunk residual: `TightLoopEntryFree k` for every `k ≥ 3`. -/
def TightLoopEntryFreeAll : Prop := ∀ k, 3 ≤ k → TightLoopEntryFree k

/-- **`SaturatedTightHeavyAll` from the shrunk residual.** -/
theorem saturatedTightHeavyAll_of_loopEntryFreeAll (hlef : TightLoopEntryFreeAll) :
    SaturatedTightHeavyAll :=
  fun k hk => saturatedTightHeavy_of_loopEntryFree hk (hlef k hk)

/-- **Theorem 2 from the shrunk residual** (verbatim `Statements.thm2` conclusion). -/
theorem thm2_of_loopEntryFree (hlef : TightLoopEntryFreeAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  ProofsAssembly.thm2_of_saturated (saturatedTightHeavyAll_of_loopEntryFreeAll hlef)

end ProofsRFrame

end Hunter

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsConfinement

/-!
# Theorem 2 — the recursion branch (long exitless paths)

This file attacks the last mathematically open piece of Hunter's Theorem 2: extending
`thm2_base_unconditional` (`j_k(ℓ) ≤ i_k(ℓ)` for `0 < ℓ ≤ k(k−1)(k−2)`) to **all** lengths,
i.e. into the region `ℓ > k(k−1)(k−2)` where `j_k` uses its `+3`-per-backtrack recursion.

The paper's appendix never wrote this proof.  See `PROGRESS-recursion.md` for the full
analysis; the headline structural results proved here are:

* `wtP_ge_jbase` — the summation lower bound `w(p) ≥ ℓ + ⌈ℓ/k⌉ + ⌈ℓ/(k(k−1))⌉ − 3`, holding
  for **every** exitless path (all lengths, no base-region restriction).  This is the base
  *formula* value `jbase(ℓ)`, which is `≤ j_k(ℓ)` (equal on the base region, strictly smaller
  in the recursion region).
* `wtP_decompose` — the **exact** weight split `w(p) = (ℓ−1) + (⌈ℓ/k⌉−1) + excess(p)`, where
  `excess(p) = Σ_{r=3}^{k} #{r+-edges}` is the total weight carried by the `≥3`-weight
  boundary edges.  This isolates the recursion gap into a single combinatorial quantity.
* `thm2_of_frontier` — the clean **reduction**: `thm2` (all `ℓ`), i.e. `j_k(ℓ) ≤ i_k(ℓ)` with
  the verbatim `Statements.thm2` shape, follows from the pure edge-count frontier
  `ExcessFrontier k`, divorced from all the `sInf`/`j`-recursion bookkeeping.
* `excess_frontier_base` — the frontier holds on the base region (it is exactly
  `prp_3edgebound`), re-deriving `thm2_base_unconditional` through the new reduction.
* `j_rec_unfold_one` — the clean one-step recursion `j_k(ℓ) = j_k(ℓ−ℓ₀) + j_k(ℓ₀) + 3`
  (recursion-region guard discharged), the engine of the `+3`-per-backtrack penalty.
* `thm2_small` — `thm2` **fully proved for `k ≤ 4`** (the recursion region is vacuous there,
  via `card_Vtx : Fintype.card (Vtx k) = k!`).

Everything is `sorry`-free and axiom-clean (`propext, Classical.choice, Quot.sound` only).
The remaining frontier (`ExcessFrontier k` in the recursion region) is a genuinely new
combinatorial fact — a level-`≥3` confinement — logged precisely in `PROGRESS-recursion.md`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsRecursion

open ProofsExitless ProofsConfinement Proved
open HPath

variable {k : ℕ}

/-! ## The unconditional-length summation bound `w(p) ≥ jbase(ℓ)` -/

/-- The edge weight never exceeds `k` (permutation words have length `k`). -/
theorem ew_le_k (hk : 1 ≤ k) (u v : Vtx k) : ew k u v ≤ k := by
  have hlen : (u : List ℕ).length = k := u.2.length
  exact (wt_spec hk (le_of_eq hlen)).2.1

/-- The summation lower bound, **for every exitless path**, without the base-region
restriction: `w(p) ≥ ℓ + ⌈ℓ/k⌉ + ⌈ℓ/(k(k−1))⌉ − 3` where `ℓ = |p|`.  (This is `wtP_ge_j`
with the `j_base` unfolding deleted; the RHS is the base *formula* value `jbase(ℓ)`, which is
`≤ j_k(ℓ)`, so this alone does **not** settle the recursion region.) -/
theorem wtP_ge_jbase {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hℓ0 : 0 < p.numVerts) :
    p.numVerts + (p.numVerts ⌈/⌉ k) + (p.numVerts ⌈/⌉ (k * (k - 1))) - 3 ≤ p.wtP := by
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ p.numVerts := hℓ0
  have h1 := Proved.prp_1edgebound hk1 hp
  have h2 := Proved.prp_2edgebound hk1 hp
  have h3 := Proved.prp_3edgebound (by omega : 2 ≤ k) hp
  have hsum := wtP_ge_edgeCounts hk1 (p := p)
  have hck1 : 1 ≤ p.numVerts ⌈/⌉ k := by
    rw [ceilDiv_succ_pred hN1 (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ p.numVerts ⌈/⌉ (k * (k - 1)) := by
    rw [ceilDiv_succ_pred hN1 (Nat.mul_pos (by omega) (by omega : 0 < k - 1))]
    exact Nat.le_add_left 1 _
  set A := p.numVerts ⌈/⌉ k
  set B := p.numVerts ⌈/⌉ (k * (k - 1))
  omega

/-! ## The exact weight decomposition -/

/-- Auxiliary: `∑_{q=1}^{k} [q ≤ e] = e` when `1 ≤ e ≤ k`. -/
theorem sum_indicator_Icc {e : ℕ} (he1 : 1 ≤ e) (hek : e ≤ k) :
    ∑ q ∈ Finset.Icc 1 k, (if q ≤ e then (1 : ℕ) else 0) = e := by
  rw [← Finset.card_filter]
  have hfilt : (Finset.Icc 1 k).filter (fun q => q ≤ e) = Finset.Icc 1 e := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt, Nat.card_Icc]
  omega

/-- **Exact full weight split.**  `w(p) = Σ_{q=1}^{k} #{q+-edges}` — the layer-cake identity
for the path weight (each edge of weight `w` contributes `1` to every layer `q ≤ w`, and edge
weights are `≤ k`). -/
theorem wtP_eq_sum_edgeCountGe {k : ℕ} (hk : 1 ≤ k) (p : HPath k) :
    p.wtP = ∑ q ∈ Finset.Icc 1 k, edgeCountGe p q := by
  have key : ∀ q : ℕ, edgeCountGe p q = ∑ i ∈ Finset.range (p.numVerts - 1),
      (if q ≤ ew k (p.vert i) (p.vert (i + 1)) then 1 else 0) := by
    intro q; rw [edgeCountGe, Finset.card_filter]
  rw [wtP_eq_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sum_indicator_Icc (ew_ge_one hk _ _) (ew_le_k hk _ _)).symm

/-- The `≥3`-weight *excess* carried by a path: the total weight of the boundary edges beyond
their first two units, `Σ_{r=3}^{k} #{r+-edges}`. -/
noncomputable def excess (p : HPath k) : ℕ := ∑ r ∈ Finset.Icc 3 k, edgeCountGe p r

/-- **Weight decomposition into the fixed part plus the excess.**  For an exitless path,
`w(p) = (ℓ−1) + (⌈ℓ/k⌉−1) + excess(p)`, where the first two summands are `prp_1edgebound`
and `prp_2edgebound` (the `1+`- and `2+`-edge counts) and the excess collects everything of
weight `≥3`.  This pins the entire recursion gap onto `excess`. -/
theorem wtP_decompose {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) :
    p.wtP = (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
  have hk1 : 1 ≤ k := by omega
  rw [wtP_eq_sum_edgeCountGe hk1 p]
  -- split off q = 1 and q = 2 from the sum over Icc 1 k
  have h13 : Finset.Icc 1 k = insert 1 (insert 2 (Finset.Icc 3 k)) := by
    apply Finset.ext; intro q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1ni : (1 : ℕ) ∉ insert 2 (Finset.Icc 3 k) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h2ni : (2 : ℕ) ∉ Finset.Icc 3 k := by
    simp only [Finset.mem_Icc]; omega
  rw [h13, Finset.sum_insert h1ni, Finset.sum_insert h2ni]
  have e1 := Proved.prp_1edgebound hk1 hp
  have e2 := Proved.prp_2edgebound hk1 hp
  rw [e1, e2, excess, Nat.add_assoc]

/-! ## The frontier and the reduction of `thm2` to it -/

/-- `edgeCountGe p 3 ≤ excess p` (the excess dominates its first layer). -/
theorem edgeCountGe3_le_excess {k : ℕ} (hk : 3 ≤ k) (p : HPath k) :
    edgeCountGe p 3 ≤ excess p := by
  apply Finset.single_le_sum (f := fun r => edgeCountGe p r) (fun i _ => Nat.zero_le _)
  simp only [Finset.mem_Icc]; omega

/-- **The recursion frontier.**  The purely combinatorial fact that, on the recursion region,
the `≥3`-weight excess of any exitless path is at least what `j_k` demands.  On the base
region this is `prp_3edgebound` (`excess_frontier_base`); in the recursion region it is the
genuinely new level-`≥3` confinement the paper never proved.  `thm2` (all lengths) follows
from this by `thm2_of_frontier`. -/
def ExcessFrontier (k : ℕ) : Prop :=
  ∀ q : HPath k, q.Exitless → 0 < q.numVerts →
    j k q.numVerts ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q

/-- **Base-region frontier** — the frontier inequality holds whenever `ℓ ≤ k(k−1)(k−2)`.
This is exactly `prp_3edgebound` repackaged through the exact weight split, and it re-derives
`thm2_base_unconditional` via `thm2_of_frontier`. -/
theorem excess_frontier_base {k : ℕ} (hk : 3 ≤ k) {q : HPath k} (hq : q.Exitless)
    (h0 : 0 < q.numVerts) (hle : q.numVerts ≤ k * (k - 1) * (k - 2)) :
    j k q.numVerts ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q := by
  have hN1 : 1 ≤ q.numVerts := h0
  have he3 := edgeCountGe3_le_excess hk q
  have h3 := Proved.prp_3edgebound (by omega : 2 ≤ k) hq
  have hck1 : 1 ≤ q.numVerts ⌈/⌉ k := by
    rw [ceilDiv_succ_pred hN1 (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ q.numVerts ⌈/⌉ (k * (k - 1)) := by
    rw [ceilDiv_succ_pred hN1 (Nat.mul_pos (by omega) (by omega : 0 < k - 1))]
    exact Nat.le_add_left 1 _
  rw [j_base (Or.inl hle)]
  omega

/-- **Reduction of `thm2` to the frontier.**  Given `ExcessFrontier k`, Hunter's Theorem 2
holds for *all* lengths: `j_k(ℓ) ≤ i_k(ℓ)`.  The proof is the exact weight split
`wtP_decompose` applied to the weight-minimising exitless witness, so all `sInf`/`j`-recursion
bookkeeping is discharged here and only the combinatorial `ExcessFrontier` remains open. -/
theorem thm2_of_frontier {k ℓ : ℕ} (hk : 3 ≤ k) (hfr : ExcessFrontier k)
    (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ := by
  obtain ⟨p, hpe, hpv⟩ := hex
  have hne : {m | ∃ q : HPath k, q.Exitless ∧ q.numVerts = ℓ ∧ q.wtP = m}.Nonempty :=
    ⟨p.wtP, p, hpe, hpv, rfl⟩
  obtain ⟨q, hqe, hqv, hqw⟩ := Nat.sInf_mem hne
  have h0 : 0 < q.numVerts := q.numVerts_pos
  calc j k ℓ = j k q.numVerts := by rw [hqv]
    _ ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q := hfr q hqe h0
    _ = q.wtP := (wtP_decompose hk hqe).symm
    _ = iExitless k ℓ := hqw

/-! ## The recursion unfolding and the size of the frontier gap -/

/-- `ℓ₀ = k(k−1)(k−2) − k > 0` for `k ≥ 3`. -/
theorem ell0_pos {k : ℕ} (hk : 3 ≤ k) : 0 < ell0 k := by
  have hm : 2 ≤ (k - 1) * (k - 2) := by
    have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
    omega
  have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
  have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  rw [heq] at hprod
  rw [ell0]; omega

/-- **Clean one-step recursion unfolding.**  For `ℓ` in the recursion region the messy
`¬(… ∨ …)` guard of `j_rec` is discharged, giving `j_k(ℓ) = j_k(ℓ−ℓ₀) + j_k(ℓ₀) + 3`. -/
theorem j_rec_unfold_one {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ : k * (k - 1) * (k - 2) < ℓ) :
    j k ℓ = j k (ℓ - ell0 k) + j k (ell0 k) + 3 := by
  apply j_rec
  have h0 := ell0_pos hk
  rw [ell0] at h0
  simp only [not_or]
  exact ⟨by omega, by omega⟩

/-! ## `thm2` for `k ≤ 4` (the recursion region is vacuous there) -/

/-- `|permsOf S| = |S|!` — the number of duplicate-free words with symbol set `S`. -/
theorem card_permsOf (S : Finset ℕ) : (permsOf S).card = Nat.factorial S.card := by
  rw [permsOf, List.toFinset_card_of_nodup
      (List.nodup_permutations _ (S.sort_nodup (· ≤ ·))),
      List.length_permutations, Finset.length_sort]

/-- The vertex set has exactly `k!` elements. -/
theorem card_Vtx (k : ℕ) : Fintype.card (Vtx k) = Nat.factorial k := by
  have e : Vtx k ≃ {w // w ∈ permsOf (Finset.Icc 1 k)} :=
    Equiv.subtypeEquivRight (fun w =>
      ⟨fun h => mem_permsOf.mpr ⟨h.1, h.2⟩,
       fun h => ⟨(mem_permsOf.mp h).1, (mem_permsOf.mp h).2⟩⟩)
  rw [Fintype.card_congr e, Fintype.card_coe, card_permsOf, Nat.card_Icc, Nat.add_sub_cancel]

/-- **thm2 for `k ≤ 4`.**  For `k ∈ {3,4}` the recursion region `ℓ > k(k−1)(k−2)` is empty
(every exitless path has `≤ k! = k(k−1)(k−2)` vertices), so Theorem 2 reduces entirely to the
base region and is fully proved unconditionally. -/
theorem thm2_small {k ℓ : ℕ} (hk : 3 ≤ k) (hk4 : k ≤ 4) (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ := by
  obtain ⟨p, hpe, hpv⟩ := hex
  have hℓ0 : 0 < ℓ := by rw [← hpv]; exact p.numVerts_pos
  have hcard : ℓ ≤ Fintype.card (Vtx k) := by rw [← hpv]; exact p.nodup.length_le_card
  rw [card_Vtx] at hcard
  have hle : ℓ ≤ k * (k - 1) * (k - 2) := by
    rcases (by omega : k = 3 ∨ k = 4) with rfl | rfl <;>
      · simp only [Nat.factorial] at hcard; omega
  exact thm2_base_unconditional hk hℓ0 hle ⟨p, hpe, hpv⟩

end ProofsRecursion

end Hunter


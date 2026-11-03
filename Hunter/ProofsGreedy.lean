/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMore
import Hunter.ProofsRecursion

/-!
# The greedy witness path `g_ℓ` (Hunter §6.4, `greedy-g`)

Explicit construction of an **exitless** `HPath k` on `ℓ` vertices of weight exactly
`j_k(ℓ)`, giving the upper bound `i_k(ℓ) ≤ j_k(ℓ)` on the base region.

This file constructs the single-marked-2-loop witness (τ-switches only), valid for
`0 < ℓ ≤ k(k−1)`.  The vertices are, in order, the `σ`-orbits of the block bases
`baseV c = (W0.rotate c) ++ [k]` where `W0 = [1,…,k−1]`; consecutive blocks are joined by
the weight-2 door `τ`.  Everything is elementary rotation arithmetic — the marked-2-loop
confinement machinery is *not* needed for the construction (only for the matching lower
bound, proved elsewhere).

Helpers live in `namespace Hunter.ProofsGreedy`; the target `greedy_g` (base range) in
`namespace Hunter.Proved`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsGreedy

open ProofsExitless ProofsRecursion

variable {k : ℕ}

/-! ## The loop word `W0 = [1,…,k−1]` and the block base word -/

/-- The loop word `W0 = [1,2,…,k−1]`. -/
def W0 (k : ℕ) : List ℕ := List.range' 1 (k - 1)

theorem W0_length (k : ℕ) : (W0 k).length = k - 1 := by
  simp [W0]

theorem W0_nodup (k : ℕ) : (W0 k).Nodup := by
  simp [W0, List.nodup_range']

theorem mem_W0 {k x : ℕ} : x ∈ W0 k ↔ 1 ≤ x ∧ x ≤ k - 1 := by
  rw [W0, List.mem_range'_1]
  omega

theorem W0_toFinset (k : ℕ) : (W0 k).toFinset = Finset.Icc 1 (k - 1) := by
  ext x
  rw [List.mem_toFinset, mem_W0, Finset.mem_Icc]

/-- The block-base word `(W0.rotate c) ++ [k]` is a permutation word (marker `k` appended to
a rotation of `[1,…,k−1]`). -/
theorem baseW_isPermWord (hk : 1 ≤ k) (c : ℕ) :
    IsPermWord k ((W0 k).rotate c ++ [k]) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨(List.rotate_perm (W0 k) c).nodup_iff.mpr (W0_nodup k), List.nodup_singleton k, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_rotate, mem_W0] at ha
    omega
  · have hrot : ((W0 k).rotate c).toFinset = (W0 k).toFinset :=
      List.toFinset_eq_of_perm _ _ (List.rotate_perm (W0 k) c)
    rw [List.toFinset_append, hrot, W0_toFinset]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, List.mem_toFinset, List.mem_singleton]
    omega

/-- The block base vertex `baseV c`, with marker `k` and cyclic part `W0.rotate c`. -/
noncomputable def baseV (k : ℕ) (hk : 1 ≤ k) (c : ℕ) : Vtx k :=
  ⟨(W0 k).rotate c ++ [k], baseW_isPermWord hk c⟩

@[simp] theorem baseV_val (hk : 1 ≤ k) (c : ℕ) :
    (baseV k hk c : List ℕ) = (W0 k).rotate c ++ [k] := rfl

/-- The greedy vertex at position `i`: the `(i%k)`-th `σ`-iterate of the `(i/k)`-th base. -/
noncomputable def gV (k : ℕ) (hk : 1 ≤ k) (i : ℕ) : Vtx k :=
  sigma^[i % k] (baseV k hk (i / k))

/-! ## `div`/`mod` bookkeeping across a step -/

theorem div_mod_add (hk : 0 < k) (q r : ℕ) (hr : r < k) :
    (k * q + r) / k = q ∧ (k * q + r) % k = r := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr

/-- Non-boundary step: `(i+1)` stays in the same block, offset advances. -/
theorem step_within (hk : 1 ≤ k) {i : ℕ} (h : i % k < k - 1) :
    (i + 1) / k = i / k ∧ (i + 1) % k = i % k + 1 := by
  have h2 : i + 1 = k * (i / k) + (i % k + 1) := by have := Nat.div_add_mod i k; omega
  rw [h2]; exact div_mod_add hk _ _ (by omega)

/-- Boundary step: `(i+1)` opens a new block at offset `0`. -/
theorem step_boundary (hk : 1 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    (i + 1) / k = i / k + 1 ∧ (i + 1) % k = 0 := by
  have hexp : k * (i / k + 1) + 0 = k * (i / k) + k := by ring
  have h2 : i + 1 = k * (i / k + 1) + 0 := by have := Nat.div_add_mod i k; omega
  rw [h2]; exact div_mod_add hk _ _ hk

/-! ## The `σ`-step and boundary relations -/

/-- Within a block, the greedy step is exactly `σ` (weight 1). -/
theorem gV_succ_within (hk : 1 ≤ k) {i : ℕ} (h : i % k < k - 1) :
    gV k hk (i + 1) = sigma (gV k hk i) := by
  obtain ⟨hd, hm⟩ := step_within hk h
  unfold gV
  rw [hd, hm, Function.iterate_succ_apply']

/-- At a block boundary, `σ` of the last vertex re-enters the block start `= gV (k·(i/k))`. -/
theorem gV_boundary_sigma (hk : 1 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    sigma (gV k hk i) = gV k hk (k * (i / k)) := by
  have hrhs : gV k hk (k * (i / k)) = baseV k hk (i / k) := by
    unfold gV
    rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hk, Function.iterate_zero_apply]
  rw [hrhs]
  have hlhs : sigma (gV k hk i) = sigma^[i % k + 1] (baseV k hk (i / k)) := by
    unfold gV; exact (Function.iterate_succ_apply' sigma (i % k) _).symm
  rw [hlhs, show i % k + 1 = k from by omega, sigma_iter_period]

/-! ## Word values of the greedy vertices -/

/-- The underlying word of `gV`. -/
theorem gV_val (hk : 1 ≤ k) (i : ℕ) :
    (gV k hk i : List ℕ) = ((W0 k).rotate (i / k) ++ [k]).rotate (i % k) := by
  unfold gV
  rw [sigma_iter_val, baseV_val]

/-- Rotating `L ++ [a]` by `|L|` brings the last symbol to the front. -/
theorem rot_snoc (L : List ℕ) (a : ℕ) : (L ++ [a]).rotate L.length = a :: L := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- Word form of the last vertex of a block (boundary source): `k :: (W0.rotate c)`. -/
theorem gV_boundary_word_i (hk : 1 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    (gV k hk i : List ℕ) = k :: (W0 k).rotate (i / k) := by
  rw [gV_val, h, show k - 1 = ((W0 k).rotate (i / k)).length from by
    rw [List.length_rotate, W0_length], rot_snoc]

/-- Word form of the first vertex of the next block (boundary target). -/
theorem gV_boundary_word_succ (hk : 1 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    (gV k hk (i + 1) : List ℕ) = ((W0 k).rotate (i / k)).rotate 1 ++ [k] := by
  obtain ⟨hd, hm⟩ := step_boundary hk h
  rw [gV_val, hd, hm, List.rotate_zero, List.rotate_rotate]

/-! ## Edge weights of the greedy path -/

/-- Within a block, the edge weight is `1` (a `σ`-step). -/
theorem ew_within_eq_one (hk : 1 ≤ k) {i : ℕ} (h : i % k < k - 1) :
    ew k (gV k hk i) (gV k hk (i + 1)) = 1 := by
  rw [gV_succ_within hk h, ew_sigma hk]

/-- At a block boundary, the edge weight is `≤ 2` (a door step; never a `3+`-edge). -/
theorem ew_boundary_le_two (hk : 1 ≤ k) (hk2 : 2 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    ew k (gV k hk i) (gV k hk (i + 1)) ≤ 2 := by
  have h3 : (gV k hk i : List ℕ).drop 2 = (gV k hk (i + 1) : List ℕ).take (k - 2) := by
    rw [gV_boundary_word_i hk h, gV_boundary_word_succ hk h]
    set L := (W0 k).rotate (i / k) with hL
    have hLlen : L.length = k - 1 := by rw [hL, List.length_rotate, W0_length]
    rw [List.rotate_eq_drop_append_take (l := L) (n := 1) (by rw [hLlen]; omega)]
    have hdrop : (k :: L).drop 2 = L.drop 1 := rfl
    rw [hdrop, List.append_assoc,
      List.take_left' (l₁ := L.drop 1) (by rw [List.length_drop, hLlen]; omega)]
  exact wt_le (by norm_num) hk2 h3

/-! ## Injectivity of the greedy sequence (Nodup) -/

/-- The marker symbol `k` sits at index `(k−1)−r` of `((W0.rotate c) ++ [k]).rotate r`. -/
theorem marker_index (hk : 1 ≤ k) (c r : ℕ) (hr : r < k) :
    (((W0 k).rotate c ++ [k]).rotate r)[(k - 1) - r]? = some k := by
  have hlen : ((W0 k).rotate c ++ [k]).length = k := by
    rw [List.length_append, List.length_rotate, W0_length, List.length_singleton]; omega
  rw [List.getElem?_rotate (l := (W0 k).rotate c ++ [k]) (n := r) (m := (k - 1) - r)
      (by rw [hlen]; omega), hlen,
    show ((k - 1) - r + r) % k = k - 1 from by
      rw [show (k - 1) - r + r = k - 1 from by omega]; exact Nat.mod_eq_of_lt (by omega),
    List.getElem?_append_right (by rw [List.length_rotate, W0_length]),
    List.length_rotate, W0_length, show (k - 1) - (k - 1) = 0 from by omega]
  rfl

/-- The greedy sequence is injective on `{ i | i / k < k − 1 }` (each block a distinct cycle,
each offset a distinct rotation) — i.e. on the whole single-2-loop range `i < k(k−1)`. -/
theorem gV_inj (hk : 1 ≤ k) {i j : ℕ} (hik : i / k < k - 1) (hjk : j / k < k - 1)
    (h : gV k hk i = gV k hk j) : i = j := by
  have hkpos : 0 < k := hk
  have hril : i % k < k := Nat.mod_lt i hkpos
  have hrjl : j % k < k := Nat.mod_lt j hkpos
  have hw : (gV k hk i : List ℕ) = (gV k hk j : List ℕ) := by rw [h]
  have lenw : (gV k hk i : List ℕ).length = k := (gV k hk i).2.length
  have hmi : (k - 1) - i % k < (gV k hk i : List ℕ).length := by rw [lenw]; omega
  have hmj : (k - 1) - j % k < (gV k hk i : List ℕ).length := by rw [lenw]; omega
  -- `k` occurs at index `(k-1) - i%k` and at `(k-1) - j%k` in the (equal) word
  have ei : (gV k hk i : List ℕ)[(k - 1) - i % k]? = some k := by
    rw [gV_val]; exact marker_index hk (i / k) (i % k) hril
  have ej : (gV k hk i : List ℕ)[(k - 1) - j % k]? = some k := by
    rw [hw, gV_val]; exact marker_index hk (j / k) (j % k) hrjl
  have gi : (gV k hk i : List ℕ)[(k - 1) - i % k] = k := by
    have := ei; rwa [List.getElem?_eq_getElem hmi, Option.some_inj] at this
  have gj : (gV k hk i : List ℕ)[(k - 1) - j % k] = k := by
    have := ej; rwa [List.getElem?_eq_getElem hmj, Option.some_inj] at this
  have hidx : (k - 1) - i % k = (k - 1) - j % k :=
    ((gV k hk i).2.nodup.getElem_inj_iff).mp (gi.trans gj.symm)
  have hr_eq : i % k = j % k := by omega
  -- equal offsets ⇒ equal base words ⇒ equal blocks
  have hbase : (W0 k).rotate (i / k) ++ [k] = (W0 k).rotate (j / k) ++ [k] := by
    have h2 : ((W0 k).rotate (i / k) ++ [k]).rotate (i % k)
        = ((W0 k).rotate (j / k) ++ [k]).rotate (j % k) := by
      rw [← gV_val, ← gV_val]; exact hw
    rw [hr_eq] at h2
    exact List.rotate_injective (j % k) h2
  have hW : (W0 k).rotate (i / k) = (W0 k).rotate (j / k) :=
    List.append_cancel_right hbase
  have hc_eq : i / k = j / k :=
    rotate_injOn_lt (W0_nodup k) (by rw [W0_length]; omega) (by rw [W0_length]; omega) hW
  have hkci : k * (i / k) = k * (j / k) := by rw [hc_eq]
  have hi := Nat.div_add_mod i k
  have hj := Nat.div_add_mod j k
  omega

/-! ## The greedy path and its properties -/

/-- Every position `< ℓ ≤ k(k−1)` lies in a block with index `< k − 1`. -/
theorem block_lt (hk : 1 ≤ k) {ℓ i : ℕ} (hℓ : ℓ ≤ k * (k - 1)) (hi : i < ℓ) : i / k < k - 1 :=
  (Nat.div_lt_iff_lt_mul hk).mpr (by rw [Nat.mul_comm]; omega)

/-- The greedy path on `ℓ ≤ k(k−1)` vertices: the `ℓ`-prefix of the greedy sequence. -/
noncomputable def greedyP (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    HPath k :=
  ⟨(List.range ℓ).map (gV k hk),
    List.ne_nil_of_length_pos (by rw [List.length_map, List.length_range]; omega),
    by
      apply List.Nodup.map_on _ List.nodup_range
      intro i hi j hj hij
      rw [List.mem_range] at hi hj
      exact gV_inj hk (block_lt hk hℓ hi) (block_lt hk hℓ hj) hij⟩

theorem greedyP_numVerts (hk : 1 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    (greedyP k hk ℓ hℓ0 hℓ).numVerts = ℓ := by
  show ((List.range ℓ).map (gV k hk)).length = ℓ
  rw [List.length_map, List.length_range]

theorem greedyP_vert (hk : 1 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) {t : ℕ}
    (ht : t < ℓ) : (greedyP k hk ℓ hℓ0 hℓ).vert t = gV k hk t := by
  rw [vert_getElem _ (by rw [greedyP_numVerts hk hℓ0 hℓ]; exact ht)]
  -- Lean 4.35 port: `rw [List.getElem_map]` no longer matches after `show`; `simp` closes it.
  simp [greedyP]

theorem greedyP_exitless (hk : 1 ≤ k) (hk2 : 2 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1)) : (greedyP k hk ℓ hℓ0 hℓ).Exitless := by
  set p := greedyP k hk ℓ hℓ0 hℓ with hpdef
  have hnum : p.numVerts = ℓ := greedyP_numVerts hk hℓ0 hℓ
  intro he
  obtain ⟨i, hi1, hi2, hi3⟩ := he
  rw [hnum] at hi1
  have hil : i < ℓ := by omega
  have hi1l : i + 1 < ℓ := hi1
  have hvi : p.vert i = gV k hk i := greedyP_vert hk hℓ0 hℓ hil
  have hvi1 : p.vert (i + 1) = gV k hk (i + 1) := greedyP_vert hk hℓ0 hℓ hi1l
  rcases Nat.lt_or_ge (i % k) (k - 1) with hlt | hge
  · -- non-boundary: the edge has weight 1, contradicting `2 ≤ w`
    rw [hvi, hvi1, ew_within_eq_one hk hlt] at hi2
    omega
  · -- boundary: `σ` re-enters the (earlier) block start
    have hb : i % k = k - 1 := by have := Nat.mod_lt i (show 0 < k from hk); omega
    have hmul : k * (i / k) ≤ i := Nat.mul_div_le i k
    have hml : k * (i / k) < ℓ := by omega
    have hσ : sigma (p.vert i) = p.vert (k * (i / k)) := by
      rw [hvi, gV_boundary_sigma hk hb, greedyP_vert hk hℓ0 hℓ hml]
    rw [hσ, pos_vert p (by rw [hnum]; exact hml)] at hi3
    omega

theorem greedyP_wtP (hk : 1 ≤ k) (hk3 : 3 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    (greedyP k hk ℓ hℓ0 hℓ).wtP = j k ℓ := by
  set p := greedyP k hk ℓ hℓ0 hℓ with hpdef
  have hnum : p.numVerts = ℓ := greedyP_numVerts hk hℓ0 hℓ
  have hpe : p.Exitless := greedyP_exitless hk (by omega) hℓ0 hℓ
  -- no `3+`-edges: `excess = 0`
  have hexcess : excess p = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [edgeCountGe, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    have hile : i + 1 < ℓ := by rw [hnum] at hi; omega
    rw [greedyP_vert hk hℓ0 hℓ (by omega : i < ℓ), greedyP_vert hk hℓ0 hℓ hile]
    have hle2 : ew k (gV k hk i) (gV k hk (i + 1)) ≤ 2 := by
      rcases Nat.lt_or_ge (i % k) (k - 1) with hlt | hge
      · exact (ew_within_eq_one hk hlt).le.trans (by norm_num)
      · have hb : i % k = k - 1 := by have := Nat.mod_lt i (show 0 < k from hk); omega
        exact ew_boundary_le_two hk (by omega) hb
    omega
  rw [wtP_decompose hk3 hpe, hnum, hexcess,
    j_base (Or.inl (le_trans hℓ (Nat.le_mul_of_pos_right _ (show 0 < k - 2 from by omega))))]
  -- `⌈ℓ/(k(k−1))⌉ = 1` and `⌈ℓ/k⌉ ≥ 1` pin the value
  have hcd : ℓ ⌈/⌉ (k * (k - 1)) = 1 := by
    have hM : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    rw [Nat.ceilDiv_eq_add_pred_div,
      show ℓ + k * (k - 1) - 1 = (ℓ - 1) + k * (k - 1) from by omega,
      Nat.add_div_right _ hM, Nat.div_eq_of_lt (by omega)]
  have hck1 : 1 ≤ ℓ ⌈/⌉ k := by
    rw [Nat.ceilDiv_eq_add_pred_div, Nat.one_le_div_iff (by omega)]; omega
  rw [hcd]
  omega

end ProofsGreedy

namespace Proved

open ProofsGreedy

/-- **greedy-g on the single-2-loop sub-range `ℓ ≤ k(k−1)`.**  For `0 < ℓ ≤ k(k−1)` there is
an exitless `HPath k` with `ℓ` vertices of weight exactly `j_k(ℓ)` — the explicit greedy
witness (chain of complete 1-cycles joined by weight-2 `τ`/door boundary edges).  Gives
`i_k(ℓ) ≤ j_k(ℓ)` on this range (and `HasExitlessPath k ℓ`).  The full base range
`ℓ ≤ k(k−1)(k−2)` additionally needs the weight-3 `α`-jumps between marked 2-loops; see
`PROGRESS-greedy.md`. -/
theorem greedy_g_le_kk {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ ∧ p.wtP = j k ℓ := by
  have hk1 : 1 ≤ k := by omega
  exact ⟨greedyP k hk1 ℓ hℓ0 hℓ, greedyP_exitless hk1 (by omega) hℓ0 hℓ,
    greedyP_numVerts hk1 hℓ0 hℓ, greedyP_wtP hk1 hk hℓ0 hℓ⟩

/-- **thm2-equality on the single-2-loop sub-range `ℓ ≤ k(k−1)`.**  `i_k(ℓ) = j_k(ℓ)` for
`0 < ℓ ≤ k(k−1)`: the `≤` is the greedy witness `greedy_g_le_kk`, the `≥` is the
(unconditional) lower bound `thm2_base_unconditional`.  This is the verbatim `thm2_equality`
restricted from `ℓ ≤ k(k−1)(k−2)` to the α-free sub-range; the existence guard `hex` is
supplied by the greedy witness itself.  See `PROGRESS-greedy.md`. -/
theorem thm2_equality_le_kk {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    iExitless k ℓ = j k ℓ := by
  obtain ⟨p, hpe, hpv, hpw⟩ := greedy_g_le_kk hk hℓ0 hℓ
  have hle : iExitless k ℓ ≤ j k ℓ := by
    rw [← hpw]; exact Nat.sInf_le ⟨p, hpe, hpv, rfl⟩
  have hge : j k ℓ ≤ iExitless k ℓ :=
    thm2_base_unconditional hk hℓ0 (le_trans hℓ (Nat.le_mul_of_pos_right _ (by omega)))
      ⟨p, hpe, hpv⟩
  omega

end Proved

end Hunter

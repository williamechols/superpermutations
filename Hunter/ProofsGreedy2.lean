/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsGreedy

/-!
# The greedy witness `g_ℓ` on the full base region (Hunter §6.4, `greedy-g`)

Extends `Hunter/ProofsGreedy.lean` (single marked 2-loop, `ℓ ≤ k(k−1)`) to the **full base
region** `ℓ ≤ k(k−1)(k−2)`, closing `greedy_g` and the base-region equality clause.

The construction is a two-level fractal of the single-loop one.  Position `i` decomposes as
`i = k*(k−1)*L + k*c + r` with the loop index `L = i / (k(k−1))`, the 1-cycle index within
the loop `c = (i/k) % (k−1)`, and the offset `r = i % k`.  The `L`-th marked 2-loop uses the
**loop word** `LW k L = (W0(k−1)).rotate L ++ [k−1]` — literally the single-loop block-base
word for `k−1` letters, with second-level marker `k−1`.  The outer marker `k` is appended and
fixed throughout.  Consecutive loops are joined by the weight-3 `α`-jump; within a loop the
weight-2 `τ`/door boundary and weight-1 `σ` steps are as before.

The one genuinely new obligation vs. the single-loop case is **cross-loop distinctness**: the
loop words must have distinct rotation classes.  This is discharged by the *same* marker
argument one level down — `marker_pins` pins a rotation by the unique position of a marker
symbol — applied to the second-level marker `k−1`.

Helpers live in `namespace Hunter.ProofsGreedy2`; the targets `greedy_g` /
`thm2_equality_base` in `namespace Hunter.Proved`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsGreedy2

open ProofsExitless ProofsRecursion ProofsGreedy Proved
open HPath

variable {k : ℕ}

/-! ## The marker lemma: a rotation is pinned by the position of a unique marker symbol -/

/-- The marker symbol `M` sits at index `|S| − r` of `(S ++ [M]).rotate r` (for `r ≤ |S|`). -/
theorem marker_last_getElem (S : List ℕ) (M : ℕ) {r : ℕ} (hr : r ≤ S.length) :
    ((S ++ [M]).rotate r)[S.length - r]? = some M := by
  have hlen : (S ++ [M]).length = S.length + 1 := by simp
  rw [List.getElem?_rotate (l := S ++ [M]) (n := r) (m := S.length - r) (by rw [hlen]; omega),
    hlen,
    show (S.length - r + r) % (S.length + 1) = S.length from by
      rw [show S.length - r + r = S.length from by omega]; exact Nat.mod_eq_of_lt (by omega),
    List.getElem?_append_right (by omega), show S.length - S.length = 0 from by omega]
  rfl

/-- **Marker pins the rotation.**  If `(S₁ ++ [M]).rotate a = (S₂ ++ [M]).rotate b` (with equal
lengths, `a,b` in range, and the left word duplicate-free) then the rotations agree and the
cores agree: `a = b` and `S₁ = S₂`.  The unique occurrence of `M` fixes the rotation amount. -/
theorem marker_pins {S₁ S₂ : List ℕ} {M a b : ℕ}
    (hnd : (S₁ ++ [M]).Nodup) (hlen : S₁.length = S₂.length)
    (ha : a ≤ S₁.length) (hb : b ≤ S₂.length)
    (h : (S₁ ++ [M]).rotate a = (S₂ ++ [M]).rotate b) : a = b ∧ S₁ = S₂ := by
  set W := (S₁ ++ [M]).rotate a with hW
  have hWnd : W.Nodup := (List.rotate_perm (S₁ ++ [M]) a).nodup_iff.mpr hnd
  have hWlen : W.length = S₁.length + 1 := by rw [hW, List.length_rotate]; simp
  have gi : W[S₁.length - a]? = some M := marker_last_getElem S₁ M ha
  have gj : W[S₂.length - b]? = some M := by rw [h]; exact marker_last_getElem S₂ M hb
  have hia : S₁.length - a < W.length := by rw [hWlen]; omega
  have hib : S₂.length - b < W.length := by rw [hWlen, ← hlen]; omega
  have gi' : W[S₁.length - a] = M := by
    have := gi; rwa [List.getElem?_eq_getElem hia, Option.some_inj] at this
  have gj' : W[S₂.length - b] = M := by
    have := gj; rwa [List.getElem?_eq_getElem hib, Option.some_inj] at this
  have hidx : S₁.length - a = S₂.length - b := (hWnd.getElem_inj_iff).mp (gi'.trans gj'.symm)
  have hab : a = b := by rw [hlen] at ha; omega
  refine ⟨hab, ?_⟩
  have hfull : S₁ ++ [M] = S₂ ++ [M] := by
    apply List.rotate_injective a
    rw [← hab] at h; exact h
  exact List.append_cancel_right hfull

/-! ## The loop word, cycle base word, and the greedy vertex -/

/-- The `L`-th **loop word** `LW k L = (W0(k−1)).rotate L ++ [k−1]` — the single-loop block base
word for `k−1` letters, with second-level marker `k−1`. -/
def LW (k L : ℕ) : List ℕ := (ProofsGreedy.W0 (k - 1)).rotate L ++ [k - 1]

/-- `LW k L` is a permutation word on `k−1` letters. -/
theorem LW_isPermWord (hk : 2 ≤ k) (L : ℕ) : IsPermWord (k - 1) (LW k L) :=
  ProofsGreedy.baseW_isPermWord (k := k - 1) (by omega) L

/-- Appending the outer marker `k` to a `(k−1)`-permutation word gives a `k`-permutation word. -/
theorem snoc_marker_isPermWord (hk : 1 ≤ k) {S : List ℕ} (hS : IsPermWord (k - 1) S) :
    IsPermWord k (S ++ [k]) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨hS.nodup, List.nodup_singleton k, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    have hmem : a ∈ Finset.Icc 1 (k - 1) := by
      rw [← hS.toFinset_eq]; exact List.mem_toFinset.mpr ha
    rw [Finset.mem_Icc] at hmem; omega
  · rw [List.toFinset_append, hS.toFinset_eq]
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, List.mem_toFinset, List.mem_singleton]
    omega

/-- The **cycle base word** at global 1-cycle index `Q`: the `(Q % (k−1))`-rotation of the loop
word `LW k (Q / (k−1))`. -/
def SWord (k Q : ℕ) : List ℕ := (LW k (Q / (k - 1))).rotate (Q % (k - 1))

theorem SWord_isPermWord (hk : 2 ≤ k) (Q : ℕ) : IsPermWord (k - 1) (SWord k Q) :=
  isPermWord_rotate (LW_isPermWord hk _) _

theorem SWord_length (hk : 2 ≤ k) (Q : ℕ) : (SWord k Q).length = k - 1 :=
  (SWord_isPermWord hk Q).length

theorem cVword_isPermWord (hk : 3 ≤ k) (Q : ℕ) : IsPermWord k (SWord k Q ++ [k]) :=
  snoc_marker_isPermWord (by omega) (SWord_isPermWord (by omega) Q)

/-- The cycle base vertex at index `Q`. -/
noncomputable def cV (k : ℕ) (hk : 3 ≤ k) (Q : ℕ) : Vtx k :=
  ⟨SWord k Q ++ [k], cVword_isPermWord hk Q⟩

@[simp] theorem cV_val (hk : 3 ≤ k) (Q : ℕ) : (cV k hk Q : List ℕ) = SWord k Q ++ [k] := rfl

/-- The greedy vertex at position `i`: the `(i%k)`-th `σ`-iterate of the `(i/k)`-th cycle base. -/
noncomputable def gV2 (k : ℕ) (hk : 3 ≤ k) (i : ℕ) : Vtx k := sigma^[i % k] (cV k hk (i / k))

theorem gV2_val (hk : 3 ≤ k) (i : ℕ) :
    (gV2 k hk i : List ℕ) = (SWord k (i / k) ++ [k]).rotate (i % k) := by
  unfold gV2; rw [sigma_iter_val, cV_val]

/-! ## Injectivity of the greedy sequence (Nodup) -/

/-- Every position `< ℓ ≤ k(k−1)(k−2)` lies in a marked 2-loop with index `< k − 2`. -/
theorem loop_lt (hk : 3 ≤ k) {ℓ i : ℕ} (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) (hi : i < ℓ) :
    i / (k * (k - 1)) < k - 2 := by
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) (by omega))).mpr
  have hassoc : (k - 2) * (k * (k - 1)) = k * (k - 1) * (k - 2) := by ring
  omega

/-- **The greedy sequence is injective** on the base range `i / (k(k−1)) < k − 2`.  Two levels
of the marker argument: the outer marker `k` pins the offset `i % k`, then the inner marker
`k−1` pins the within-loop cycle `(i/k) % (k−1)`, and `rotate_injOn_lt` on `W0(k−1)` pins the
loop `i / (k(k−1))`. -/
theorem gV2_inj (hk : 3 ≤ k) {i j : ℕ}
    (hib : i / (k * (k - 1)) < k - 2) (hjb : j / (k * (k - 1)) < k - 2)
    (h : gV2 k hk i = gV2 k hk j) : i = j := by
  have hkpos : 0 < k := by omega
  have hril : i % k < k := Nat.mod_lt i hkpos
  have hrjl : j % k < k := Nat.mod_lt j hkpos
  have hw : (gV2 k hk i : List ℕ) = (gV2 k hk j : List ℕ) := by rw [h]
  rw [gV2_val, gV2_val] at hw
  -- Level 1: outer marker `k` pins `i % k = j % k` and `SWord (i/k) = SWord (j/k)`.
  have hnd1 : (SWord k (i / k) ++ [k]).Nodup := (cVword_isPermWord hk (i / k)).nodup
  have hlen1 : (SWord k (i / k)).length = (SWord k (j / k)).length := by
    rw [SWord_length (by omega) (i / k), SWord_length (by omega) (j / k)]
  have hai : i % k ≤ (SWord k (i / k)).length := by
    rw [SWord_length (by omega) (i / k)]; omega
  have haj : j % k ≤ (SWord k (j / k)).length := by
    rw [SWord_length (by omega) (j / k)]; omega
  obtain ⟨hr_eq, hS⟩ := marker_pins hnd1 hlen1 hai haj hw
  -- Level 2: inner marker `k−1` pins the within-loop cycle and the loop word.
  rw [SWord, SWord, LW, LW] at hS
  have hnd2 : ((ProofsGreedy.W0 (k - 1)).rotate (i / k / (k - 1)) ++ [k - 1]).Nodup :=
    (LW_isPermWord (by omega) (i / k / (k - 1))).nodup
  have hlen2 : ((ProofsGreedy.W0 (k - 1)).rotate (i / k / (k - 1))).length
      = ((ProofsGreedy.W0 (k - 1)).rotate (j / k / (k - 1))).length := by
    rw [List.length_rotate, List.length_rotate]
  have hci : i / k % (k - 1) ≤ ((ProofsGreedy.W0 (k - 1)).rotate (i / k / (k - 1))).length := by
    rw [List.length_rotate, ProofsGreedy.W0_length]
    have := Nat.mod_lt (i / k) (show 0 < k - 1 by omega); omega
  have hcj : j / k % (k - 1) ≤ ((ProofsGreedy.W0 (k - 1)).rotate (j / k / (k - 1))).length := by
    rw [List.length_rotate, ProofsGreedy.W0_length]
    have := Nat.mod_lt (j / k) (show 0 < k - 1 by omega); omega
  obtain ⟨hc_eq, hU⟩ := marker_pins hnd2 hlen2 hci hcj hS
  -- `rotate_injOn_lt` on `W0(k−1)` pins the loop index.
  have hLi : i / k / (k - 1) = i / (k * (k - 1)) := Nat.div_div_eq_div_mul i k (k - 1)
  have hLj : j / k / (k - 1) = j / (k * (k - 1)) := Nat.div_div_eq_div_mul j k (k - 1)
  have hL_eq : i / k / (k - 1) = j / k / (k - 1) := by
    apply rotate_injOn_lt (ProofsGreedy.W0_nodup (k - 1))
      (by rw [ProofsGreedy.W0_length]; omega) (by rw [ProofsGreedy.W0_length]; omega) hU
  -- Reassemble: equal loop, equal cycle, equal offset ⇒ equal `i/k`, hence equal `i`.
  have hQ : i / k = j / k := by
    have e3i := Nat.div_add_mod (i / k) (k - 1)
    have e3j := Nat.div_add_mod (j / k) (k - 1)
    rw [hL_eq, hc_eq] at e3i
    omega
  have hkQ : k * (i / k) = k * (j / k) := by rw [hQ]
  have hi := Nat.div_add_mod i k
  have hj := Nat.div_add_mod j k
  omega

/-! ## Step / boundary relations and edge weights -/

/-- Within a 1-cycle, the greedy step is exactly `σ` (weight 1). -/
theorem gV2_succ_within (hk : 3 ≤ k) {i : ℕ} (h : i % k < k - 1) :
    gV2 k hk (i + 1) = sigma (gV2 k hk i) := by
  obtain ⟨hd, hm⟩ := ProofsGreedy.step_within (show 1 ≤ k by omega) h
  unfold gV2; rw [hd, hm, Function.iterate_succ_apply']

/-- At any block boundary, `σ` of the last vertex re-enters the current block start
`= gV2 (k·(i/k))` (already visited). -/
theorem gV2_boundary_sigma (hk : 3 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    sigma (gV2 k hk i) = gV2 k hk (k * (i / k)) := by
  have hk1 : 1 ≤ k := by omega
  have hrhs : gV2 k hk (k * (i / k)) = cV k hk (i / k) := by
    unfold gV2
    rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hk1, Function.iterate_zero_apply]
  rw [hrhs]
  have hlhs : sigma (gV2 k hk i) = sigma^[i % k + 1] (cV k hk (i / k)) := by
    unfold gV2; exact (Function.iterate_succ_apply' sigma (i % k) _).symm
  rw [hlhs, show i % k + 1 = k from by omega, sigma_iter_period]

/-- Word form of the last vertex of a block (any boundary source): `k :: SWord (i/k)`. -/
theorem gV2_boundary_word_i (hk : 3 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    (gV2 k hk i : List ℕ) = k :: SWord k (i / k) := by
  rw [gV2_val, h, show k - 1 = (SWord k (i / k)).length from (SWord_length (by omega) _).symm,
    ProofsGreedy.rot_snoc]

/-- Word form of the first vertex of the next block (any boundary target). -/
theorem gV2_boundary_word_succ (hk : 3 ≤ k) {i : ℕ} (h : i % k = k - 1) :
    (gV2 k hk (i + 1) : List ℕ) = SWord k (i / k + 1) ++ [k] := by
  obtain ⟨hd, hm⟩ := ProofsGreedy.step_boundary (show 1 ≤ k by omega) h
  rw [gV2_val, hd, hm, List.rotate_zero]

/-- Within a loop, a cycle-boundary advances the base word by a single rotation. -/
theorem SWord_succ_cycle (hk : 3 ≤ k) {Q : ℕ} (hc : Q % (k - 1) < k - 2) :
    SWord k (Q + 1) = (SWord k Q).rotate 1 := by
  obtain ⟨hd, hm⟩ := ProofsGreedy.step_within (k := k - 1) (show (1 : ℕ) ≤ k - 1 by omega)
    (i := Q) (show Q % (k - 1) < (k - 1) - 1 by omega)
  rw [SWord, SWord, hd, hm, List.rotate_rotate]

/-- At a loop boundary, the base word jumps to the next loop word `LW k (L+1)`. -/
theorem SWord_loop (hk : 3 ≤ k) {Q : ℕ} (hc : Q % (k - 1) = k - 2) :
    SWord k (Q + 1) = LW k (Q / (k - 1) + 1) := by
  obtain ⟨hd, hm⟩ := ProofsGreedy.step_boundary (k := k - 1) (show (1 : ℕ) ≤ k - 1 by omega)
    (i := Q) (show Q % (k - 1) = (k - 1) - 1 by omega)
  rw [SWord, hd, hm, List.rotate_zero]

/-- The loop-boundary source's base word is `(k−1) :: (W0(k−1)).rotate L`. -/
theorem SWord_loop_src (hk : 3 ≤ k) {Q : ℕ} (hc : Q % (k - 1) = k - 2) :
    SWord k Q = (k - 1) :: (ProofsGreedy.W0 (k - 1)).rotate (Q / (k - 1)) := by
  rw [SWord, LW, hc,
    show k - 2 = ((ProofsGreedy.W0 (k - 1)).rotate (Q / (k - 1))).length from by
      rw [List.length_rotate, ProofsGreedy.W0_length]; omega]
  exact ProofsGreedy.rot_snoc _ _

/-- Within a 1-cycle the edge weight is `1`. -/
theorem ew_within_eq_one (hk : 3 ≤ k) {i : ℕ} (h : i % k < k - 1) :
    ew k (gV2 k hk i) (gV2 k hk (i + 1)) = 1 := by
  rw [gV2_succ_within hk h, ew_sigma (by omega)]

/-- A cycle boundary within a loop has weight `≤ 2` (a door step). -/
theorem ew_cycle_le_two (hk : 3 ≤ k) {i : ℕ} (hb : i % k = k - 1)
    (hc : i / k % (k - 1) < k - 2) : ew k (gV2 k hk i) (gV2 k hk (i + 1)) ≤ 2 := by
  have h3 : (gV2 k hk i : List ℕ).drop 2 = (gV2 k hk (i + 1) : List ℕ).take (k - 2) := by
    rw [gV2_boundary_word_i hk hb, gV2_boundary_word_succ hk hb, SWord_succ_cycle hk hc]
    set L := SWord k (i / k) with hL
    have hLlen : L.length = k - 1 := by rw [hL, SWord_length (by omega)]
    rw [List.rotate_eq_drop_append_take (l := L) (n := 1) (by rw [hLlen]; omega)]
    have hdrop : (k :: L).drop 2 = L.drop 1 := rfl
    rw [hdrop, List.append_assoc,
      List.take_left' (l₁ := L.drop 1) (by rw [List.length_drop, hLlen]; omega)]
  exact wt_le (by norm_num) (by omega : 2 ≤ k) h3

/-- A loop boundary (`α`-jump) has weight `≤ 3`. -/
theorem ew_loop_le_three (hk : 3 ≤ k) {i : ℕ} (hb : i % k = k - 1)
    (hc : i / k % (k - 1) = k - 2) : ew k (gV2 k hk i) (gV2 k hk (i + 1)) ≤ 3 := by
  have h3 : (gV2 k hk i : List ℕ).drop 3 = (gV2 k hk (i + 1) : List ℕ).take (k - 3) := by
    rw [gV2_boundary_word_i hk hb, SWord_loop_src hk hc,
      gV2_boundary_word_succ hk hb, SWord_loop hk hc, LW]
    set R := (ProofsGreedy.W0 (k - 1)).rotate (i / k / (k - 1)) with hR
    have hRlen : R.length = k - 2 := by rw [hR, List.length_rotate, ProofsGreedy.W0_length]; omega
    have hW01 : (ProofsGreedy.W0 (k - 1)).rotate (i / k / (k - 1) + 1) = R.rotate 1 := by
      rw [hR, List.rotate_rotate]
    rw [hW01, List.rotate_eq_drop_append_take (l := R) (n := 1) (by rw [hRlen]; omega)]
    have hdrop : (k :: (k - 1) :: R).drop 3 = R.drop 1 := rfl
    rw [hdrop, List.append_assoc, List.append_assoc,
      List.take_left' (l₁ := R.drop 1) (by rw [List.length_drop, hRlen]; omega)]
  exact wt_le (by norm_num) (by omega : 3 ≤ k) h3

/-! ## Localizing the weight-3 edges and counting them -/

/-- The two-level residue identity: `i mod (k(k−1)) = k·((i/k) mod (k−1)) + i mod k`. -/
theorem mod_mul_add (_hk : 3 ≤ k) (i : ℕ) :
    i % (k * (k - 1)) = k * (i / k % (k - 1)) + i % k := by
  have e1 : i = k * (k - 1) * (i / (k * (k - 1))) + i % (k * (k - 1)) :=
    (Nat.div_add_mod i (k * (k - 1))).symm
  have e2 : i / (k * (k - 1)) = i / k / (k - 1) := (Nat.div_div_eq_div_mul i k (k - 1)).symm
  have e4 : i = k * (i / k) + i % k := (Nat.div_add_mod i k).symm
  have hkQ : k * (i / k) = k * (k - 1) * (i / k / (k - 1)) + k * (i / k % (k - 1)) := by
    conv_lhs => rw [← Nat.div_add_mod (i / k) (k - 1)]
    rw [Nat.mul_add, ← Nat.mul_assoc]
  rw [e2] at e1
  omega

/-- A weight-3 edge sits exactly at a loop boundary, so its residue is `k(k−1) − 1`. -/
theorem loopbdry_mod (hk : 3 ≤ k) {i : ℕ} (hb : i % k = k - 1) (hc : i / k % (k - 1) = k - 2) :
    i % (k * (k - 1)) = k * (k - 1) - 1 := by
  rw [mod_mul_add hk, hb, hc]
  have h1 : k * (k - 1) = k * (k - 2) + k := by
    rw [show k - 1 = (k - 2) + 1 from by omega, Nat.mul_add, Nat.mul_one]
  omega

/-- A `≥3`-weight greedy edge forces a loop boundary. -/
theorem edge3_loopbdry (hk : 3 ≤ k) {i : ℕ}
    (h3 : 3 ≤ ew k (gV2 k hk i) (gV2 k hk (i + 1))) :
    i % k = k - 1 ∧ i / k % (k - 1) = k - 2 := by
  rcases Nat.lt_or_ge (i % k) (k - 1) with hlt | hge
  · rw [ew_within_eq_one hk hlt] at h3; omega
  · have hb : i % k = k - 1 := by have := Nat.mod_lt i (show 0 < k by omega); omega
    rcases Nat.lt_or_ge (i / k % (k - 1)) (k - 2) with hcc | hcc
    · have := ew_cycle_le_two hk hb hcc; omega
    · have hc : i / k % (k - 1) = k - 2 := by
        have := Nat.mod_lt (i / k) (show 0 < k - 1 by omega); omega
      exact ⟨hb, hc⟩

/-- Counting bound: a set of loop-boundary positions in `range (ℓ−1)` has `≤ (ℓ−1)/m`
elements (map each to its loop index `i/m`; injective since the residue is pinned). -/
theorem card_le_of_loopbdry {m ℓ : ℕ} (hm : 0 < m) {F : Finset ℕ}
    (hF : ∀ i ∈ F, i < ℓ - 1 ∧ i % m = m - 1) : F.card ≤ (ℓ - 1) / m := by
  rw [← Finset.card_range ((ℓ - 1) / m)]
  apply Finset.card_le_card_of_injOn (fun i => i / m)
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    obtain ⟨hlt, hmod⟩ := hF i hi
    have hdecomp : i = m * (i / m) + (m - 1) := by have := Nat.div_add_mod i m; omega
    have hB : (i / m + 1) * m = m * (i / m) + m := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    have hle : (i / m + 1) * m ≤ ℓ - 1 := by omega
    have hlt2 : i / m + 1 ≤ (ℓ - 1) / m := (Nat.le_div_iff_mul_le hm).mpr hle
    omega
  · intro i hi i' hi' heq
    simp only [Finset.mem_coe] at hi hi'
    obtain ⟨_, hmod⟩ := hF i hi
    obtain ⟨_, hmod'⟩ := hF i' hi'
    have heq' : i / m = i' / m := heq
    have hdi : i = m * (i / m) + (m - 1) := by have := Nat.div_add_mod i m; omega
    have hdi' : i' = m * (i' / m) + (m - 1) := by have := Nat.div_add_mod i' m; omega
    have hprod : m * (i / m) = m * (i' / m) := by rw [heq']
    omega

/-! ## The greedy path and its three properties -/

/-- The greedy path on `ℓ ≤ k(k−1)(k−2)` vertices. -/
noncomputable def greedyP2 (k : ℕ) (hk : 3 ≤ k) (ℓ : ℕ) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) : HPath k :=
  ⟨(List.range ℓ).map (gV2 k hk),
    List.ne_nil_of_length_pos (by rw [List.length_map, List.length_range]; omega),
    by
      apply List.Nodup.map_on _ List.nodup_range
      intro i hi j hj hij
      rw [List.mem_range] at hi hj
      exact gV2_inj hk (loop_lt hk hℓ hi) (loop_lt hk hℓ hj) hij⟩

theorem greedyP2_numVerts (hk : 3 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) :
    (greedyP2 k hk ℓ hℓ0 hℓ).numVerts = ℓ := by
  show ((List.range ℓ).map (gV2 k hk)).length = ℓ
  rw [List.length_map, List.length_range]

theorem greedyP2_vert (hk : 3 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) {t : ℕ}
    (ht : t < ℓ) : (greedyP2 k hk ℓ hℓ0 hℓ).vert t = gV2 k hk t := by
  rw [vert_getElem _ (by rw [greedyP2_numVerts hk hℓ0 hℓ]; exact ht)]
  -- Lean 4.35 port: `rw [List.getElem_map]` no longer matches after `show`; `simp` closes it.
  simp [greedyP2]

theorem greedyP2_exitless (hk : 3 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) : (greedyP2 k hk ℓ hℓ0 hℓ).Exitless := by
  set p := greedyP2 k hk ℓ hℓ0 hℓ with hpdef
  have hnum : p.numVerts = ℓ := greedyP2_numVerts hk hℓ0 hℓ
  intro he
  obtain ⟨i, hi1, hi2, hi3⟩ := he
  rw [hnum] at hi1
  have hil : i < ℓ := by omega
  have hi1l : i + 1 < ℓ := hi1
  have hvi : p.vert i = gV2 k hk i := greedyP2_vert hk hℓ0 hℓ hil
  have hvi1 : p.vert (i + 1) = gV2 k hk (i + 1) := greedyP2_vert hk hℓ0 hℓ hi1l
  rcases Nat.lt_or_ge (i % k) (k - 1) with hlt | hge
  · rw [hvi, hvi1, ew_within_eq_one hk hlt] at hi2
    omega
  · have hb : i % k = k - 1 := by have := Nat.mod_lt i (show 0 < k from by omega); omega
    have hmul : k * (i / k) ≤ i := Nat.mul_div_le i k
    have hml : k * (i / k) < ℓ := by omega
    have hσ : sigma (p.vert i) = p.vert (k * (i / k)) := by
      rw [hvi, gV2_boundary_sigma hk hb, greedyP2_vert hk hℓ0 hℓ hml]
    rw [hσ, pos_vert p (by rw [hnum]; exact hml)] at hi3
    omega

theorem greedyP2_wtP (hk : 3 ≤ k) {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) :
    (greedyP2 k hk ℓ hℓ0 hℓ).wtP = j k ℓ := by
  set p := greedyP2 k hk ℓ hℓ0 hℓ with hpdef
  have hnum : p.numVerts = ℓ := greedyP2_numVerts hk hℓ0 hℓ
  have hpe : p.Exitless := greedyP2_exitless hk hℓ0 hℓ
  -- All greedy edges have weight ≤ 3.
  have hle3 : ∀ i, i + 1 < ℓ → ew k (gV2 k hk i) (gV2 k hk (i + 1)) ≤ 3 := by
    intro i _
    rcases Nat.lt_or_ge (i % k) (k - 1) with hlt | hge
    · rw [ew_within_eq_one hk hlt]; norm_num
    · have hb : i % k = k - 1 := by have := Nat.mod_lt i (show 0 < k from by omega); omega
      rcases Nat.lt_or_ge (i / k % (k - 1)) (k - 2) with hcc | hcc
      · exact le_trans (ew_cycle_le_two hk hb hcc) (by norm_num)
      · have hc : i / k % (k - 1) = k - 2 := by
          have := Nat.mod_lt (i / k) (show 0 < k - 1 from by omega); omega
        exact ew_loop_le_three hk hb hc
  -- No `≥4`-weight edges.
  have hr0 : ∀ r, 4 ≤ r → edgeCountGe p r = 0 := by
    intro r hr
    rw [edgeCountGe, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    have hile : i + 1 < ℓ := by rw [hnum] at hi; omega
    rw [greedyP2_vert hk hℓ0 hℓ (by omega : i < ℓ), greedyP2_vert hk hℓ0 hℓ hile]
    have := hle3 i hile
    omega
  -- Hence the excess collapses to the weight-3 layer.
  have hexc : excess p = edgeCountGe p 3 := by
    rw [excess, show Finset.Icc 3 k = insert 3 (Finset.Icc 4 k) from by
          apply Finset.ext; intro q; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
        Finset.sum_eq_zero (fun r hr => hr0 r (by rw [Finset.mem_Icc] at hr; omega)),
        Nat.add_zero]
  -- The weight-3 layer is bounded by the loop-boundary count `D = ⌈ℓ/(k(k−1))⌉ − 1`.
  have hD : edgeCountGe p 3 ≤ ℓ ⌈/⌉ (k * (k - 1)) - 1 := by
    have hmpos : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    have hDeq : ℓ ⌈/⌉ (k * (k - 1)) - 1 = (ℓ - 1) / (k * (k - 1)) := by
      rw [ceilDiv_succ_pred (by omega : 1 ≤ ℓ) hmpos, Nat.add_sub_cancel]
    rw [edgeCountGe, hnum, hDeq]
    apply card_le_of_loopbdry hmpos
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hir, h3⟩ := hi
    have hile : i + 1 < ℓ := by omega
    rw [greedyP2_vert hk hℓ0 hℓ (by omega : i < ℓ), greedyP2_vert hk hℓ0 hℓ hile] at h3
    obtain ⟨hb, hc⟩ := edge3_loopbdry hk h3
    exact ⟨by omega, loopbdry_mod hk hb hc⟩
  -- Combine the exact decomposition with the unconditional lower bound.
  have hjbeq : j k ℓ = ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3 := j_base (Or.inl hℓ)
  have hlow := wtP_ge_jbase hk hpe (by rw [hnum]; exact hℓ0)
  rw [hnum] at hlow
  have hdec := wtP_decompose hk hpe
  rw [hnum, hexc] at hdec
  have hck1 : 1 ≤ ℓ ⌈/⌉ k := by
    rw [ceilDiv_succ_pred (by omega : 1 ≤ ℓ) (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ ℓ ⌈/⌉ (k * (k - 1)) := by
    rw [ceilDiv_succ_pred (by omega : 1 ≤ ℓ) (Nat.mul_pos (by omega) (by omega))]
    exact Nat.le_add_left 1 _
  omega

end ProofsGreedy2

namespace Proved

open ProofsGreedy2

/-- **greedy-g on the full base region** (`main_version.tex` §6.4, verbatim `Statements.greedy_g`
type).  For `0 < ℓ ≤ k(k−1)(k−2)` there is an exitless `HPath k` with `ℓ` vertices of weight
exactly `j_k(ℓ)`: the explicit two-level greedy witness (`k−2` marked 2-loops of complete
1-cycles joined by weight-3 `α`-jumps, cycles joined by weight-2 `τ` doors, `σ` steps within).
Gives `i_k(ℓ) ≤ j_k(ℓ)` on the whole base region (and `HasExitlessPath k ℓ`). -/
theorem greedy_g {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) :
    ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ ∧ p.wtP = j k ℓ :=
  ⟨greedyP2 k hk ℓ hℓ0 hℓ, greedyP2_exitless hk hℓ0 hℓ, greedyP2_numVerts hk hℓ0 hℓ,
    greedyP2_wtP hk hℓ0 hℓ⟩

/-- **thm2-equality on the full base region** (unconditional).  `i_k(ℓ) = j_k(ℓ)` for
`0 < ℓ ≤ k(k−1)(k−2)`: the `≤` is `greedy_g`, the `≥` is `thm2_base_unconditional`.  The
existence guard is supplied by the greedy witness itself, so no `HasExitlessPath` hypothesis is
needed. -/
theorem thm2_equality_base {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) : iExitless k ℓ = j k ℓ := by
  obtain ⟨p, hpe, hpv, hpw⟩ := greedy_g hk hℓ0 hℓ
  have hle : iExitless k ℓ ≤ j k ℓ := by rw [← hpw]; exact Nat.sInf_le ⟨p, hpe, hpv, rfl⟩
  have hge : j k ℓ ≤ iExitless k ℓ := thm2_base_unconditional hk hℓ0 hℓ ⟨p, hpe, hpv⟩
  omega

/-- **thm2-equality** (verbatim `Statements.thm2_equality` type — full base region, with the
redundant `HasExitlessPath` guard the paper's statement carries).  Wraps `thm2_equality_base`. -/
theorem thm2_equality {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) (_hex : HasExitlessPath k ℓ) :
    iExitless k ℓ = j k ℓ :=
  thm2_equality_base hk hℓ0 hℓ

/-- **Existence on the base region.**  `HasExitlessPath k ℓ` for every `0 < ℓ ≤ k(k−1)(k−2)`,
`k ≥ 3` — the greedy witness supplies the path.  Discharges the `hexists`/`hpivot` existence
leaf used across the `b2`/`thm1` reduction chains (`PROGRESS-b2.md`, `PROGRESS-gb2.md`). -/
theorem hasExitlessPath_base {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) : HasExitlessPath k ℓ :=
  ⟨greedyP2 k hk ℓ hℓ0 hℓ, greedyP2_exitless hk hℓ0 hℓ, greedyP2_numVerts hk hℓ0 hℓ⟩

/-- **Existence at the pivot** (the exact `hexists` leaf shape).  `HasExitlessPath k (k(k−1)(k−2))`
for all `k ≥ 3`. -/
theorem hasExitlessPath_pivot (k : ℕ) (hk : 3 ≤ k) :
    HasExitlessPath k (k * (k - 1) * (k - 2)) :=
  hasExitlessPath_base hk (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (le_refl _)

end Proved

end Hunter

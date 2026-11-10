/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Defs
import Hunter.Appendix

/-!
# Proofs of the "exitless" track of Hunter, *A New Lower Bound for Superpermutations*

This file proves the mathematically central **normal-form** results about exitless paths and
the appendix edge-count propositions, together with the base-region case of Theorem 2.

The centerpiece is the **rotation-structure lemma** (`vert_eq_sigma_iter`): every exitless
path decomposes, blockwise in windows of `k` consecutive vertices, into complete traversals
of distinct 1-cycles.  From it we derive:

* the *fresh-cycle forcing* and *no-re-entry* normal-form lemmas;
* `prp_periodicedges`, `prp_1edgebound`, `prp_2edgebound`;
* `clm_1cyclesubset`, `clm_phi_necessity`, `clm_phi_sufficiency`, `clm_prefix`;
* `j_at_pivot`;
* the summation identity `w(p) ≥ Σ_q #{q+-edges}` and `thm2_base`.

Helper lemmas live in `namespace Hunter.ProofsExitless`; the targets copied verbatim from
`Hunter/Statements.lean` are proved as `Hunter.Proved.<name>`.
-/

namespace Hunter
namespace ProofsExitless

open List
open scoped Classical

variable {k : ℕ}

/-! ## Ported: rotations by distinct amounts `< length` differ (from Coeff2/Auxiliary) -/

/-- Left-rotations of a duplicate-free word by distinct amounts `< length` differ.
Ported verbatim from `Coeff2/Auxiliary.lean` (`rotate_injOn_lt`). -/
theorem rotate_injOn_lt {w : List ℕ} (hnd : w.Nodup) {a b : ℕ} (ha : a < w.length)
    (hb : b < w.length) (heq : w.rotate a = w.rotate b) : a = b := by
  have h0 : 0 < w.length := by omega
  have e := congrArg (fun l => l[0]?) heq
  simp only [List.getElem?_rotate h0, Nat.zero_add, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at e
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at e
  exact (hnd.getElem_inj_iff).mp (Option.some_inj.mp e)

/-! ## `σ` iteration and the 1-cycle orbit -/

/-- `σ^r` acts on the underlying word as rotation by `r`. -/
theorem sigma_iter_val (r : ℕ) (v : Vtx k) : (sigma^[r] v).1 = (v : List ℕ).rotate r := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((sigma^[n] v : Vtx k) : List ℕ).rotate 1 = (v : List ℕ).rotate (n + 1)
    rw [ih, List.rotate_rotate, Nat.add_comm]

/-- `σ^r v` reduces mod the word length (`= k`). -/
theorem sigma_iter_mod (r : ℕ) (v : Vtx k) : sigma^[r % k] v = sigma^[r] v := by
  apply Subtype.ext
  rw [sigma_iter_val, sigma_iter_val]
  have h : r % k = r % (v : List ℕ).length := by rw [v.2.length]
  rw [h, List.rotate_mod]

/-- `σ^k v = v` (rotate by the length). -/
theorem sigma_iter_period (v : Vtx k) : sigma^[k] v = v := by
  apply Subtype.ext
  rw [sigma_iter_val]
  have h : (v : List ℕ).rotate k = (v : List ℕ).rotate (v : List ℕ).length := by rw [v.2.length]
  rw [h, List.rotate_length]

/-- On a permutation word, rotations by distinct amounts `< k` are distinct. -/
theorem sigma_iter_inj (v : Vtx k) {a b : ℕ} (ha : a < k) (hb : b < k)
    (h : sigma^[a] v = sigma^[b] v) : a = b := by
  have hlen : (v : List ℕ).length = k := v.2.length
  apply rotate_injOn_lt v.2.nodup (a := a) (b := b) (by rw [hlen]; exact ha)
    (by rw [hlen]; exact hb)
  have := congrArg (Subtype.val) h
  rwa [sigma_iter_val, sigma_iter_val] at this

/-! ## Path index / position helpers -/

open HPath

theorem vert_getElem (p : HPath k) {t : ℕ} (ht : t < p.numVerts) :
    p.vert t = p.verts[t]'ht := by
  have ht' : t < p.verts.length := ht
  rw [HPath.vert]; exact List.getD_eq_getElem _ _ ht'

theorem vert_mem (p : HPath k) {t : ℕ} (ht : t < p.numVerts) : p.vert t ∈ p.verts := by
  rw [vert_getElem p ht]; exact List.getElem_mem _

theorem pos_lt (p : HPath k) {v : Vtx k} (hv : v ∈ p.verts) : p.pos v < p.numVerts :=
  List.idxOf_lt_length_of_mem hv

theorem pos_of_not_mem (p : HPath k) {v : Vtx k} (hv : v ∉ p.verts) :
    p.pos v = p.numVerts :=
  List.idxOf_of_notMem hv

theorem vert_pos (p : HPath k) {v : Vtx k} (hv : v ∈ p.verts) : p.vert (p.pos v) = v := by
  show p.verts.getD (p.verts.idxOf v) (p.verts.head p.ne) = v
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hv)]
  exact List.getElem_idxOf _

theorem pos_vert (p : HPath k) {t : ℕ} (ht : t < p.numVerts) : p.pos (p.vert t) = t := by
  rw [vert_getElem p ht]
  exact p.nodup.idxOf_getElem t ht

theorem vert_inj (p : HPath k) {a b : ℕ} (ha : a < p.numVerts) (hb : b < p.numVerts)
    (h : p.vert a = p.vert b) : a = b := by
  have := congrArg p.pos h
  rwa [pos_vert p ha, pos_vert p hb] at this

/-! ## The 1-cycle `cyc` as the `σ`-orbit -/

theorem mem_cyc {u v : Vtx k} : u ∈ cyc v ↔ rotClass u.1 = rotClass v.1 := by
  rw [cyc, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem rotClass_sigma_iter (r : ℕ) (v : Vtx k) :
    rotClass (sigma^[r] v).1 = rotClass v.1 := by
  rw [sigma_iter_val]
  have h1 : (v : List ℕ) ~r (v : List ℕ).rotate r := ⟨r, rfl⟩
  exact rotClass_eq_iff.mpr h1.symm

theorem sigma_iter_mem_cyc (r : ℕ) (v : Vtx k) : sigma^[r] v ∈ cyc v :=
  mem_cyc.mpr (rotClass_sigma_iter r v)

theorem mem_cyc_iff_exists (hk : 1 ≤ k) {u v : Vtx k} :
    u ∈ cyc v ↔ ∃ r < k, u = sigma^[r] v := by
  rw [mem_cyc]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (rotClass_eq_iff.mp h).symm
    refine ⟨n % k, Nat.mod_lt _ hk, ?_⟩
    apply Subtype.ext
    rw [sigma_iter_val]
    have hmod : n % k = n % (v : List ℕ).length := by rw [v.2.length]
    rw [hmod, List.rotate_mod, hn]
  · rintro ⟨r, -, rfl⟩
    exact rotClass_sigma_iter r v

theorem cyc_eq_image (hk : 1 ≤ k) (v : Vtx k) :
    cyc v = (Finset.range k).image (fun r => sigma^[r] v) := by
  ext u
  rw [mem_cyc_iff_exists hk, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, Finset.mem_range.mpr hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, Finset.mem_range.mp hr, rfl⟩

theorem card_cyc (hk : 1 ≤ k) (v : Vtx k) : (cyc v).card = k := by
  rw [cyc_eq_image hk, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact sigma_iter_inj v (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-! ## Weight-1 edges are exactly the `σ`-steps; the operational exitless rule -/

theorem ew_ge_one (hk : 1 ≤ k) (u v : Vtx k) : 1 ≤ ew k u v :=
  (wt_spec hk (le_of_eq u.2.length)).1

theorem ew_eq_one_iff (hk : 1 ≤ k) {u v : Vtx k} : ew k u v = 1 ↔ v = sigma u := by
  constructor
  · intro h
    apply Subtype.ext
    have := eq_rho_of_wt_one hk u.2 v.2 h
    rw [this]; rfl
  · rintro rfl; exact ew_sigma hk u

/-- The operational form of the exitless rule: across each edge, either we take the
weight-1 `σ`-step, or `σ` of the source has already been visited (at position `≤ i`). -/
theorem exitless_step (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) :
    p.vert (i + 1) = sigma (p.vert i) ∨ p.pos (sigma (p.vert i)) ≤ i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hp
  refine ⟨i, hi, ?_, h2⟩
  have hne : ew k (p.vert i) (p.vert (i + 1)) ≠ 1 := by
    intro he
    exact h1 ((ew_eq_one_iff hk).mp he)
  have hge := ew_ge_one hk (p.vert i) (p.vert (i + 1))
  omega

/-! ## Arithmetic helpers for the block decomposition -/

theorem mul_add_mod_lt (a b c : ℕ) (h : c < b) : (b * a + c) % b = c := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]

theorem mul_add_div_lt (a b c : ℕ) (hb : 0 < b) (h : c < b) :
    b * ((b * a + c) / b) = b * a := by
  rw [Nat.mul_add_div hb, Nat.div_eq_of_lt h, Nat.add_zero]

/-! ## The rotation-structure lemma (centerpiece / normal form)

Every exitless path decomposes, in windows of `k` consecutive vertices, into complete
traversals of distinct 1-cycles: the vertex at position `i` is the `(i mod k)`-th rotation
of the start of its block `k·⌊i/k⌋`.  All three normal-form facts — fresh-cycle forcing,
no-re-entry, and the blockwise decomposition — are consequences. -/

/-- **Rotation-structure lemma.**  For an exitless path, `p[i] = σ^{i mod k}(p[k·⌊i/k⌋])`. -/
theorem vert_eq_sigma_iter (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    ∀ i, i < p.numVerts → p.vert i = sigma^[i % k] (p.vert (k * (i / k))) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    set B := k * (i / k) with hBdef
    set m := i % k with hmdef
    have hdm : B + m = i := by rw [hBdef, hmdef]; exact Nat.div_add_mod i k
    have hmk : m < k := by rw [hmdef]; exact Nat.mod_lt i hk
    have hB_dvd : k ∣ B := ⟨i / k, hBdef⟩
    -- Prior blocks are complete traversals of their 1-cycle:
    have blockComplete : ∀ (C0 r : ℕ), k ∣ C0 → C0 + k ≤ i → r < k →
        p.vert (C0 + r) = sigma^[r] (p.vert C0) := by
      intro C0 r hdvd hle hr
      obtain ⟨q, rfl⟩ := hdvd
      have hlt_i : k * q + r < i := by omega
      have hlt_n : k * q + r < p.numVerts := lt_trans hlt_i hi
      have H := IH (k * q + r) hlt_i hlt_n
      rw [mul_add_mod_lt q k r hr, mul_add_div_lt q k r hk hr] at H
      exact H
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- block start
      have hBi : B = i := by omega
      rw [hm0, hBi]; simp
    · -- i % k = m ≥ 1: forced weight-1 step from the previous vertex
      have hi_pos : 1 ≤ i := by omega
      have hIHi' : p.vert (i - 1) = sigma^[m - 1] (p.vert B) := by
        have hlt_i : i - 1 < i := by omega
        have hlt_n : i - 1 < p.numVerts := by omega
        have H := IH (i - 1) hlt_i hlt_n
        have hrepr : i - 1 = k * (i / k) + (m - 1) := by rw [← hBdef]; omega
        rw [show (i - 1) % k = m - 1 from by
              rw [hrepr, mul_add_mod_lt (i / k) k (m - 1) (by omega)],
            show k * ((i - 1) / k) = B from by
              rw [hrepr, mul_add_div_lt (i / k) k (m - 1) hk (by omega), ← hBdef]] at H
        exact H
      have hsm : sigma^[m] (p.vert B) = sigma (p.vert (i - 1)) := by
        rw [hIHi']
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        rw [Function.iterate_succ_apply']
      rw [hsm]
      have hi'succ : (i - 1) + 1 = i := by omega
      have hstep := exitless_step hk hp (i := i - 1) (by rw [hi'succ]; exact hi)
      rw [hi'succ] at hstep
      rcases hstep with hgood | hbad
      · exact hgood
      · exfalso
        rw [← hsm] at hbad
        set j := p.pos (sigma^[m] (p.vert B)) with hjdef
        have hj_lt_n : j < p.numVerts := by omega
        have hwmem : sigma^[m] (p.vert B) ∈ p.verts := by
          by_contra hcon
          have := pos_of_not_mem p hcon
          rw [← hjdef] at this; omega
        have hvj : p.vert j = sigma^[m] (p.vert B) := by rw [hjdef]; exact vert_pos p hwmem
        rcases lt_or_ge j B with hjB | hBj
        · -- j lies in a strictly earlier block ⇒ re-entered 1-cycle ⇒ contradiction
          set B' := k * (j / k) with hB'def
          have hB'_dvd : k ∣ B' := ⟨j / k, hB'def⟩
          have hjdm : k * (j / k) + j % k = j := Nat.div_add_mod j k
          have hr0k : j % k < k := Nat.mod_lt j hk
          have hj_lt_B : j < k * (i / k) := by rw [← hBdef]; exact hjB
          have hquot : j / k < i / k := by
            by_contra hc
            push Not at hc
            have h1 : k * (i / k) ≤ k * (j / k) := Nat.mul_le_mul (le_refl k) hc
            have h2 : k * (j / k) ≤ j := by omega
            omega
          have hB'k_le_B : B' + k ≤ B := by
            have h2 : k * (j / k + 1) ≤ k * (i / k) := Nat.mul_le_mul (le_refl k) hquot
            rw [hB'def, hBdef]
            calc k * (j / k) + k = k * (j / k + 1) := by ring
              _ ≤ k * (i / k) := h2
          have hB'k_le_i : B' + k ≤ i := by omega
          have hjvert : p.vert j = sigma^[j % k] (p.vert B') := by
            have hbc := blockComplete B' (j % k) hB'_dvd hB'k_le_i hr0k
            rw [show B' + j % k = j from by rw [hB'def]; exact hjdm] at hbc
            exact hbc
          have hcls : rotClass (p.vert B).1 = rotClass (p.vert B').1 := by
            have e1 := rotClass_sigma_iter m (p.vert B)
            have e2 := rotClass_sigma_iter (j % k) (p.vert B')
            have heq : sigma^[m] (p.vert B) = sigma^[j % k] (p.vert B') := by
              rw [← hvj]; exact hjvert
            rw [← e1, heq]; exact e2
          obtain ⟨r1, hr1k, hr1eq⟩ := (mem_cyc_iff_exists hk).mp (mem_cyc.mpr hcls)
          have hbc1 := blockComplete B' r1 hB'_dvd hB'k_le_i hr1k
          rw [← hr1eq] at hbc1
          have hlt1 : B' + r1 < B := by omega
          have hn1 : B' + r1 < p.numVerts := by omega
          have hnB : B < p.numVerts := by omega
          have := vert_inj p hn1 hnB hbc1
          omega
        · -- j lies in the current block ⇒ would equal i, contradicting j ≤ i-1
          set d := j - B with hddef
          have hdk : d < k := by omega
          have hjeq : j = k * (i / k) + d := by rw [← hBdef]; omega
          have hIHj : p.vert j = sigma^[d] (p.vert B) := by
            have hlt_i : j < i := by omega
            have hlt_n : j < p.numVerts := lt_trans hlt_i hi
            have H := IH j hlt_i hlt_n
            rw [show j % k = d from by rw [hjeq, mul_add_mod_lt (i / k) k d hdk],
                show k * (j / k) = B from by
                  rw [hjeq, mul_add_div_lt (i / k) k d hk hdk, ← hBdef]] at H
            exact H
          have hww : sigma^[m] (p.vert B) = sigma^[d] (p.vert B) := by rw [← hvj]; exact hIHj
          have hmd : m = d := sigma_iter_inj (p.vert B) hmk hdk hww
          omega

/-! ## Immediate corollaries: fresh-cycle forcing and no re-entry -/

/-- **Fresh-cycle forcing (normal form).**  Every position inside a block equals the
corresponding `σ`-rotation of the block's start — so entering a fresh 1-cycle forces a
complete traversal. -/
theorem block_is_full_cycle (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {B r : ℕ}
    (hdvd : k ∣ B) (hr : r < k) (hB : B + r < p.numVerts) :
    p.vert (B + r) = sigma^[r] (p.vert B) := by
  obtain ⟨q, rfl⟩ := hdvd
  have S := vert_eq_sigma_iter hk hp (k * q + r) hB
  rwa [mul_add_mod_lt q k r hr, mul_add_div_lt q k r hk hr] at S

/-- **No re-entry (normal form).**  An earlier *complete* block (`B + k ≤ B'`) and any later
block start `B'` lie in distinct 1-cycles: a 1-cycle is never re-entered. -/
theorem no_reentry (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {B B' : ℕ}
    (hdvd : k ∣ B) (hBk : B + k ≤ B') (hB'n : B' < p.numVerts) :
    rotClass (p.vert B).1 ≠ rotClass (p.vert B').1 := by
  intro hcls
  have hmem : p.vert B' ∈ cyc (p.vert B) := mem_cyc.mpr hcls.symm
  obtain ⟨r1, hr1k, hr1eq⟩ := (mem_cyc_iff_exists hk).mp hmem
  have hbc := block_is_full_cycle hk hp hdvd hr1k (by omega : B + r1 < p.numVerts)
  rw [← hr1eq] at hbc
  have hlt : B + r1 < B' := by omega
  have := vert_inj p (by omega) hB'n hbc
  omega

/-! ## Arithmetic on `%`/`/` for the periodic-edge structure -/

theorem mod_eq_pred_of_dvd_succ (hk : 1 ≤ k) {i : ℕ} (h : k ∣ (i + 1)) :
    i % k = k - 1 := by
  obtain ⟨q, hq⟩ := h
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h1
    · rw [h0, Nat.mul_zero] at hq; omega
    · exact h1
  have hkq : k * (q - 1) + k = k * q := by
    cases q with
    | zero => omega
    | succ n => rw [Nat.succ_sub_one, Nat.mul_succ]
  have hirepr : i = k * (q - 1) + (k - 1) := by omega
  rw [hirepr, mul_add_mod_lt (q - 1) k (k - 1) (by omega)]

theorem succ_mod_div_of_not_dvd (hk : 1 ≤ k) {i : ℕ} (h : ¬ k ∣ (i + 1)) :
    (i + 1) % k = i % k + 1 ∧ (i + 1) / k = i / k := by
  have hik : i % k < k := Nat.mod_lt i hk
  have hlt : i % k + 1 < k := by
    rcases Nat.lt_or_ge (i % k + 1) k with h1 | h1
    · exact h1
    · exfalso; apply h
      refine ⟨i / k + 1, ?_⟩
      have hd := Nat.div_add_mod i k
      have hik2 : i % k + 1 = k := by omega
      rw [Nat.mul_add, Nat.mul_one]; omega
  have hrepr : i + 1 = k * (i / k) + (i % k + 1) := by have := Nat.div_add_mod i k; omega
  refine ⟨?_, ?_⟩
  · rw [hrepr, mul_add_mod_lt (i / k) k (i % k + 1) hlt]
  · rw [hrepr, Nat.mul_add_div hk, Nat.div_eq_of_lt hlt, Nat.add_zero]

/-- Within a block, the next vertex is the `σ`-step (a weight-1 edge). -/
theorem vert_succ (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hnd : ¬ k ∣ (i + 1)) :
    p.vert (i + 1) = sigma (p.vert i) := by
  have hi' : i < p.numVerts := by omega
  have S1 := vert_eq_sigma_iter hk hp (i + 1) hi
  have S0 := vert_eq_sigma_iter hk hp i hi'
  obtain ⟨hmod, hdiv⟩ := succ_mod_div_of_not_dvd hk hnd
  rw [S1, hdiv, hmod, Function.iterate_succ_apply', ← S0]

/-- At a block boundary the step is *not* a `σ`-step (hence weight `≥ 2`): `σ(p[i])` is the
already-visited block start. -/
theorem vert_succ_ne (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) :
    p.vert (i + 1) ≠ sigma (p.vert i) := by
  have hi' : i < p.numVerts := by omega
  have S0 := vert_eq_sigma_iter hk hp i hi'
  have him := mod_eq_pred_of_dvd_succ hk hd
  have key : sigma (p.vert i) = p.vert (k * (i / k)) := by
    rw [S0]
    have hstep := (Function.iterate_succ_apply' sigma (i % k) (p.vert (k * (i / k)))).symm
    have hexp : (i % k).succ = k := by omega
    rw [hstep, hexp, sigma_iter_period]
  rw [key]
  intro heq
  have hblt : k * (i / k) < i + 1 := by have := Nat.div_add_mod i k; omega
  have hb : k * (i / k) < p.numVerts := by omega
  have := vert_inj p hi hb heq
  omega

end ProofsExitless

/-! ## Targets (statements copied verbatim from `Hunter/Statements.lean`) -/

namespace Proved

open ProofsExitless
open scoped Classical

/-! ### A few more helpers -/

theorem sigma_iter_succ' {k : ℕ} (n : ℕ) (v : Vtx k) :
    sigma (sigma^[n] v) = sigma^[n + 1] v := by rw [Function.iterate_succ_apply']

theorem last_eq_vert {k : ℕ} (p : HPath k) : p.last = p.vert (p.numVerts - 1) := by
  have h : p.numVerts - 1 < p.numVerts := by have := p.numVerts_pos; omega
  rw [HPath.last]
  exact (List.getLast_eq_getElem p.ne).trans (vert_getElem p h).symm

theorem vtx_zero_elim (u v : Vtx 0) : u = v := by
  apply Subtype.ext
  have hu : (u : List ℕ).toFinset = ∅ := by
    have h := u.2.2; rwa [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0)] at h
  have hv : (v : List ℕ).toFinset = ∅ := by
    have h := v.2.2; rwa [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0)] at h
  rw [List.toFinset_eq_empty_iff] at hu hv
  rw [hu, hv]

/-- **strongly exitless ⇒ `k ∣ |p|`**: no partial terminal block, since `σ` of the last
vertex would be an unvisited fresh rotation (or force re-entry). -/
theorem dvd_numVerts_of_stronglyExitless {k : ℕ} (hk : 1 ≤ k) {p : HPath k}
    (hp : p.StronglyExitless) : k ∣ p.numVerts := by
  obtain ⟨hpe, hlast⟩ := hp
  by_contra hnd
  have hN : 1 ≤ p.numVerts := p.numVerts_pos
  have hrk : p.numVerts % k < k := Nat.mod_lt _ hk
  have hr1 : 1 ≤ p.numVerts % k := by
    rcases Nat.eq_zero_or_pos (p.numVerts % k) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hnd
    · exact h
  have hdmN : k * (p.numVerts / k) + p.numVerts % k = p.numVerts := Nat.div_add_mod _ _
  have hNm1 : p.numVerts - 1 < p.numVerts := by omega
  have hS := vert_eq_sigma_iter hk hpe (p.numVerts - 1) hNm1
  have hrepr : p.numVerts - 1 = k * (p.numVerts / k) + (p.numVerts % k - 1) := by omega
  rw [show (p.numVerts - 1) % k = p.numVerts % k - 1 from by
        rw [hrepr, mul_add_mod_lt (p.numVerts / k) k (p.numVerts % k - 1) (by omega)],
      show k * ((p.numVerts - 1) / k) = k * (p.numVerts / k) from by
        rw [hrepr, mul_add_div_lt (p.numVerts / k) k (p.numVerts % k - 1) hk (by omega)]] at hS
  have hlv : p.last = p.vert (p.numVerts - 1) := last_eq_vert p
  rw [hlv, hS,
      sigma_iter_succ' (p.numVerts % k - 1) (p.vert (k * (p.numVerts / k))),
      show p.numVerts % k - 1 + 1 = p.numVerts % k from by omega] at hlast
  set B := k * (p.numVerts / k) with hBdef
  have hBdvd : k ∣ B := ⟨p.numVerts / k, hBdef⟩
  set j := p.pos (sigma^[p.numVerts % k] (p.vert B)) with hjdef
  have hjlt : j < p.numVerts := pos_lt p hlast
  have hvj : p.vert j = sigma^[p.numVerts % k] (p.vert B) := vert_pos p hlast
  rcases lt_or_ge j B with hjB | hBj
  · have hj_lt_B : j < k * (p.numVerts / k) := by rw [← hBdef]; exact hjB
    have hquot : j / k < p.numVerts / k := by
      by_contra hc; push Not at hc
      have h1 : k * (p.numVerts / k) ≤ k * (j / k) := Nat.mul_le_mul (le_refl k) hc
      have h2 : k * (j / k) ≤ j := by have := Nat.div_add_mod j k; omega
      omega
    have hB'dvd : k ∣ k * (j / k) := ⟨j / k, rfl⟩
    have hB'k : k * (j / k) + k ≤ B := by
      have h2 : k * (j / k + 1) ≤ k * (p.numVerts / k) := Nat.mul_le_mul (le_refl k) hquot
      rw [hBdef]
      calc k * (j / k) + k = k * (j / k + 1) := by ring
        _ ≤ k * (p.numVerts / k) := h2
    have hBn : B < p.numVerts := by rw [hBdef]; omega
    have hjvert := vert_eq_sigma_iter hk hpe j hjlt
    have hcls : rotClass (p.vert B).1 = rotClass (p.vert (k * (j / k))).1 := by
      have e1 := rotClass_sigma_iter (p.numVerts % k) (p.vert B)
      have e2 := rotClass_sigma_iter (j % k) (p.vert (k * (j / k)))
      have heq : sigma^[p.numVerts % k] (p.vert B) = sigma^[j % k] (p.vert (k * (j / k))) := by
        rw [← hvj]; exact hjvert
      rw [← e1, heq]; exact e2
    exact no_reentry hk hpe hB'dvd hB'k hBn hcls.symm
  · set d := j - B with hddef
    have hjb2 : d < k := by omega
    have hjrepr : j = k * (p.numVerts / k) + d := by rw [← hBdef]; omega
    have hjstruct := vert_eq_sigma_iter hk hpe j hjlt
    rw [show j % k = d from by rw [hjrepr, mul_add_mod_lt (p.numVerts / k) k d hjb2],
        show k * (j / k) = B from by
          rw [hjrepr, mul_add_div_lt (p.numVerts / k) k d hk hjb2, ← hBdef]] at hjstruct
    have hww : sigma^[p.numVerts % k] (p.vert B) = sigma^[d] (p.vert B) := by
      rw [← hvj]; exact hjstruct
    have := sigma_iter_inj (p.vert B) hrk hjb2 hww
    omega

/-- **clm-1cyclesubset** — a strongly exitless path is a disjoint union of full 1-cycles. -/
theorem clm_1cyclesubset {k : ℕ} {p : HPath k} (hp : p.StronglyExitless) :
    p.IsUnionOfCycles := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    intro v hv u _
    rw [vtx_zero_elim u v]; exact HPath.mem_vertsFinset.mpr hv
  · have hdvd := dvd_numVerts_of_stronglyExitless hk hp
    obtain ⟨hpe, _⟩ := hp
    intro v hv u hu
    have hposv : p.pos v < p.numVerts := pos_lt p hv
    have hvv : p.vert (p.pos v) = v := vert_pos p hv
    set i := p.pos v with hidef
    have hBk : k * (i / k) + k ≤ p.numVerts := by
      obtain ⟨t, ht⟩ := hdvd
      have hit : i / k < t := by
        by_contra hc; push Not at hc
        have h1 : k * t ≤ k * (i / k) := Nat.mul_le_mul (le_refl k) hc
        have h2 : k * (i / k) ≤ i := by have := Nat.div_add_mod i k; omega
        rw [ht] at hposv; omega
      have hit' : i / k + 1 ≤ t := hit
      have h2 : k * (i / k + 1) ≤ k * t := Nat.mul_le_mul (le_refl k) hit'
      rw [ht]
      calc k * (i / k) + k = k * (i / k + 1) := by ring
        _ ≤ k * t := h2
    have hS := vert_eq_sigma_iter hk hpe i hposv
    rw [mem_cyc] at hu
    have hvB : rotClass v.1 = rotClass (p.vert (k * (i / k))).1 := by
      rw [← hvv, hS]; exact rotClass_sigma_iter _ _
    have huB : u ∈ cyc (p.vert (k * (i / k))) := mem_cyc.mpr (hu.trans hvB)
    obtain ⟨r, hrk, hru⟩ := (mem_cyc_iff_exists hk).mp huB
    have hbc := block_is_full_cycle hk hpe (⟨i / k, rfl⟩ : k ∣ k * (i / k)) hrk
      (by omega : k * (i / k) + r < p.numVerts)
    rw [← hru] at hbc
    rw [HPath.mem_vertsFinset, ← hbc]
    exact vert_mem p (by omega)

/-- **clm-prefix** — the `(|p|−1)`-vertex prefix of an exitless path is exitless. -/
theorem clm_prefix {k : ℕ} {p : HPath k} (hp : p.Exitless) (h2 : 2 ≤ p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.dropLast ∧ q.Exitless := by
  have h2' : 2 ≤ p.verts.length := h2
  have hne : p.verts.dropLast ≠ [] := by
    have : 0 < p.verts.dropLast.length := by rw [List.length_dropLast]; omega
    exact List.ne_nil_of_length_pos this
  have hnodup : p.verts.dropLast.Nodup := p.nodup.sublist (List.dropLast_sublist _)
  refine ⟨⟨p.verts.dropLast, hne, hnodup⟩, rfl, ?_⟩
  set q : HPath k := ⟨p.verts.dropLast, hne, hnodup⟩ with hq
  have hqnv : q.numVerts = p.numVerts - 1 := by
    show p.verts.dropLast.length = p.verts.length - 1
    rw [List.length_dropLast]
  have hqvert : ∀ i (hi : i < q.numVerts), q.vert i = p.vert i := by
    intro i hi
    have hi' : i < p.numVerts := by rw [hqnv] at hi; omega
    rw [vert_getElem q hi, vert_getElem p hi']
    exact List.getElem_dropLast _
  have hqpos : ∀ w : Vtx k, q.pos w ≤ p.pos w := by
    intro w
    show (p.verts.dropLast).idxOf w ≤ p.verts.idxOf w
    conv_rhs => rw [← List.dropLast_append_getLast p.ne]
    by_cases hw : w ∈ p.verts.dropLast
    · exact le_of_eq (List.idxOf_append_of_mem hw).symm
    · rw [List.idxOf_append_of_notMem hw, List.idxOf_of_notMem hw]
      omega
  intro hEE
  obtain ⟨i, hi1, hi2, hi3⟩ := hEE
  have hiq : i + 1 < p.numVerts := by rw [hqnv] at hi1; omega
  have hvi : q.vert i = p.vert i := hqvert i (by omega)
  apply hp
  refine ⟨i, hiq, ?_, ?_⟩
  · rw [← hvi, ← hqvert (i + 1) hi1]; exact hi2
  · rw [← hvi]; exact lt_of_lt_of_le hi3 (hqpos _)

/-- **prp-periodicedges** — the backbone fact: a path edge has weight 1 iff it is not a
block-boundary edge. -/
theorem prp_periodicedges {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {i : ℕ} (hi : i + 1 < p.numVerts) :
    ew k (p.vert i) (p.vert (i + 1)) = 1 ↔ ¬ (k ∣ (i + 1)) := by
  rw [ew_eq_one_iff hk]
  constructor
  · intro heq hd
    exact vert_succ_ne hk hp hi hd heq
  · intro hnd
    exact vert_succ hk hp hi hnd

/-- **prp-1edgebound** — every edge has weight `≥ 1`, so there are `ℓ − 1` of them. -/
theorem prp_1edgebound {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (_hp : p.Exitless) :
    edgeCountGe p 1 = p.numVerts - 1 := by
  rw [edgeCountGe,
    Finset.filter_true_of_mem (fun i _ => ew_ge_one hk (p.vert i) (p.vert (i + 1))),
    Finset.card_range]

theorem ceilDiv_succ_pred {N k : ℕ} (hN : 1 ≤ N) (hk : 0 < k) :
    N ⌈/⌉ k = (N - 1) / k + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Nat.ceilDiv_eq_add_pred_div, show n + 1 + k - 1 = n + k from by omega,
      show n + 1 - 1 = n from by omega, Nat.add_div_right _ hk]

/-- **prp-2edgebound** — the `2+`-edges are exactly the block-boundary edges, `⌈ℓ/k⌉ − 1`. -/
theorem prp_2edgebound {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 2 = p.numVerts ⌈/⌉ k - 1 := by
  have hN : 1 ≤ p.numVerts := p.numVerts_pos
  have hpos := ceilDiv_succ_pred hN hk
  have hc : p.numVerts ⌈/⌉ k - 1 = (p.numVerts - 1) / k := by rw [hpos, Nat.add_sub_cancel]
  rw [hc, edgeCountGe]
  rw [show (Finset.range (p.numVerts - 1)).filter
          (fun i => 2 ≤ ew k (p.vert i) (p.vert (i + 1)))
        = (Finset.range (p.numVerts - 1)).filter (fun i => k ∣ (i + 1)) from ?_]
  · exact Nat.card_multiples (p.numVerts - 1) k
  · apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    have hi' : i + 1 < p.numVerts := by omega
    have hpe := prp_periodicedges hk hp hi'
    have hge := ew_ge_one hk (p.vert i) (p.vert (i + 1))
    constructor
    · intro h2
      by_contra hnd
      exact absurd (hpe.mpr hnd) (by omega)
    · intro hd
      have hne : ew k (p.vert i) (p.vert (i + 1)) ≠ 1 := fun he => (hpe.mp he) hd
      omega

/-- Exact `ceilDiv` when the divisor divides. -/
theorem ceilDiv_of_dvd {a b : ℕ} (hb : 0 < b) (h : b ∣ a) : a ⌈/⌉ b = a / b := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.ceilDiv_eq_add_pred_div, show b * c + b - 1 = b * c + (b - 1) from by omega,
      Nat.mul_add_div hb, Nat.div_eq_of_lt (by omega : b - 1 < b), Nat.add_zero,
      Nat.mul_div_cancel_left c hb]

/-- **j-at-pivot** — `j_k(k(k−1)(k−2)) = k²(k−2) − 3`. -/
theorem j_at_pivot {k : ℕ} (hk : 3 ≤ k) :
    j k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 := by
  rw [j_base (Or.inl (le_refl _))]
  have hk0 : 0 < k := by omega
  have hkk0 : 0 < k * (k - 1) := by
    have : 0 < k - 1 := by omega
    exact Nat.mul_pos hk0 this
  have hd1 : k ∣ k * (k - 1) * (k - 2) := ⟨(k - 1) * (k - 2), by rw [Nat.mul_assoc]⟩
  have hd2 : k * (k - 1) ∣ k * (k - 1) * (k - 2) := ⟨k - 2, rfl⟩
  rw [ceilDiv_of_dvd hk0 hd1, ceilDiv_of_dvd hkk0 hd2]
  have e1 : k * (k - 1) * (k - 2) / k = (k - 1) * (k - 2) := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hk0]
  have e2 : k * (k - 1) * (k - 2) / (k * (k - 1)) = k - 2 := by
    rw [Nat.mul_div_cancel_left _ hkk0]
  rw [e1, e2]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have s1 : m + 3 - 1 = m + 2 := by omega
  have s2 : m + 3 - 2 = m + 1 := by omega
  rw [s1, s2]
  have core : (m + 3) * (m + 2) * (m + 1) + (m + 2) * (m + 1) + (m + 1)
      = (m + 3) ^ 2 * (m + 1) := by ring
  omega

/-! ### Weight = sum of edge weights; the summation bound `w(p) ≥ Σ_q #{q+-edges}` -/

theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- `w(p) = Σ_{i} w(p[i] → p[i+1])` as a `Finset` sum over the `|p|−1` edges. -/
theorem wtP_eq_sum {k : ℕ} (p : HPath k) :
    p.wtP = ∑ i ∈ Finset.range (p.numVerts - 1), ew k (p.vert i) (p.vert (i + 1)) := by
  rw [HPath.wtP]
  rw [show p.verts.zipWith (ew k) p.verts.tail
        = (List.range (p.numVerts - 1)).map (fun i => ew k (p.vert i) (p.vert (i + 1))) from ?_]
  · exact list_range_map_sum _ _
  · apply List.ext_getElem
    · rw [List.length_zipWith, List.length_map, List.length_range, List.length_tail]
      have : p.numVerts = p.verts.length := rfl
      omega
    · intro i h1 h2
      have hlen : i < p.verts.tail.length := by
        rw [List.length_tail]
        rw [List.length_zipWith, List.length_tail] at h1
        omega
      have hi1 : i < p.numVerts := by
        rw [List.length_zipWith, List.length_tail] at h1
        have : p.numVerts = p.verts.length := rfl
        omega
      have hi2 : i + 1 < p.numVerts := by
        rw [List.length_tail] at hlen
        have : p.numVerts = p.verts.length := rfl
        omega
      rw [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_tail]
      exact (congrArg₂ (ew k) (vert_getElem p hi1) (vert_getElem p hi2)).symm

/-- **Summation bound** — the weight of an exitless path is at least the total count of
`1+`, `2+`, and `3+` edges. -/
theorem indicator_sum_le (e : ℕ) :
    (if 1 ≤ e then 1 else 0) + (if 2 ≤ e then 1 else 0) + (if 3 ≤ e then 1 else 0) ≤ e := by
  split_ifs <;> omega

theorem wtP_ge_edgeCounts {k : ℕ} (_hk : 1 ≤ k) {p : HPath k} :
    edgeCountGe p 1 + edgeCountGe p 2 + edgeCountGe p 3 ≤ p.wtP := by
  have key : ∀ q : ℕ, edgeCountGe p q = ∑ i ∈ Finset.range (p.numVerts - 1),
      (if q ≤ ew k (p.vert i) (p.vert (i + 1)) then 1 else 0) := by
    intro q; rw [edgeCountGe, Finset.card_filter]
  rw [key 1, key 2, key 3, wtP_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact indicator_sum_le _

/-- The greedy lower bound `w(p) ≥ j_k(|p|)` on the base interval — modulo the `3+`-edge
count (`prp_3edgebound`), supplied as `h3`. -/
theorem wtP_ge_j {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (hℓ0 : 0 < p.numVerts) (hℓ : p.numVerts ≤ k * (k - 1) * (k - 2))
    (h3 : p.numVerts ⌈/⌉ (k * (k - 1)) - 1 ≤ edgeCountGe p 3) :
    j k p.numVerts ≤ p.wtP := by
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ p.numVerts := hℓ0
  have h1 := prp_1edgebound hk1 hp
  have h2 := prp_2edgebound hk1 hp
  have hsum := wtP_ge_edgeCounts hk1 (p := p)
  have hck1 : 1 ≤ p.numVerts ⌈/⌉ k := by
    rw [ceilDiv_succ_pred hN1 (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ p.numVerts ⌈/⌉ (k * (k - 1)) := by
    rw [ceilDiv_succ_pred hN1 (Nat.mul_pos (by omega) (by omega : 0 < k - 1))]
    exact Nat.le_add_left 1 _
  rw [j_base (Or.inl hℓ)]
  set A := p.numVerts ⌈/⌉ k
  set B := p.numVerts ⌈/⌉ (k * (k - 1))
  omega

/-- **thm2 (base region)** — `j_k(ℓ) ≤ i_k(ℓ)` for `0 < ℓ ≤ k(k−1)(k−2)`, modulo the
`3+`-edge count `h3` (`prp_3edgebound`). -/
theorem thm2_base {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2))
    (hex : HasExitlessPath k ℓ)
    (h3 : ∀ q : HPath k, q.Exitless → q.numVerts ⌈/⌉ (k * (k - 1)) - 1 ≤ edgeCountGe q 3) :
    j k ℓ ≤ iExitless k ℓ := by
  obtain ⟨p, hpe, hpv⟩ := hex
  have hne : {m | ∃ q : HPath k, q.Exitless ∧ q.numVerts = ℓ ∧ q.wtP = m}.Nonempty :=
    ⟨p.wtP, p, hpe, hpv, rfl⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨q, hqe, hqv, hqw⟩ := hmem
  calc j k ℓ = j k q.numVerts := by rw [hqv]
    _ ≤ q.wtP := wtP_ge_j hk hqe (by rw [hqv]; exact hℓ0) (by rw [hqv]; exact hℓ) (h3 q hqe)
    _ = iExitless k ℓ := hqw

/-! ### `clm-phi` — the `φ(c⃗,v⃗)` characterization of strongly exitless paths -/

theorem verts_eq_map_vert {k : ℕ} (p : HPath k) :
    p.verts = (List.range p.numVerts).map (fun i => p.vert i) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, HPath.numVerts]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    have hi : i < p.numVerts := by rw [List.length_map, List.length_range] at h2; exact h2
    exact (vert_getElem p hi).symm

theorem range_reshape {α : Type*} (f : ℕ → α) (k t : ℕ) :
    (List.range (k * t)).map f
      = ((List.range t).map (fun s => (List.range k).map (fun r => f (k * s + r)))).flatten := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, List.range_add, List.map_append, ih, List.range_succ, List.map_append,
        List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.map_map]
    rfl

/-- **clm-phi (necessity)**, amended with `1 ≤ k` (false at `k = 0`, see PROGRESS). -/
theorem clm_phi_necessity_amended {k : ℕ} (hk : 1 ≤ k) {p : HPath k}
    (hp : p.StronglyExitless) : IsPhiForm p := by
  have hdvd := dvd_numVerts_of_stronglyExitless hk hp
  obtain ⟨hpe, _⟩ := hp
  obtain ⟨t, ht⟩ := hdvd
  have hcase : ∀ a b : ℕ, a < b → b < t →
      rotClass (p.vert (k * a)).1 ≠ rotClass (p.vert (k * b)).1 := by
    intro a b hab hbt
    have hBk : k * a + k ≤ k * b := by
      have h1 : k * a + k = k * (a + 1) := by ring
      rw [h1]; exact Nat.mul_le_mul (le_refl k) hab
    have hB'n : k * b < p.numVerts := by rw [ht]; exact Nat.mul_lt_mul_of_pos_left hbt hk
    exact no_reentry hk hpe ⟨a, rfl⟩ hBk hB'n
  refine ⟨(List.range t).map (fun s => p.vert (k * s)), ?_, ?_⟩
  · rw [List.map_map]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    simp only [List.mem_range] at ha hb
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd hab (hcase a b h hb)
    · exact h
    · exact absurd hab.symm (hcase b a h ha)
  · rw [verts_eq_map_vert p, ht, range_reshape, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [List.mem_range] at hs
    apply List.map_congr_left
    intro r hr
    simp only [List.mem_range] at hr
    have hb : k * s + r < p.numVerts := by
      rw [ht]
      calc k * s + r < k * s + k := by omega
        _ = k * (s + 1) := by ring
        _ ≤ k * t := Nat.mul_le_mul (le_refl k) hs
    exact block_is_full_cycle hk hpe ⟨s, rfl⟩ hr hb

end Proved
end Hunter

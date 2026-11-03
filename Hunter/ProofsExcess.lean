/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsRecursion

/-!
# Theorem 2 — the level-≥3 excess frontier (mixed-layer recursion region)

This file attacks the single remaining sub-goal of Hunter's Theorem 2: the frontier
inequality `ExcessFrontier k` (`ProofsRecursion`) on the recursion region
`ℓ > k(k−1)(k−2)`, whose validity closes `Hunter.Proved.thm2` via
`ProofsRecursion.thm2_of_frontier`.

The demand is `excess(q) ≥ D(ℓ)` with `D(ℓ) = j_k(ℓ) − (ℓ−1) − (⌈ℓ/k⌉−1)`, where
`excess(q) = Σ_{boundaries}(w−2)`.  The level-2 confinement (`prp_3edgebound`) already
delivers, *unconditionally in the length*, `excess(q) ≥ ⌈ℓ/(k(k−1))⌉−1 =: D_base(ℓ)`.  Hence
the frontier is free wherever `D(ℓ) ≤ D_base(ℓ)` (deficit 0), which — computed exhaustively
— covers the whole base region *and* the large majority of the recursion region (45 of the
60 recursion lengths at k=5; all but a width-`k` band after each multiple of `k(k−1)`).

This file proves, sorry-free and axiom-clean:

* `excess_ge_Dbase` — the unconditional `excess(q) ≥ ⌈ℓ/(k(k−1))⌉−1`.
* `thm2_of_j_le_jbase` — **thm2 (`j_k(ℓ) ≤ i_k(ℓ)`) for every `ℓ` with `j_k(ℓ) ≤ jbase(ℓ)`**,
  a genuine extension of `thm2_base_unconditional` into the recursion region.
* the level-3 structural core `Vset3` (the σ-closed `k(k−1)(k−2)`-vertex marked-3-loop) with
  `card_Vset3_le`, the reusable object for a future full level-3 confinement.
* `prefix_exitless` — every prefix of an exitless path is exitless.

The residual open piece (the deficit>0 band) is logged precisely in `PROGRESS-excess.md`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsExcess

open ProofsExitless ProofsConfinement ProofsRecursion Proved
open HPath

variable {k : ℕ}

/-! ## The unconditional level-2 excess bound and the `j ≤ jbase` frontier extension -/

/-- **Unconditional excess bound.**  For *every* exitless path (all lengths, no base-region
restriction) the `≥3`-weight excess is at least `⌈ℓ/(k(k−1))⌉−1`.  This is `prp_3edgebound`
(level-2 confinement) composed with `excess ≥ edgeCountGe · 3`. -/
theorem excess_ge_Dbase {k : ℕ} (hk : 3 ≤ k) {q : HPath k} (hq : q.Exitless) :
    q.numVerts ⌈/⌉ (k * (k - 1)) - 1 ≤ excess q :=
  le_trans (Proved.prp_3edgebound (by omega) hq) (edgeCountGe3_le_excess hk q)

/-- **Frontier at `q` when `j ≤ jbase`.**  The `ExcessFrontier` inequality holds at any
exitless `q` whose length satisfies `j_k(ℓ) ≤ jbase(ℓ) = ℓ+⌈ℓ/k⌉+⌈ℓ/(k(k−1))⌉−3` — in
particular on the whole base region and on every deficit-0 length of the recursion region. -/
theorem excess_frontier_of_j_le_jbase {k : ℕ} (hk : 3 ≤ k) {q : HPath k} (hq : q.Exitless)
    (h0 : 0 < q.numVerts)
    (hj : j k q.numVerts ≤
        q.numVerts + (q.numVerts ⌈/⌉ k) + (q.numVerts ⌈/⌉ (k * (k - 1))) - 3) :
    j k q.numVerts ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q := by
  have hN1 : 1 ≤ q.numVerts := h0
  have he := excess_ge_Dbase hk hq
  have hck1 : 1 ≤ q.numVerts ⌈/⌉ k := by
    rw [ceilDiv_succ_pred hN1 (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ q.numVerts ⌈/⌉ (k * (k - 1)) := by
    rw [ceilDiv_succ_pred hN1 (Nat.mul_pos (by omega) (by omega : 0 < k - 1))]
    exact Nat.le_add_left 1 _
  set A := q.numVerts ⌈/⌉ k
  set B := q.numVerts ⌈/⌉ (k * (k - 1))
  omega

/-- **thm2 for `j ≤ jbase` lengths (extension into the recursion region).**  For every `ℓ`
with an exitless witness and `j_k(ℓ) ≤ jbase(ℓ)`, Hunter's Theorem 2 holds:
`j_k(ℓ) ≤ i_k(ℓ)`.  Since `j_k = jbase` on the base region this subsumes
`thm2_base_unconditional`, and it additionally settles every deficit-0 length above
`k(k−1)(k−2)` (the 45/60 majority of the k=5 recursion region). -/
theorem thm2_of_j_le_jbase {k ℓ : ℕ} (hk : 3 ≤ k)
    (hj : j k ℓ ≤ ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3)
    (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ := by
  obtain ⟨p, hpe, hpv⟩ := hex
  have hne : {m | ∃ q : HPath k, q.Exitless ∧ q.numVerts = ℓ ∧ q.wtP = m}.Nonempty :=
    ⟨p.wtP, p, hpe, hpv, rfl⟩
  obtain ⟨q, hqe, hqv, hqw⟩ := Nat.sInf_mem hne
  have h0 : 0 < q.numVerts := q.numVerts_pos
  calc j k ℓ
      = j k q.numVerts := by rw [hqv]
    _ ≤ q.numVerts + (q.numVerts ⌈/⌉ k) + (q.numVerts ⌈/⌉ (k * (k - 1))) - 3 := by
        rw [hqv]; exact hj
    _ ≤ q.wtP := wtP_ge_jbase hk hqe h0
    _ = iExitless k ℓ := hqw

/-! ## Prefixes of exitless paths are exitless -/

/-- Dropping tail vertices preserves `Exitless`: for every `d < |p|` there is an exitless
path whose vertex list is the length-`(|p|−d)` prefix of `p`.  Proved by iterating the
one-step `clm_prefix`. -/
theorem prefix_exitless_aux {k : ℕ} {p : HPath k} (hp : p.Exitless) :
    ∀ d, d < p.numVerts →
      ∃ q : HPath k, q.verts = p.verts.take (p.numVerts - d) ∧ q.Exitless := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨p, ?_, hp⟩
    rw [Nat.sub_zero]
    exact List.take_length.symm
  | succ d ih =>
    intro hd
    obtain ⟨q, hqv, hqe⟩ := ih (by omega)
    have hqnv : q.numVerts = p.numVerts - d := by
      show q.verts.length = _; rw [hqv, List.length_take]
      have : p.numVerts - d ≤ p.verts.length := by
        show p.numVerts - d ≤ p.numVerts; omega
      omega
    have hq2 : 2 ≤ q.numVerts := by rw [hqnv]; omega
    obtain ⟨r, hrv, hre⟩ := Proved.clm_prefix hqe hq2
    refine ⟨r, ?_, hre⟩
    have e1 : r.verts = q.verts.take (q.numVerts - 1) := by
      rw [hrv]; exact List.dropLast_eq_take
    rw [e1, hqnv, hqv, List.take_take]
    congr 1
    omega

/-- **Prefix exitless.**  For `1 ≤ n ≤ |p|`, the length-`n` prefix of an exitless path is
(the vertex list of) an exitless path. -/
theorem prefix_exitless {k : ℕ} {p : HPath k} (hp : p.Exitless) {n : ℕ} (hn : 1 ≤ n)
    (hnle : n ≤ p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.take n ∧ q.Exitless := by
  obtain ⟨q, hqv, hqe⟩ := prefix_exitless_aux hp (p.numVerts - n) (by omega)
  exact ⟨q, by rw [hqv, show p.numVerts - (p.numVerts - n) = n from by omega], hqe⟩

/-! ## The level-3 marked-loop `Vset3` (σ-closed, `k(k−1)(k−2)` vertices)

The natural level-3 analog of `ProofsConfinement.Vset`: fix two markers `α₁, α₂` and require
the doubly-erased word to lie in a fixed rotation class `K`.  It is σ-closed (both erasures
survive rotation up to a further rotation) and has at most `k(k−1)(k−2)` vertices — the
`(k−1)(k−2)` one-cycles of a marked 3-loop.  This is the reusable structural core for a full
level-3 confinement (whose move algebra lives in the contracted graph `S'_k`; see
`PROGRESS-excess.md`). -/

/-- The marked-3-loop vertex set: permutation words `v` with
`rotClass ((v.erase α₁).erase α₂) = K`. -/
noncomputable def Vset3 (k : ℕ) (α₁ α₂ : ℕ) (K : RotClass) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => rotClass (((v : List ℕ).erase α₁).erase α₂) = K)

theorem mem_Vset3 {α₁ α₂ : ℕ} {K : RotClass} {v : Vtx k} :
    v ∈ Vset3 k α₁ α₂ K ↔ rotClass (((v : List ℕ).erase α₁).erase α₂) = K := by
  rw [Vset3, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `Vset3` is closed under `σ`: rotating `v` rotates `v.erase α₁` (up to a further
rotation), which fixes the class of `(v.erase α₁).erase α₂`. -/
theorem sigma_mem_Vset3 {α₁ α₂ : ℕ} {K : RotClass} {v : Vtx k}
    (h : v ∈ Vset3 k α₁ α₂ K) : sigma v ∈ Vset3 k α₁ α₂ K := by
  rw [mem_Vset3] at h ⊢
  show rotClass ((((v : List ℕ).rotate 1).erase α₁).erase α₂) = K
  have hr : (v : List ℕ).erase α₁ ~r ((v : List ℕ).rotate 1).erase α₁ :=
    (rotClass_eq_iff.mp (rotClass_erase_rotate_one v.2.nodup)).symm
  obtain ⟨s, hs⟩ := hr
  rw [← hs, rotClass_erase_rotate (v.2.nodup.erase α₁) s]
  exact h

/-- `Vset3` is closed under all `σ`-iterates. -/
theorem sigma_iter_mem_Vset3 {α₁ α₂ : ℕ} {K : RotClass} {v : Vtx k}
    (h : v ∈ Vset3 k α₁ α₂ K) (r : ℕ) : sigma^[r] v ∈ Vset3 k α₁ α₂ K := by
  induction r with
  | zero => simpa using h
  | succ r ih => rw [Function.iterate_succ_apply']; exact sigma_mem_Vset3 ih

/-- A whole 1-cycle lies in `Vset3` once its base point does. -/
theorem cyc_subset_Vset3 {α₁ α₂ : ℕ} {K : RotClass} {v : Vtx k} (hk1 : 1 ≤ k)
    (h : v ∈ Vset3 k α₁ α₂ K) : cyc v ⊆ Vset3 k α₁ α₂ K := by
  intro u hu
  obtain ⟨r, _, rfl⟩ := (mem_cyc_iff_exists hk1).mp hu
  exact sigma_iter_mem_Vset3 h r

/-- **Cardinality of the marked-3-loop.**  With the two markers taken as the last two symbols
of a base word `A` and `K` the rotation class of the remaining `k−2` symbols, the marked
3-loop `Vset3` has at most `k(k−1)(k−2)` vertices.  Level-3 analog of `card_Vset_le`, via a
double insertion surjection `(r, j₂, j₁) ↦ insert α₁ (insert α₂ (u₀₀.rotate r))`. -/
theorem card_Vset3_le {A : Vtx k} (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass}
    (hα1 : α₁ = (A : List ℕ).getLastD 0)
    (hα2 : α₂ = ((A : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((A : List ℕ).dropLast.dropLast)) :
    (Vset3 k α₁ α₂ K).card ≤ k * (k - 1) * (k - 2) := by
  classical
  -- destruct A = (u₀₀ ++ [α₂]) ++ [α₁]
  rcases List.eq_nil_or_concat (A : List ℕ) with hnil | ⟨A', a, hAeq⟩
  · exact absurd hnil (A.2.ne_nil (by omega))
  rw [List.concat_eq_append] at hAeq
  rcases List.eq_nil_or_concat A' with hnil' | ⟨u₀₀, b, hA'eq⟩
  · exfalso; have hl := A.2.length; rw [hAeq, hnil'] at hl; simp at hl; omega
  rw [List.concat_eq_append] at hA'eq
  have hAeq3 : (A : List ℕ) = (u₀₀ ++ [b]) ++ [a] := by rw [hAeq, hA'eq]
  have hnd3 : ((u₀₀ ++ [b]) ++ [a]).Nodup := by rw [← hAeq3]; exact A.2.nodup
  have hAlen : ((u₀₀ ++ [b]) ++ [a]).length = k := by rw [← hAeq3]; exact A.2.length
  have hu0len : u₀₀.length = k - 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hAlen; omega
  have hlenpos : 0 < u₀₀.length := by rw [hu0len]; omega
  -- markers and class from the concat structure
  have hαa : α₁ = a := by rw [hα1, hAeq3, List.getLastD_concat]
  have hAdl : (A : List ℕ).dropLast = u₀₀ ++ [b] := by rw [hAeq3, List.dropLast_concat]
  have hαb : α₂ = b := by rw [hα2, hAdl, List.getLastD_concat]
  have hKu : K = rotClass u₀₀ := by rw [hK, hAeq3, List.dropLast_concat, List.dropLast_concat]
  -- symbols of A are [k]; a, b ∈ Icc 1 k, and a ≠ b
  have haIcc : a ∈ Finset.Icc 1 k := by
    rw [← A.2.toFinset_eq, List.mem_toFinset, hAeq3]; simp
  have hbIcc : b ∈ Finset.Icc 1 k := by
    rw [← A.2.toFinset_eq, List.mem_toFinset, hAeq3]; simp
  have haU : a ∉ u₀₀ ++ [b] :=
    fun h => (List.nodup_append.mp hnd3).2.2 a h a (List.mem_cons_self ..) rfl
  have hab : a ≠ b := fun h => haU (by rw [h]; simp)
  -- the double-insertion map
  set f : ℕ × ℕ × ℕ → List ℕ := fun p =>
    ((u₀₀.rotate p.1).take p.2.1 ++ α₂ :: (u₀₀.rotate p.1).drop p.2.1).take p.2.2 ++
      α₁ :: ((u₀₀.rotate p.1).take p.2.1 ++ α₂ :: (u₀₀.rotate p.1).drop p.2.1).drop p.2.2
    with hf
  have hsub : (Vset3 k α₁ α₂ K).image Subtype.val ⊆
      (Finset.range (k - 2) ×ˢ (Finset.range (k - 1) ×ˢ Finset.range k)).image f := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨v, hvV, rfl⟩ := hw
    rw [mem_Vset3] at hvV
    -- a ∈ v, split
    have hav : a ∈ (v : List ℕ) := by rw [← List.mem_toFinset, v.2.toFinset_eq]; exact haIcc
    have hbv : b ∈ (v : List ℕ) := by rw [← List.mem_toFinset, v.2.toFinset_eq]; exact hbIcc
    obtain ⟨t₁, r₁, hv1⟩ := List.append_of_mem hav
    have hvnd1 : (t₁ ++ a :: r₁).Nodup := by rw [← hv1]; exact v.2.nodup
    have hat1 : a ∉ t₁ :=
      fun h => (List.nodup_append.mp hvnd1).2.2 a h a (List.mem_cons_self ..) rfl
    have herasea : (v : List ℕ).erase a = t₁ ++ r₁ := by
      rw [hv1, List.erase_append_right _ hat1, List.erase_cons_head]
    -- b ∈ v.erase a, split
    have hbva : b ∈ (v : List ℕ).erase a := (List.mem_erase_of_ne hab.symm).mpr hbv
    obtain ⟨t₂, r₂, hva⟩ := List.append_of_mem hbva
    have hvbnd : (t₂ ++ b :: r₂).Nodup := by rw [← hva]; exact v.2.nodup.erase a
    have hbt2 : b ∉ t₂ :=
      fun h => (List.nodup_append.mp hvbnd).2.2 b h b (List.mem_cons_self ..) rfl
    have hbase : ((v : List ℕ).erase a).erase b = t₂ ++ r₂ := by
      rw [hva, List.erase_append_right _ hbt2, List.erase_cons_head]
    -- rotation-class equation ⇒ the base word is a rotation of u₀₀
    rw [hαa, hαb, hKu, hbase] at hvV
    obtain ⟨m, hm⟩ := rotClass_eq_iff.mp hvV.symm
    have hrot : u₀₀.rotate (m % u₀₀.length) = t₂ ++ r₂ := by rw [List.rotate_mod]; exact hm
    -- lengths for the index ranges
    have hvlen : (v : List ℕ).length = k := v.2.length
    have ht1lt : t₁.length < k := by
      have h := congrArg List.length hv1; rw [hvlen] at h
      simp only [List.length_append, List.length_cons] at h; omega
    have ht2lt : t₂.length < k - 1 := by
      have hel : ((v : List ℕ).erase a).length = k - 1 := by
        rw [List.length_erase_of_mem hav, hvlen]
      have h := congrArg List.length hva; rw [hel] at h
      simp only [List.length_append, List.length_cons] at h; omega
    refine Finset.mem_image.mpr ⟨(m % u₀₀.length, t₂.length, t₁.length), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_range.mpr (by rw [← hu0len]; exact Nat.mod_lt _ hlenpos)
      · exact Finset.mem_range.mpr ht2lt
      · exact Finset.mem_range.mpr ht1lt
    · show ((u₀₀.rotate (m % u₀₀.length)).take t₂.length ++ α₂ ::
          (u₀₀.rotate (m % u₀₀.length)).drop t₂.length).take t₁.length ++ α₁ ::
          ((u₀₀.rotate (m % u₀₀.length)).take t₂.length ++ α₂ ::
          (u₀₀.rotate (m % u₀₀.length)).drop t₂.length).drop t₁.length = (v : List ℕ)
      have hinner : (u₀₀.rotate (m % u₀₀.length)).take t₂.length ++ α₂ ::
          (u₀₀.rotate (m % u₀₀.length)).drop t₂.length = (v : List ℕ).erase a := by
        rw [hrot, List.take_left, List.drop_left, hαb, ← hva]
      rw [hinner, herasea, List.take_left, List.drop_left, hαa, ← hv1]
  have hinjval : Function.Injective (Subtype.val : Vtx k → List ℕ) := fun a b h => Subtype.ext h
  calc (Vset3 k α₁ α₂ K).card
      = ((Vset3 k α₁ α₂ K).image Subtype.val).card :=
        (Finset.card_image_of_injective _ hinjval).symm
    _ ≤ ((Finset.range (k - 2) ×ˢ (Finset.range (k - 1) ×ˢ Finset.range k)).image f).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (k - 2) ×ˢ (Finset.range (k - 1) ×ˢ Finset.range k)).card :=
        Finset.card_image_le
    _ = (k - 2) * ((k - 1) * k) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
          Finset.card_range]
    _ = k * (k - 1) * (k - 2) := by ring

/-! ## A clean interval extension of thm2: `ℓ ≤ k²(k−2)`

On the first recursion interval `k(k−1)(k−2) < ℓ ≤ k²(k−2)` the recursion unfolds once into
the base region, and a short ceiling computation gives `j_k(ℓ) = ℓ+⌈ℓ/k⌉+(k−4) ≤ jbase(ℓ)`
(the last step because `⌈ℓ/(k(k−1))⌉ ≥ k−1` once `ℓ > k(k−1)(k−2)`).  Feeding this through
`thm2_of_j_le_jbase` extends Theorem 2 from `ℓ ≤ k(k−1)(k−2)` to `ℓ ≤ k²(k−2)`. -/

/-- `(a + b) ⌈/⌉ k = a ⌈/⌉ k + b / k` when `k ∣ b`. -/
theorem ceilDiv_add_dvd {a b k : ℕ} (hk : 0 < k) (hb : k ∣ b) :
    (a + b) ⌈/⌉ k = a ⌈/⌉ k + b / k := by
  obtain ⟨t, rfl⟩ := hb
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div, Nat.mul_div_cancel_left t hk,
      show a + k * t + k - 1 = (a + k - 1) + k * t from by omega,
      Nat.add_mul_div_left _ _ hk]

/-- `⌈ℓ₀ / (k(k−1))⌉ = k − 2` for the pivot `ℓ₀ = k(k−1)(k−2) − k`. -/
theorem ceilDiv_ell0 {k : ℕ} (hk : 3 ≤ k) : ell0 k ⌈/⌉ (k * (k - 1)) = k - 2 := by
  have hN1 : 1 ≤ ell0 k := ProofsRecursion.ell0_pos hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have hDpos : 0 < (m + 3) * (m + 3 - 1) := by rw [e1]; positivity
  rw [Proved.ceilDiv_succ_pred hN1 hDpos]
  have hval : ell0 (m + 3) - 1 = (m + 3) * (m + 3 - 1) * m + (m ^ 2 + 4 * m + 2) := by
    rw [ell0, e1, e2]
    have expand : (m + 3) * (m + 2) * (m + 1) = (m + 3) * (m + 2) * m + (m + 3) * (m + 2) := by
      ring
    have expand2 : (m + 3) * (m + 2) = m ^ 2 + 5 * m + 6 := by ring
    omega
  have hlt : m ^ 2 + 4 * m + 2 < (m + 3) * (m + 3 - 1) := by rw [e1]; nlinarith
  rw [hval, Nat.mul_add_div hDpos, Nat.div_eq_of_lt hlt]
  omega

/-- `k ∣ ℓ₀`. -/
theorem k_dvd_ell0 {k : ℕ} (hk : 3 ≤ k) : k ∣ ell0 k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [ell0, show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
  obtain ⟨P, hP⟩ : ∃ P, (m + 2) * (m + 1) = P + 1 := by
    have hpos : 0 < (m + 2) * (m + 1) := by positivity
    exact ⟨(m + 2) * (m + 1) - 1, by omega⟩
  refine ⟨P, ?_⟩
  have hexp : (m + 3) * (m + 2) * (m + 1) = (m + 3) * P + (m + 3) := by
    rw [show (m + 3) * (m + 2) * (m + 1) = (m + 3) * ((m + 2) * (m + 1)) from by ring, hP]; ring
  omega

/-- **`j ≤ jbase` on the first recursion interval.**  For `k(k−1)(k−2) < ℓ ≤ k²(k−2)`,
`j_k(ℓ) ≤ ℓ + ⌈ℓ/k⌉ + ⌈ℓ/(k(k−1))⌉ − 3`. -/
theorem j_le_jbase_recursion {k ℓ : ℕ} (hk : 3 ≤ k)
    (hlo : k * (k - 1) * (k - 2) < ℓ) (hhi : ℓ ≤ k ^ 2 * (k - 2)) :
    j k ℓ ≤ ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3 := by
  have hk0 : 0 < k := by omega
  have hkk1pos : 0 < k * (k - 1) := Nat.mul_pos hk0 (by omega)
  have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
  -- nonlinear identities (via k = m+3)
  have hrel1 : k ^ 2 * (k - 2) = k * (k - 1) * (k - 2) + k * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]; ring
  have hrel2 : k * (k - 2) + k = k * (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]; ring
  have hrel3 : k * (k - 1) ≤ k * (k - 1) * (k - 2) := by
    have : 1 ≤ k - 2 := by omega
    calc k * (k - 1) = k * (k - 1) * 1 := by rw [Nat.mul_one]
      _ ≤ k * (k - 1) * (k - 2) := Nat.mul_le_mul_left _ this
  have hell0B : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  -- bounds on the split length s = ℓ − ℓ₀
  have hell0lt : ell0 k < ℓ := by omega
  have hsle : ℓ - ell0 k ≤ k * (k - 1) := by omega
  have hsle_base : ℓ - ell0 k ≤ k * (k - 1) * (k - 2) := le_trans hsle hrel3
  have hs1 : 1 ≤ ℓ - ell0 k := by omega
  have hℓsum : ℓ = (ℓ - ell0 k) + ell0 k := by omega
  -- the ceiling facts
  have hcadd : ℓ ⌈/⌉ k = (ℓ - ell0 k) ⌈/⌉ k + ell0 k / k := by
    conv_lhs => rw [hℓsum]
    exact ceilDiv_add_dvd hk0 hdvd
  have hce : ell0 k ⌈/⌉ k = ell0 k / k := Proved.ceilDiv_of_dvd hk0 hdvd
  have hcs1 : (ℓ - ell0 k) ⌈/⌉ (k * (k - 1)) = 1 := by
    rw [Proved.ceilDiv_succ_pred hs1 hkk1pos, Nat.div_eq_of_lt (by omega)]
  have hce0 : ell0 k ⌈/⌉ (k * (k - 1)) = k - 2 := ceilDiv_ell0 hk
  have hcll : k - 1 ≤ ℓ ⌈/⌉ (k * (k - 1)) := by
    by_contra hc
    have hle : ℓ ⌈/⌉ (k * (k - 1)) ≤ k - 2 := by omega
    rw [ceilDiv_le_iff_le_mul hkk1pos] at hle
    omega
  -- lower bounds preventing spurious ℕ-subtraction truncation
  have hk2k : k * 2 ≤ k * (k - 1) := Nat.mul_le_mul (le_refl k) (by omega)
  have hkle : k ≤ ell0 k := by rw [hell0B]; omega
  have hCs1 : 1 ≤ (ℓ - ell0 k) ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred hs1 hk0]; exact Nat.le_add_left 1 _
  -- the j values
  have hjs : j k (ℓ - ell0 k) =
      (ℓ - ell0 k) + ((ℓ - ell0 k) ⌈/⌉ k) + ((ℓ - ell0 k) ⌈/⌉ (k * (k - 1))) - 3 :=
    j_base (Or.inl hsle_base)
  have hje0 : j k (ell0 k) =
      ell0 k + (ell0 k ⌈/⌉ k) + (ell0 k ⌈/⌉ (k * (k - 1))) - 3 := by
    apply j_base; left
    have := ProofsRecursion.ell0_pos hk; rw [hell0B] at this ⊢; omega
  have hjrec : j k ℓ = j k (ℓ - ell0 k) + j k (ell0 k) + 3 := j_rec_unfold_one hk hlo
  -- combine (all ceilings and j-values are atoms with linear relations)
  rw [hcs1] at hjs
  rw [hce, hce0] at hje0
  omega

/-- **thm2 up to `ℓ ≤ k²(k−2)`.**  Hunter's Theorem 2 (`j_k(ℓ) ≤ i_k(ℓ)`) holds for every
`0 < ℓ ≤ k²(k−2)` — the base region `k(k−1)(k−2)` extended by the whole first recursion
interval.  A genuine extension of `thm2_base_unconditional` (and, with `thm2_small`, of the
`k ≤ 4` closure). -/
theorem thm2_upto {k ℓ : ℕ} (hk : 3 ≤ k) (hhi : ℓ ≤ k ^ 2 * (k - 2))
    (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ := by
  apply thm2_of_j_le_jbase hk _ hex
  by_cases hb : ℓ ≤ k * (k - 1) * (k - 2)
  · rw [j_base (Or.inl hb)]
  · exact j_le_jbase_recursion hk (by omega) hhi

end ProofsExcess

end Hunter

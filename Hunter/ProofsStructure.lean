/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsSpine
import Hunter.ProofsExitless

/-!
# Proofs — §5 structural layer of Hunter, *A New Lower Bound for Superpermutations*

Proofs of the §4 weight bookkeeping (`clm_eqq`), the §5 "rules ladder" describing the
structure of `X = F(P)` (`clm_rule1`,…,`cor_pathfirst`), the core weight bound
`prp_wPgivenX`, and the `𝒳_k` characterization (`prp_Xk_se_*`).

Helper lemmas live in namespace `Hunter.ProofsStructure`; targets are proved as
`Hunter.Proved.<name>` with the statement type copied verbatim from `Hunter/Statements.lean`
(or `<name>_amended` where the verbatim statement is false as stated — see
`PROGRESS-structure.md`).

Reuses `Hunter.ProofsSpine` (surgery/degree lemmas) and `Hunter.ProofsExitless`
(rotation/normal-form lemmas).
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsStructure

variable {k : ℕ}

/-! ## Basic unfolding and `σ`/`σ⁻¹` facts -/

theorem F_eq (P : HPath k) : F P = fPS P (Sset P) := rfl

/-- `getElem` at definitionally-equal indices agrees (avoids index-rewrite motive issues). -/
theorem getElem_eq_of_index_eq {α : Type*} {l : List α} {a b : ℕ}
    (hab : a = b) (ha : a < l.length) (hb : b < l.length) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- `σ ∘ σ⁻¹ = id` on vertices (rotate by `k−1` then by `1` is rotate by `k = length`). -/
theorem sigma_sigmaInv (v : Vtx k) : sigma (sigmaInv v) = v := by
  apply Subtype.ext
  show ((v : List ℕ).rotate (k - 1)).rotate 1 = (v : List ℕ)
  rw [List.rotate_rotate]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hv : (v : List ℕ) = [] := List.length_eq_zero_iff.mp v.2.length
    rw [hv]; simp
  · have hlen : (v : List ℕ).length = k := v.2.length
    have hkk : k - 1 + 1 = k := by omega
    rw [hkk]
    have hr := List.rotate_length (v : List ℕ)
    rwa [hlen] at hr

/-- `σ` preserves rotation class. -/
theorem rotClass_sigma (v : Vtx k) : rotClass (sigma v).1 = rotClass v.1 := by
  have h := ProofsExitless.rotClass_sigma_iter 1 v
  simpa using h

/-- A `P`-edge advances position by exactly one: `(a→b) ∈ E(P) ⟹ P⁻¹[b] = P⁻¹[a]+1`. -/
theorem edge_pos_succ {P : HPath k} {a b : Vtx k} (h : (a, b) ∈ P.edges) :
    P.pos b = P.pos a + 1 := by
  rw [HPath.edges, List.mem_toFinset] at h
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp h
  have hlen_i : i < P.verts.length := List.lt_length_left_of_zip hi
  have hlen_i1 : i + 1 < P.verts.length := by
    have h' := List.lt_length_right_of_zip hi; rw [List.length_tail] at h'; omega
  have ea : P.verts[i]'hlen_i = a := by
    have h' : ((P.verts.zip P.verts.tail)[i]'hi).1 = a := by rw [hia]
    simpa using h'
  have eb : P.verts[i + 1]'hlen_i1 = b := by
    have h' : ((P.verts.zip P.verts.tail)[i]'hi).2 = b := by rw [hia]
    simpa using h'
  have hidxa : P.verts.idxOf a = i := by rw [← ea]; exact P.nodup.idxOf_getElem i hlen_i
  have hidxb : P.verts.idxOf b = i + 1 := by rw [← eb]; exact P.nodup.idxOf_getElem (i + 1) hlen_i1
  show P.verts.idxOf b = P.verts.idxOf a + 1
  rw [hidxa, hidxb]

/-- Consecutive vertices of a path form a path-edge. -/
theorem consec_mem_edges {p : HPath k} {i : ℕ} (hi : i + 1 < p.verts.length) :
    (p.verts[i]'(by omega), p.verts[i + 1]'hi) ∈ p.edges := by
  rw [HPath.edges, List.mem_toFinset]
  have hzip : i < (p.verts.zip p.verts.tail).length := by
    rw [List.length_zip, List.length_tail]; omega
  refine List.mem_iff_getElem.mpr ⟨i, hzip, ?_⟩
  rw [List.getElem_zip, List.getElem_tail]

/-- Consecutive vertices of a path form a path-edge (vertex form). -/
theorem vert_consec_mem_edges {p : HPath k} {i : ℕ} (hi : i + 1 < p.numVerts) :
    (p.vert i, p.vert (i + 1)) ∈ p.edges := by
  have hb : i + 1 < p.verts.length := hi
  have hi0 : i < p.numVerts := by omega
  rw [ProofsExitless.vert_getElem p hi0, ProofsExitless.vert_getElem p hi]
  exact consec_mem_edges (p := p) (i := i) hb

/-- The start vertex has position `0`. -/
theorem pos_first (p : HPath k) : p.pos p.first = 0 := by
  rw [← p.vert_zero]; exact ProofsExitless.pos_vert p p.numVerts_pos

/-! ## `Vtx k` for `k ≤ 1` is a subsingleton -/

theorem vtx_subsingleton (hk : k ≤ 1) : Subsingleton (Vtx k) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have hla : (a : List ℕ).length = k := a.2.length
  have hlb : (b : List ℕ).length = k := b.2.length
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
  · rw [List.length_eq_zero_iff.mp hla, List.length_eq_zero_iff.mp hlb]
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hla
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlb
    have hax : x ∈ Finset.Icc 1 1 := by rw [← a.2.2, hx]; simp
    have hby : y ∈ Finset.Icc 1 1 := by rw [← b.2.2, hy]; simp
    rw [Finset.mem_Icc] at hax hby
    rw [hx, hy]; congr 1; omega

/-- For `k ≤ 1` every vertex lies in `C₋₁` (its 1-cycle is a fixed point). -/
theorem mem_Cm1_of_le_one (hk : k ≤ 1) (P : HPath k) (v : Vtx k) : v ∈ Cm1 P := by
  have hsub := vtx_subsingleton hk
  rw [Cm1, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [C0, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro u _
  rw [Subsingleton.elim u (sigma v)]

/-- Contrapositive: `v ∉ C₋₁ ⟹ k ≥ 2`. -/
theorem two_le_of_not_Cm1 {P : HPath k} {v : Vtx k} (hv : v ∉ Cm1 P) : 2 ≤ k := by
  by_contra hc
  exact hv (mem_Cm1_of_le_one (by omega) P v)

/-! ## The core membership fact: `(v → σv) ∈ F(P)` for `v ∉ C₋₁` -/

/-- If `u` is a `double` then some added 1-edge points at `u`. -/
theorem double_imp_added_inedge {P : HPath k} {S : Finset (Vtx k)} {u : Vtx k}
    (hu : u ∈ doubles P S) : (intoV (addedEdges S) u).Nonempty := by
  simp only [doubles, Finset.mem_filter] at hu
  obtain ⟨-, hu2⟩ := hu
  have hdecomp : intoV (Xstep1 P S) u =
      intoV (P.edges \ E1removed P S) u ∪ intoV (addedEdges S) u := by
    unfold Xstep1; exact ProofsSpine.intoV_union _ _ u
  have hAle : (intoV (P.edges \ E1removed P S) u).card ≤ 1 :=
    le_trans (Finset.card_le_card (ProofsSpine.intoV_mono Finset.sdiff_subset u))
      (ProofsSpine.path_into_le_one P u)
  rw [Finset.nonempty_iff_ne_empty]
  intro hB
  rw [hdecomp, hB, Finset.union_empty] at hu2
  omega

/-- If `σv` is a `double`, then `v ∈ S`. -/
theorem mem_S_of_sigma_double {P : HPath k} {S : Finset (Vtx k)} {v : Vtx k}
    (hd : sigma v ∈ doubles P S) : v ∈ S := by
  obtain ⟨e, he⟩ := double_imp_added_inedge hd
  simp only [intoV, mem_into, addedEdges, Finset.mem_image, Finset.mem_singleton] at he
  obtain ⟨⟨w, hwS, hwe⟩, he2⟩ := he
  rw [← hwe] at he2
  have hww : sigma w = sigma v := he2
  rw [ProofsSpine.sigma_inj hww] at hwS
  exact hwS

/-- **Core fact** — for `v ∉ C₋₁`, the 1-edge `(v → σv)` is an edge of `F(P)`. -/
theorem mem_F_sigma_of_not_Cm1 {P : HPath k} {v : Vtx k} (hv : v ∉ Cm1 P) :
    (v, sigma v) ∈ F P := by
  rw [F_eq, fPS, Finset.mem_sdiff]
  set S := Sset P with hS
  refine ⟨?_, ?_⟩
  · by_cases hvP : (v, sigma v) ∈ P.edges
    · rw [Xstep1, Finset.mem_union]; left
      rw [Finset.mem_sdiff]
      refine ⟨hvP, ?_⟩
      intro hc
      rw [E1removed, Finset.mem_filter] at hc
      have hvS : v ∈ S := hc.2
      rw [hS, Sset, Finset.mem_filter] at hvS
      exact hvS.2.2 hvP
    · have hvS : v ∈ S := by
        rw [hS, Sset, Finset.mem_filter]; exact ⟨Finset.mem_univ v, hv, hvP⟩
      rw [Xstep1, Finset.mem_union]; right
      rw [addedEdges, Finset.mem_image]; exact ⟨v, hvS, rfl⟩
  · intro hc
    have hcP : (v, sigma v) ∈ P.edges := E2removed_subset P S hc
    have hvnS : v ∉ S := by
      intro hvS; rw [hS, Sset, Finset.mem_filter] at hvS; exact hvS.2.2 hcP
    rw [E2removed, Finset.mem_filter] at hc
    have hd : sigma v ∈ doubles P S := hc.2
    exact hvnS (mem_S_of_sigma_double hd)

/-- For `k ≥ 2`, `C₀` and `C₋₁` are disjoint (a cycle has a unique first vertex). -/
theorem C0_not_Cm1 {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) {v : Vtx k}
    (hv : v ∈ C0 P) : v ∉ Cm1 P := by
  intro hvm
  rw [C0, Finset.mem_filter] at hv
  rw [Cm1, Finset.mem_filter] at hvm
  have hsuC0 := hvm.2
  rw [C0, Finset.mem_filter] at hsuC0
  have hf1 := hv.2
  have hf2 := hsuC0.2
  have hrc : rotClass (sigma v).1 = rotClass v.1 := rotClass_sigma v
  have hle1 := hf1 (sigma v) hrc
  have hle2 := hf2 v hrc.symm
  have hposeq : P.pos v = P.pos (sigma v) := le_antisymm hle1 hle2
  have hveq : v = sigma v :=
    (ProofsExitless.vert_pos P (hP v)).symm.trans
      (by rw [hposeq]; exact ProofsExitless.vert_pos P (hP (sigma v)))
  have hne : sigma v ≠ v := by
    intro hc
    have := ProofsExitless.sigma_iter_inj v (a := 1) (b := 0) (by omega) (by omega)
      (by simpa using hc)
    omega
  exact hne hveq.symm

/-- Every vertex of `𝒮_k` is incident to an edge of `F(P)` (for `k ≥ 2`), so
`V(F(P)) = V(𝒮_k)`. -/
theorem vertsOf_F_eq_univ {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    vertsOf (F P) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  rw [vertsOf, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hvC0 : v ∈ C0 P
  · exact ⟨(v, sigma v), mem_F_sigma_of_not_Cm1 (C0_not_Cm1 hP hk hvC0), Or.inl rfl⟩
  · have hun : sigmaInv v ∉ Cm1 P := by
      intro h; rw [Cm1, Finset.mem_filter] at h
      rw [sigma_sigmaInv] at h; exact hvC0 h.2
    have hedge : (sigmaInv v, v) ∈ F P := by
      have h := mem_F_sigma_of_not_Cm1 hun; rwa [sigma_sigmaInv] at h
    exact ⟨(sigmaInv v, v), hedge, Or.inr rfl⟩

/-! ## Weight-bookkeeping helpers (for `clm_eqq`) -/

theorem wEdges_union_disjoint {A B : Finset (Vtx k × Vtx k)} (h : Disjoint A B) :
    wEdges (A ∪ B) = wEdges A + wEdges B := by
  simp only [wEdges]; exact Finset.sum_union h

theorem wEdges_sdiff {A B : Finset (Vtx k × Vtx k)} (h : B ⊆ A) :
    wEdges (A \ B) + wEdges B = wEdges A := by
  simp only [wEdges]; exact Finset.sum_sdiff h

/-- `E₂` is genuinely removed from the Step-1 graph (its edges survive Step 1). -/
theorem E2removed_subset_Xstep1 {P : HPath k} {S : Finset (Vtx k)} :
    E2removed P S ⊆ Xstep1 P S := by
  intro e he
  have heP : e ∈ P.edges := E2removed_subset P S he
  rw [E2removed, Finset.mem_filter] at he
  have hd : e.2 ∈ doubles P S := he.2
  simp only [doubles, Finset.mem_filter] at hd
  obtain ⟨-, hd2⟩ := hd
  have hdecomp : intoV (Xstep1 P S) e.2 =
      intoV (P.edges \ E1removed P S) e.2 ∪ intoV (addedEdges S) e.2 := by
    unfold Xstep1; exact ProofsSpine.intoV_union _ _ e.2
  have hBle : (intoV (addedEdges S) e.2).card ≤ 1 := ProofsSpine.intoV_addedEdges_le_one S e.2
  have hAne : (intoV (P.edges \ E1removed P S) e.2).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hA
    rw [hdecomp, hA, Finset.empty_union] at hd2; omega
  obtain ⟨x, hx⟩ := hAne
  simp only [intoV, mem_into, Finset.mem_singleton] at hx
  obtain ⟨hxPE1, hx2⟩ := hx
  have hxP : x ∈ P.edges := (Finset.mem_sdiff.mp hxPE1).1
  have hxe : x = e :=
    Finset.card_le_one.mp (ProofsSpine.path_into_le_one P e.2) x
      (by simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨hxP, hx2⟩) e
      (by simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨heP, trivial⟩)
  rw [← hxe, Xstep1, Finset.mem_union]; exact Or.inl hxPE1

/-- Every added 1-edge has weight one, so `w(addedEdges) = |S|` (for `k ≥ 1`). -/
theorem wEdges_addedEdges {S : Finset (Vtx k)} (hk : 1 ≤ k) :
    wEdges (addedEdges S) = S.card := by
  rw [wEdges, addedEdges,
    Finset.sum_image (by intro a _ b _ hab; exact (Prod.ext_iff.mp hab).1)]
  rw [Finset.sum_congr rfl (fun v _ => ew_sigma hk v), Finset.sum_const, smul_eq_mul, mul_one]

/-- Position of the last vertex is `|p| − 1`. -/
theorem pos_last (p : HPath k) : p.pos p.last = p.numVerts - 1 := by
  rw [Proved.last_eq_vert]
  exact ProofsExitless.pos_vert p (by have := p.numVerts_pos; omega)

/-- The source of a path-edge is never the last (head) vertex. -/
theorem ne_last_of_out_edge {P : HPath k} {a b : Vtx k} (h : (a, b) ∈ P.edges) :
    a ≠ P.last := by
  intro hcon
  have hps := edge_pos_succ h
  have hbz : (a, b) ∈ P.verts.zip P.verts.tail := ProofsSpine.mem_edges_iff.mp h
  have hbt : b ∈ P.verts.tail := ProofsSpine.snd_mem_tail hbz
  have hb : b ∈ P.verts := P.verts.tail_sublist.subset hbt
  have hposb := ProofsExitless.pos_lt P hb
  have hposlast := pos_last P
  rw [hcon, hposlast] at hps
  have := P.numVerts_pos
  omega

/-- A non-last vertex of `P` (that lies on `P`) has an out-edge. -/
theorem out_edge_of_ne_last {P : HPath k} {v : Vtx k} (hv : v ∈ P.verts)
    (hne : v ≠ P.last) : ∃ w, (v, w) ∈ P.edges := by
  have hpos : P.pos v < P.numVerts := ProofsExitless.pos_lt P hv
  have hposlast := pos_last P
  have hne' : P.pos v ≠ P.numVerts - 1 := by
    intro hcon
    apply hne
    have h1 := ProofsExitless.vert_pos P hv
    have h2 := Proved.last_eq_vert P
    rw [← h1, hcon, ← h2]
  have hbound : P.pos v + 1 < P.numVerts := by omega
  have hedge : (P.vert (P.pos v), P.vert (P.pos v + 1)) ∈ P.edges :=
    vert_consec_mem_edges hbound
  rw [ProofsExitless.vert_pos P hv] at hedge
  exact ⟨P.vert (P.pos v + 1), hedge⟩

/-- The Step-1 edge count `|E₁| + I = |S|` (needs `S ⊆ V(P)`). -/
theorem E1removed_card {P : HPath k} {S : Finset (Vtx k)} (hSV : S ⊆ P.vertsFinset) :
    (E1removed P S).card + indicatorI P S = S.card := by
  have hinj : Set.InjOn Prod.fst (E1removed P S : Set (Vtx k × Vtx k)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, E1removed, Finset.mem_filter] at ha hb
    exact Finset.card_le_one.mp (ProofsSpine.path_out_le_one P a.1) a
      (by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨ha.1, trivial⟩) b
      (by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hb.1, hab.symm⟩)
  have himg : (E1removed P S).image Prod.fst = S.filter (fun v => ¬ v = P.last) := by
    ext v
    simp only [Finset.mem_image, E1removed, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨heP, heS⟩, rfl⟩
      exact ⟨heS, ne_last_of_out_edge heP⟩
    · rintro ⟨hvS, hvne⟩
      obtain ⟨w, hw⟩ := out_edge_of_ne_last (HPath.mem_vertsFinset.mp (hSV hvS)) hvne
      exact ⟨(v, w), ⟨hw, hvS⟩, rfl⟩
  have hcard1 : (E1removed P S).card = (S.filter (fun v => ¬ v = P.last)).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  have hI : indicatorI P S = (S.filter (fun v => v = P.last)).card := by
    rw [indicatorI, Finset.filter_eq']
    by_cases h : P.last ∈ S <;> simp [h]
  have hkey := Finset.card_filter_add_card_filter_not (s := S) (p := fun v => v = P.last)
  rw [hcard1, hI]; omega

end ProofsStructure

/-! ## Targets (statements copied verbatim from `Hunter/Statements.lean`) -/

namespace Proved

open ProofsStructure
open scoped Classical

variable {k : ℕ}

/-- **clm-rule2** — `v ∉ C₋₁ ⟹ out(X,v) = {(v→σv)}`. -/
theorem clm_rule2 {P : HPath k} (_hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∉ Cm1 P) :
    outV (F P) v = {(v, sigma v)} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  have hmem : (v, sigma v) ∈ outV (F P) v := by
    simp only [outV, mem_out, Finset.mem_singleton]
    exact ⟨mem_F_sigma_of_not_Cm1 hv, trivial⟩
  refine ⟨hmem, ?_⟩
  intro x hx
  have hle : (outV (F P) v).card ≤ 1 := by
    rw [F_eq]; exact ProofsSpine.outV_fPS_le_one P (Sset P) v
  exact Finset.card_le_one.mp hle x hx (v, sigma v) hmem

/-- **clm-rule2.75** — every `u ∉ C₋₁` has its 1-edge `(u→σu) ∈ X`. -/
theorem clm_rule2_75 {P : HPath k} (_hP : P.IsHamiltonian) {u : Vtx k}
    (hu : u ∉ Cm1 P) :
    (u, sigma u) ∈ F P :=
  mem_F_sigma_of_not_Cm1 hu

/-- **clm-rule1** — `v ∈ C₋₁` with an out-edge keeps its `P`-out-edge. -/
theorem clm_rule1 {P : HPath k} (_hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∈ Cm1 P) (hne : outV (F P) v ≠ ∅) :
    outV (F P) v = outV P.edges v := by
  have hvnS : v ∉ Sset P := by
    intro h; rw [Sset, Finset.mem_filter] at h; exact h.2.1 hv
  have hsub : outV (F P) v ⊆ outV P.edges v := by
    intro e he
    simp only [outV, mem_out, Finset.mem_singleton] at he ⊢
    obtain ⟨heF, he1⟩ := he
    refine ⟨?_, he1⟩
    have heX1 : e ∈ Xstep1 P (Sset P) := fPS_subset_step1 P (Sset P) heF
    rw [Xstep1, Finset.mem_union] at heX1
    rcases heX1 with hPE | hA
    · exact (Finset.mem_sdiff.mp hPE).1
    · exfalso
      rw [addedEdges, Finset.mem_image] at hA
      obtain ⟨w, hwS, hwe⟩ := hA
      have hwv : w = v := by rw [← hwe] at he1; exact he1
      exact hvnS (hwv ▸ hwS)
  have hcard : (outV P.edges v).card ≤ 1 := ProofsSpine.path_out_le_one P v
  have hpos : 1 ≤ (outV (F P) v).card :=
    Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr hne)
  exact Finset.eq_of_subset_of_card_le hsub (le_trans hcard hpos)

/-- **clm-rule2.5** — `v ∉ C₀ ⟹ into(X,v) = {(σ⁻¹v→v)}`. -/
theorem clm_rule2_5 {P : HPath k} (_hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∉ C0 P) :
    intoV (F P) v = {(sigmaInv v, v)} := by
  have hsu : sigma (sigmaInv v) = v := sigma_sigmaInv v
  have hunC : sigmaInv v ∉ Cm1 P := by
    intro h; rw [Cm1, Finset.mem_filter] at h
    rw [hsu] at h; exact hv h.2
  have hedge : (sigmaInv v, v) ∈ F P := by
    have h := mem_F_sigma_of_not_Cm1 hunC
    rwa [hsu] at h
  have hmem : (sigmaInv v, v) ∈ intoV (F P) v := by
    simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨hedge, trivial⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmem, ?_⟩
  intro x hx
  have hle : (intoV (F P) v).card ≤ 1 := by
    rw [F_eq]; exact ProofsSpine.intoV_fPS_le_one P (Sset P) (sset_sPrecond P) v
  exact Finset.card_le_one.mp hle x hx (sigmaInv v, v) hmem

/-- **clm-rule3** — `u ∈ C₋₁` with an out-edge leaves to a `C₀`-vertex. -/
theorem clm_rule3 {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hu : u ∈ Cm1 P) (hne : outV (F P) u ≠ ∅) :
    ∃ v, v ∈ C0 P ∧ outV (F P) u = {(u, v)} := by
  have h1 := clm_rule1 hP hu hne
  have hnesub : (outV P.edges u).Nonempty := by
    rw [← h1]; exact Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨e, he⟩ := hnesub
  have he1 : e.1 = u := by
    simp only [outV, mem_out, Finset.mem_singleton] at he; exact he.2
  set v := e.2 with hvdef
  have hev : e = (u, v) := by rw [← he1, hvdef]
  have heF : e ∈ F P := by
    have hmem : e ∈ outV (F P) u := by rw [h1]; exact he
    simp only [outV, mem_out] at hmem; exact hmem.1
  have huvF : (u, v) ∈ F P := hev ▸ heF
  refine ⟨v, ?_, ?_⟩
  · by_contra hvnC0
    have h25 := clm_rule2_5 hP hvnC0
    have hin : (u, v) ∈ intoV (F P) v := by
      simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨huvF, trivial⟩
    rw [h25, Finset.mem_singleton] at hin
    have husi : u = sigmaInv v := (Prod.ext_iff.mp hin).1
    have hvsu : v = sigma u := by rw [husi, sigma_sigmaInv]
    have hsuC0 : sigma u ∈ C0 P := by rw [Cm1, Finset.mem_filter] at hu; exact hu.2
    rw [← hvsu] at hsuC0
    exact hvnC0 hsuC0
  · rw [h1]
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hev ▸ he, ?_⟩
    intro x hx
    exact Finset.card_le_one.mp (ProofsSpine.path_out_le_one P u) x hx e he |>.trans hev

/-- **rmk-rule3** — the `C₀`-target of `u ∈ C₋₁`'s out-edge is never `σ(u)`. -/
theorem rmk_rule3 {P : HPath k} (hP : P.IsHamiltonian) {u v : Vtx k}
    (hu : u ∈ Cm1 P) (h : (u, v) ∈ F P) : v ≠ sigma u := by
  intro hvsu
  subst hvsu
  have hne : outV (F P) u ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]
    exact ⟨(u, sigma u), by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩⟩
  have h1 := clm_rule1 hP hu hne
  have huv : (u, sigma u) ∈ P.edges := by
    have hmem : (u, sigma u) ∈ outV (F P) u := by
      simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩
    rw [h1] at hmem
    simp only [outV, mem_out] at hmem; exact hmem.1
  have hpos := edge_pos_succ huv
  have hsuC0 : sigma u ∈ C0 P := by rw [Cm1, Finset.mem_filter] at hu; exact hu.2
  rw [C0, Finset.mem_filter] at hsuC0
  have hfirst := hsuC0.2
  have hrc : rotClass u.1 = rotClass (sigma u).1 := (rotClass_sigma u).symm
  have hle := hfirst u hrc
  omega

/-! ## The central lemma `lem_walking` -/

/-- Auxiliary for `lem_walking` / `clm_ordering`, phrased over `getElem` indices with strong
induction on the gap `j − i`.  The *start* `D[i]` must be a `C₀ ∪ C₋₁` vertex; the endpoint
`D[j]` is arbitrary (this is what lets it prove `clm_ordering` for a non-special `u`). -/
theorem walking_aux {P : HPath k} (hP : P.IsHamiltonian) {D : List (Vtx k)}
    (hD : IsWalk (F P) D) :
    ∀ (g i j : ℕ) (hi : i < D.length) (hj : j < D.length), j - i = g → i < j →
      D[i] ∈ C0 P ∪ Cm1 P → P.pos D[i] < P.pos D[j] := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g IH =>
    intro i j hi hj hg hij hDi
    rcases Classical.em (∃ t : ℕ, ∃ (ht : t < D.length),
        i < t ∧ t < j ∧ D[t]'ht ∈ C0 P ∪ Cm1 P) with hA | hA
    · obtain ⟨t, ht, hit, htj, hDt⟩ := hA
      have h1 := IH (t - i) (by omega) i t hi ht (by omega) hit hDi
      have h2 := IH (j - t) (by omega) t j ht hj (by omega) htj hDt
      omega
    · have hi1 : i + 1 < D.length := by omega
      have hedge0 : (D[i], D[i + 1]) ∈ F P := List.IsChain.getElem hD i hi1
      by_cases huCm1 : D[i] ∈ Cm1 P
      · have hne : outV (F P) D[i] ≠ ∅ := by
          rw [← Finset.nonempty_iff_ne_empty]
          exact ⟨(D[i], D[i + 1]), by
            simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hedge0, trivial⟩⟩
        obtain ⟨w, hwC0, hout⟩ := clm_rule3 hP huCm1 hne
        have hDi1w : D[i + 1] = w := by
          have hmem : (D[i], D[i + 1]) ∈ outV (F P) D[i] := by
            simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hedge0, trivial⟩
          rw [hout, Finset.mem_singleton] at hmem
          exact (Prod.ext_iff.mp hmem).2
        have hij1 : i + 1 = j := by
          by_contra hne'
          exact hA ⟨i + 1, hi1, by omega, by omega,
            show D[i + 1]'hi1 ∈ C0 P ∪ Cm1 P by
              rw [hDi1w]; exact Finset.mem_union.mpr (Or.inl hwC0)⟩
        have h1 := clm_rule1 hP huCm1 hne
        have hPedge : (D[i], w) ∈ P.edges := by
          have hmem : (D[i], w) ∈ outV (F P) D[i] := by
            rw [hout]; exact Finset.mem_singleton_self _
          rw [h1] at hmem
          simp only [outV, mem_out] at hmem; exact hmem.1
        have hpossucc := edge_pos_succ hPedge
        subst hij1
        rw [hDi1w]; omega
      · have huC0 : D[i] ∈ C0 P := by
          rcases Finset.mem_union.mp hDi with h | h
          · exact h
          · exact absurd h huCm1
        have hk2 : 2 ≤ k := two_le_of_not_Cm1 huCm1
        have orbit : ∀ m, m ≤ g → ∀ (hm : i + m < D.length),
            D[i + m]'hm = sigma^[m] D[i] := by
          intro m
          induction m with
          | zero => intro _ hm; simp
          | succ n ih =>
            intro hmg hm
            have hnlt : i + n < D.length := by omega
            have hDn := ih (by omega) hnlt
            have hnotCm1 : D[i + n]'hnlt ∉ Cm1 P := by
              rcases Nat.eq_zero_or_pos n with hn0 | hn0
              · subst hn0; simpa using huCm1
              · intro hc
                exact hA ⟨i + n, hnlt, by omega, by omega, Finset.mem_union.mpr (Or.inr hc)⟩
            have hedge : (D[i + n], D[i + n + 1]) ∈ F P :=
              List.IsChain.getElem hD (i + n) (by omega)
            have hr2 := clm_rule2 hP hnotCm1
            have hmem : (D[i + n], D[i + n + 1]) ∈ outV (F P) D[i + n] := by
              simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hedge, trivial⟩
            rw [hr2, Finset.mem_singleton] at hmem
            have hnext : D[i + n + 1] = sigma D[i + n] := (Prod.ext_iff.mp hmem).2
            show D[(i + n) + 1]'hm = sigma^[n + 1] D[i]
            rw [hnext, hDn, Function.iterate_succ_apply']
        have hg1 : 1 ≤ g := by omega
        have hvorbit : D[j] = sigma^[g] D[i] := by
          have h := orbit g (le_refl g) (by omega)
          rw [getElem_eq_of_index_eq (show j = i + g from by omega) hj (by omega)]
          exact h
        have hrc : rotClass D[j].1 = rotClass D[i].1 := by
          rw [hvorbit]; exact ProofsExitless.rotClass_sigma_iter g D[i]
        have hfirst : firstInCycle P D[i] := by
          rw [C0, Finset.mem_filter] at huC0; exact huC0.2
        have hle : P.pos D[i] ≤ P.pos D[j] := hfirst D[j] hrc
        have hne_uv : D[j] ≠ D[i] := by
          rw [hvorbit]
          intro hcon
          have hgk : g < k := by
            by_contra hgk'
            push Not at hgk'
            have hspecial : sigma^[k - 1] D[i] ∈ Cm1 P := by
              rw [Cm1, Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have hstep : sigma (sigma^[k - 1] D[i]) = D[i] := by
                have e1 : sigma (sigma^[k - 1] D[i]) = sigma^[(k - 1) + 1] D[i] :=
                  (Function.iterate_succ_apply' sigma (k - 1) D[i]).symm
                rw [e1, show (k - 1) + 1 = k from by omega, ProofsExitless.sigma_iter_period]
              rw [hstep]; exact huC0
            have hik1 : i + (k - 1) < D.length := by omega
            have hik : D[i + (k - 1)]'hik1 = sigma^[k - 1] D[i] :=
              orbit (k - 1) (by omega) hik1
            exact hA ⟨i + (k - 1), hik1, by omega, by omega,
              show D[i + (k - 1)]'hik1 ∈ C0 P ∪ Cm1 P by
                rw [hik]; exact Finset.mem_union.mpr (Or.inr hspecial)⟩
          have hcon' : sigma^[g] D[i] = sigma^[0] D[i] := by simpa using hcon
          have := ProofsExitless.sigma_iter_inj D[i] hgk (by omega) hcon'
          omega
        have hposne : P.pos D[i] ≠ P.pos D[j] := by
          intro hcon
          apply hne_uv
          have hui := ProofsExitless.vert_pos P (hP D[i])
          have hvj := ProofsExitless.vert_pos P (hP D[j])
          rw [← hui, ← hvj, hcon]
        omega

/-- **lem-walking** — central lemma: order along a directed walk in `F(P)` (restricted to
`C₀ ∪ C₋₁`) refines the order in `P`. -/
theorem lem_walking {P : HPath k} (hP : P.IsHamiltonian)
    {D : List (Vtx k)} (hD : IsWalk (F P) D) {u v : Vtx k}
    (hu : u ∈ C0 P ∪ Cm1 P) (_hv : v ∈ C0 P ∪ Cm1 P)
    (huD : u ∈ D) (hvD : v ∈ D) (hlt : D.idxOf u < D.idxOf v) :
    P.pos u < P.pos v := by
  have hiu : D.idxOf u < D.length := List.idxOf_lt_length_of_mem huD
  have hiv : D.idxOf v < D.length := List.idxOf_lt_length_of_mem hvD
  have hgu : D[D.idxOf u]'hiu = u := List.getElem_idxOf hiu
  have hgv : D[D.idxOf v]'hiv = v := List.getElem_idxOf hiv
  have key := walking_aux hP hD (D.idxOf v - D.idxOf u) (D.idxOf u) (D.idxOf v) hiu hiv rfl hlt
    (by rw [hgu]; exact hu)
  rwa [hgu, hgv] at key

/-- The vertex list of a path-component of `F(P)` is a directed walk in `F(P)`. -/
theorem isWalk_verts {P : HPath k} {p : HPath k} (hp : IsPathComponent p (F P)) :
    IsWalk (F P) p.verts := by
  rw [IsWalk, List.isChain_iff_getElem]
  intro i hi
  exact hp.1 (ProofsStructure.consec_mem_edges hi)

/-- **clm-ordering** — order along a path-component (from a `C₀ ∪ C₋₁` vertex) refines `P`. -/
theorem clm_ordering {P : HPath k} (hP : P.IsHamiltonian)
    {p : HPath k} (hp : IsPathComponent p (F P)) {v u : Vtx k}
    (hv : v ∈ C0 P ∪ Cm1 P) (hvp : v ∈ p.verts) (hup : u ∈ p.verts)
    (hlt : p.pos v < p.pos u) : P.pos v < P.pos u := by
  have hwalk := isWalk_verts hp
  have hiv : p.pos v < p.verts.length := ProofsExitless.pos_lt p hvp
  have hiu : p.pos u < p.verts.length := ProofsExitless.pos_lt p hup
  have hgv : p.verts[p.pos v]'hiv = v := by
    rw [← ProofsExitless.vert_getElem p hiv]; exact ProofsExitless.vert_pos p hvp
  have hgu : p.verts[p.pos u]'hiu = u := by
    rw [← ProofsExitless.vert_getElem p hiu]; exact ProofsExitless.vert_pos p hup
  have key := walking_aux hP hwalk (p.pos u - p.pos v) (p.pos v) (p.pos u) hiv hiu rfl hlt
    (by rw [hgv]; exact hv)
  rwa [hgv, hgu] at key

/-- **cor-pathfirst** — `p[1]` is the `P`-earliest vertex of a path-component `p` of `F(P)`. -/
theorem cor_pathfirst {P : HPath k} (hP : P.IsHamiltonian)
    {p : HPath k} (hp : IsPathComponent p (F P)) {u : Vtx k} (hu : u ∈ p.verts) :
    P.pos p.first ≤ P.pos u := by
  have htail : intoV (F P) p.first = ∅ := by
    have h := ProofsSpine.compTails_eq hp
    have hmem : p.first ∈ compTails (F P) p.vertsFinset := by
      rw [h]; exact Finset.mem_singleton_self _
    rw [compTails, Finset.mem_filter] at hmem
    exact hmem.2
  have hfirstC0 : p.first ∈ C0 P := by
    by_contra hc
    have h25 := clm_rule2_5 hP hc
    rw [h25] at htail
    exact absurd htail (Finset.singleton_ne_empty _)
  by_cases heq : u = p.first
  · rw [heq]
  · have h0 : p.pos p.first = 0 := ProofsStructure.pos_first p
    have hupos : 0 < p.pos u := by
      rcases Nat.eq_zero_or_pos (p.pos u) with h | h
      · exfalso
        have hvp := ProofsExitless.vert_pos p hu
        rw [h, p.vert_zero] at hvp
        exact heq hvp.symm
      · exact h
    exact le_of_lt (clm_ordering hP hp (Finset.mem_union.mpr (Or.inl hfirstC0))
      p.first_mem hu (by omega))

/-! ## §4 weight bookkeeping `clm_eqq` (amended: `1 ≤ k` and `S ⊆ V(P)`) -/

/-- **clm-eqq** (amended) — the exact weight bookkeeping for `X = f(P,S)`.  The verbatim
statement is FALSE at `k = 0` (self-loop `w = 0`) and for `S ⊄ V(P)` (uncounted added
edges); see `PROGRESS-structure.md`.  With `1 ≤ k` and `S ⊆ V(P)` (both implied by the
paper's Hamiltonian `P`, `k ≥ 3` regime) it holds. -/
theorem clm_eqq_amended {P : HPath k} {S : Finset (Vtx k)} (hk : 1 ≤ k)
    (hSV : S ⊆ P.vertsFinset) (hS : SPrecond P S) :
    (P.wtP : ℤ) = (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ E2removed P S, (ew k e.1 e.2 : ℤ) := by
  have hstar : wEdges (fPS P S) + wEdges (E1removed P S) + wEdges (E2removed P S)
      = wEdges P.edges + wEdges (addedEdges S) := by
    have hb : wEdges (Xstep1 P S) = wEdges (fPS P S) + wEdges (E2removed P S) :=
      (ProofsStructure.wEdges_sdiff
        (ProofsStructure.E2removed_subset_Xstep1 (P := P) (S := S))).symm
    have hdisj : Disjoint (P.edges \ E1removed P S) (addedEdges S) := by
      rw [Finset.disjoint_left]
      intro e he heA
      rw [addedEdges, Finset.mem_image] at heA
      obtain ⟨w, hwS, hwe⟩ := heA
      have heP : e ∈ P.edges := (Finset.mem_sdiff.mp he).1
      rw [← hwe] at heP
      exact hS w hwS heP
    have hc : wEdges (Xstep1 P S)
        = wEdges (P.edges \ E1removed P S) + wEdges (addedEdges S) := by
      rw [Xstep1]; exact ProofsStructure.wEdges_union_disjoint hdisj
    have hd : wEdges (P.edges \ E1removed P S) + wEdges (E1removed P S) = wEdges P.edges :=
      ProofsStructure.wEdges_sdiff (E1removed_subset P S)
    omega
  have hL2 : wEdges (addedEdges S) = S.card := ProofsStructure.wEdges_addedEdges hk
  have hL3 : (E1removed P S).card + indicatorI P S = S.card :=
    ProofsStructure.E1removed_card hSV
  have hcastE1 : (wEdges (E1removed P S) : ℤ) = ∑ e ∈ E1removed P S, (ew k e.1 e.2 : ℤ) := by
    rw [wEdges, Nat.cast_sum]
  have hcastE2 : (wEdges (E2removed P S) : ℤ) = ∑ e ∈ E2removed P S, (ew k e.1 e.2 : ℤ) := by
    rw [wEdges, Nat.cast_sum]
  have hsplit1 : ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1)
      = (wEdges (E1removed P S) : ℤ) - ((E1removed P S).card : ℤ) := by
    rw [Finset.sum_sub_distrib, hcastE1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbridge : (P.wtP : ℤ) = (wEdges P.edges : ℤ) := by
    rw [bridge_wEdges_edges_eq_wtP]
  have hstarZ : (wEdges (fPS P S) : ℤ) + (wEdges (E1removed P S) : ℤ)
      + (wEdges (E2removed P S) : ℤ) = (wEdges P.edges : ℤ) + (wEdges (addedEdges S) : ℤ) := by
    exact_mod_cast hstar
  have hL2Z : (wEdges (addedEdges S) : ℤ) = (S.card : ℤ) := by exact_mod_cast hL2
  have hL3Z : ((E1removed P S).card : ℤ) + (indicatorI P S : ℤ) = (S.card : ℤ) := by
    exact_mod_cast hL3
  rw [hbridge, hsplit1, ← hcastE2]
  linarith [hstarZ, hL2Z, hL3Z]

/-- **prp-Xk-se (necessity)** (amended) — proved taking `cor_exitlessrule` (`h_se`, a §5
target routed through the unproved `lem_pathrule`) as an explicit hypothesis, and with the
`k ≥ 2` guard the `V(X) = V(𝒮_k)` half genuinely needs (it is FALSE at `k = 1`, where
`F(P) = ∅`).  The `V(F(P)) = V(𝒮_k)` half is discharged outright via `vertsOf_F_eq_univ`. -/
theorem prp_Xk_se_necessity_amended {k : ℕ} {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k)
    (h_se : ∀ P : HPath k, P.IsHamiltonian → IsUnionOfStronglyExitlessPaths (F P))
    (hX : X ∈ Xk k) :
    vertsOf X = Finset.univ ∧ IsUnionOfStronglyExitlessPaths X := by
  obtain ⟨P, hP, hFX⟩ := hX
  subst hFX
  exact ⟨ProofsStructure.vertsOf_F_eq_univ hP hk, h_se P hP⟩

end Proved

end Hunter

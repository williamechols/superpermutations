/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsUnwind2

/-!
# Closing the unwinding residual `hdec` (Hunter §5, `prp-Xk-se` sufficiency)

This file continues `Hunter/ProofsUnwind2.lean`.  Its goal is to discharge the single
remaining hypothesis `hdec` of `prp_Xk_se_sufficiency_unwind2` — the **edge decomposition**
of the unwound path `P = unwindP ps`:

    E(P) = (X ∖ FE) ∪ E1removed ∪ E2removed

with `X = ⋃ᵢ E(pᵢ)`, `FE = addedEdges (headSet)`, `E1removed` the head-chain and
`E2removed` the back-links — plus the three natural disjointnesses.

The argument is the mechanical `zip`/`getElem` classification of the consecutive pairs of the
concatenation `unwindVerts ps = heads ++ tails`, using the positional toolkit from
`ProofsUnwind2` (KEY ORDER, `interior_edge_mem`, `junction_edge_mem`,
`first_edge_not_mem_edges`) and the `doubles` in-degree-2 bookkeeping (`key_doubles_iff`).

See `PROGRESS-unwind3.md`.
-/

namespace Hunter.ProofsUnwind3

open List
open Hunter.ProofsUnwind
open Hunter.ProofsUnwind2
open scoped Classical

variable {k : ℕ}

/-! ## Component-edge basics: the first-edge of an SE component -/

/-- For a strongly exitless component, `p[2] = σ(p[1])` — the second vertex is the σ-successor
of the first. -/
theorem vert1_eq_sigma_first {p : HPath k} (hpSE : p.StronglyExitless) (hk : 2 ≤ k) :
    p.vert 1 = sigma p.first := by
  have hk1 : 1 ≤ k := by omega
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk1 hpSE
  have hkle : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
  have h1lt : 1 < p.numVerts := by omega
  have hkndvd : ¬ k ∣ (0 + 1) := by
    intro h; have := Nat.le_of_dvd (show 0 < 0 + 1 by omega) h; omega
  have h := ProofsExitless.vert_succ hk1 hpSE.1 (i := 0) (show 0 + 1 < p.numVerts by omega) hkndvd
  rwa [p.vert_zero] at h

/-- `1 < |p|` for an SE component (needs `2 ≤ k`). -/
theorem one_lt_numVerts {p : HPath k} (hpSE : p.StronglyExitless) (hk : 2 ≤ k) :
    1 < p.numVerts := by
  have hk1 : 1 ≤ k := by omega
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk1 hpSE
  have hkle : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
  omega

/-- The first-edge `p[1] → σ(p[1])` is a genuine edge of `p`. -/
theorem first_edge_mem_self {p : HPath k} (hpSE : p.StronglyExitless) (hk : 2 ≤ k) :
    (p.first, sigma p.first) ∈ p.edges := by
  have h1lt : 1 < p.numVerts := one_lt_numVerts hpSE hk
  have h01 := ProofsStructure.vert_consec_mem_edges (p := p) (i := 0) (by omega)
  rwa [p.vert_zero, vert1_eq_sigma_first hpSE hk] at h01

/-- An edge of `p` is a consecutive pair `(p[j], p[j+1])` with `j = pos(e.1)` and
`j + 1 < |p|`. -/
theorem edge_eq_consec {p : HPath k} {e : Vtx k × Vtx k} (he : e ∈ p.edges) :
    e = (p.vert (p.pos e.1), p.vert (p.pos e.1 + 1)) ∧ p.pos e.1 + 1 < p.numVerts := by
  have hpos := ProofsStructure.edge_pos_succ he
  -- e.1, e.2 ∈ p.verts
  have h1mem : e.1 ∈ p.verts := by
    have := ProofsSpine.mem_edges_iff.mp he
    exact List.of_mem_zip this |>.1
  have h2mem : e.2 ∈ p.verts := by
    have := ProofsSpine.mem_edges_iff.mp he
    exact List.mem_of_mem_tail (List.of_mem_zip this |>.2)
  have hv1 : p.vert (p.pos e.1) = e.1 := ProofsExitless.vert_pos p h1mem
  have hv2 : p.vert (p.pos e.2) = e.2 := ProofsExitless.vert_pos p h2mem
  have hlt : p.pos e.2 < p.numVerts := ProofsExitless.pos_lt p h2mem
  refine ⟨?_, by rw [← hpos]; exact hlt⟩
  rw [hv1, ← hpos, hv2]

/-! ## The `headSet` and `addedEdges` bookkeeping -/

/-- Abbreviation for the paper's `S(P) = {pᵢ[1] : i < n}`. -/
@[reducible] def headSet (ps : List (HPath k)) : Finset (Vtx k) :=
  (ps.dropLast.map HPath.first).toFinset

/-- `v ∈ headSet ↔ v` is a first-vertex of some non-last component. -/
theorem mem_headSet {ps : List (HPath k)} {v : Vtx k} :
    v ∈ headSet ps ↔ ∃ q ∈ ps.dropLast, q.first = v := by
  rw [headSet, List.mem_toFinset, List.mem_map]

/-- The first-edge of a non-last component is an added 1-edge. -/
theorem first_edge_mem_addedEdges {ps : List (HPath k)} {p : HPath k}
    (hpdl : p ∈ ps.dropLast) :
    (p.first, sigma p.first) ∈ addedEdges (headSet ps) := by
  rw [addedEdges, Finset.mem_image]
  exact ⟨p.first, mem_headSet.mpr ⟨p, hpdl, rfl⟩, rfl⟩

/-- An added 1-edge `(v, σv)` has `v = q.first` for a non-last component `q`, and equals that
component's first-edge. -/
theorem mem_addedEdges_iff {ps : List (HPath k)} {e : Vtx k × Vtx k} :
    e ∈ addedEdges (headSet ps) ↔ ∃ q ∈ ps.dropLast, e = (q.first, sigma q.first) := by
  rw [addedEdges, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨q, hq, rfl⟩ := mem_headSet.mp hv
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.first, mem_headSet.mpr ⟨q, hq, rfl⟩, rfl⟩

/-! ## The `⊇` direction: `X ∖ FE ⊆ E(P)` -/

/-- **Every component-edge not detoured survives in `P`.**  A `p`-edge `e` (for `p ∈ ps`) that
is not one of the removed first-edges (`e ∉ addedEdges (headSet)`) is an edge of the unwound
path.  Interior edges survive by `interior_edge_mem`; the last component's first-edge by
`junction_edge_mem`; a non-last component's first-edge is exactly the removed one. -/
theorem component_edge_mem_P {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    {p : HPath k} (hp : p ∈ ps) {e : Vtx k × Vtx k} (he : e ∈ p.edges)
    (heFE : e ∉ addedEdges (headSet ps)) :
    e ∈ (unwindP ps hps hnd).edges := by
  have hpSE := hSE p hp
  obtain ⟨heq, hlt⟩ := edge_eq_consec he
  set j := p.pos e.1 with hj
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- `j = 0`: `e = (p.first, σ p.first)`
    rw [hj0] at heq hlt
    have he0 : e = (p.first, sigma p.first) := by
      rw [heq, p.vert_zero, vert1_eq_sigma_first hpSE hk]
    by_cases hpdl : p ∈ ps.dropLast
    · exact absurd (he0 ▸ first_edge_mem_addedEdges hpdl) heFE
    · -- `p` is the last component: junction edge
      have hsplit := List.dropLast_append_getLast hps
      have hmem2 : p ∈ ps.dropLast ++ [ps.getLast hps] := hsplit.symm ▸ hp
      rw [List.mem_append, List.mem_singleton] at hmem2
      have hpeq : p = ps.getLast hps := hmem2.resolve_left hpdl
      rw [he0, hpeq]
      exact junction_edge_mem hps hnd hSE hk
  · -- `j ≥ 1`: interior edge
    rw [heq]
    exact interior_edge_mem hps hnd hp hj1 hlt

/-- **`X ∖ FE ⊆ E(P)`.**  With `X = ⋃ᵢ E(pᵢ)`, every edge of `X` that is not a removed
first-edge is an edge of the unwound path. -/
theorem sdiff_subset_edges {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    X \ addedEdges (headSet ps) ⊆ (unwindP ps hps hnd).edges := by
  intro e he
  rw [Finset.mem_sdiff] at he
  obtain ⟨p, hp, hep⟩ := (hXdef e).mp he.1
  exact component_edge_mem_P hps hnd hSE hk hp hep he.2

/-- **`addedEdges (headSet) ⊆ X`.**  Each removed first-edge `(pᵢ[1], σpᵢ[1])` is a genuine
edge of its component `pᵢ`, hence in `X`. -/
theorem addedEdges_subset_X {ps : List (HPath k)}
    (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    addedEdges (headSet ps) ⊆ X := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := mem_addedEdges_iff.mp he
  have hqmem : q ∈ ps := List.dropLast_subset ps hq
  exact (hXdef _).mpr ⟨q, hqmem, first_edge_mem_self (hSE q hqmem) hk⟩

/-! ## `doubles` bookkeeping -/

/-- **Creating a double.**  If `(a,b)` is a `P`-edge whose source `a ∉ S`, and some `v ∈ S`
has `σv = b`, then `b` has in-degree 2 in `Xstep1` (the surviving `P`-in-edge `(a,b)` plus the
added 1-edge `(v,b)`), i.e. `b ∈ doubles P S`. -/
theorem mem_doubles_of (P : HPath k) (S : Finset (Vtx k)) {a b v : Vtx k}
    (hab : (a, b) ∈ P.edges) (haS : a ∉ S) (hvS : v ∈ S) (hσ : sigma v = b) :
    b ∈ doubles P S := by
  rw [doubles, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hdecomp : intoV (Xstep1 P S) b =
      intoV (P.edges \ E1removed P S) b ∪ intoV (addedEdges S) b := by
    unfold Xstep1; exact ProofsSpine.intoV_union _ _ b
  have hab1 : (a, b) ∈ intoV (P.edges \ E1removed P S) b := by
    rw [intoV, mem_into, Finset.mem_singleton]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_sdiff]
    exact ⟨hab, fun hc => haS (by rw [E1removed, Finset.mem_filter] at hc; exact hc.2)⟩
  have hvb1 : (v, b) ∈ intoV (addedEdges S) b := by
    rw [intoV, mem_into, Finset.mem_singleton]
    exact ⟨by rw [addedEdges, Finset.mem_image]; exact ⟨v, hvS, by rw [hσ]⟩, rfl⟩
  have hne : ((a, b) : Vtx k × Vtx k) ≠ (v, b) := by
    intro h; rw [Prod.mk.injEq] at h; exact haS (h.1 ▸ hvS)
  have hsub : ({(a, b), (v, b)} : Finset (Vtx k × Vtx k)) ⊆ intoV (Xstep1 P S) b := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hdecomp, Finset.mem_union]
    rcases hx with rfl | rfl
    · exact Or.inl hab1
    · exact Or.inr hvb1
  have hge : 2 ≤ (intoV (Xstep1 P S) b).card := by
    have hpc : ({(a, b), (v, b)} : Finset (Vtx k × Vtx k)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    calc 2 = ({(a, b), (v, b)} : Finset (Vtx k × Vtx k)).card := hpc.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hAle : (intoV (P.edges \ E1removed P S) b).card ≤ 1 :=
    le_trans (Finset.card_le_card (ProofsSpine.intoV_mono Finset.sdiff_subset b))
      (ProofsSpine.path_into_le_one P b)
  have hBle : (intoV (addedEdges S) b).card ≤ 1 := ProofsSpine.intoV_addedEdges_le_one S b
  have hle : (intoV (Xstep1 P S) b).card ≤ 2 := by
    rw [hdecomp]
    exact le_trans (Finset.card_union_le _ _) (by omega)
  omega

/-- **A double has an incoming added 1-edge.**  If `b ∈ doubles P S`, then `b = σv` for some
`v ∈ S`. -/
theorem mem_doubles_imp {P : HPath k} {S : Finset (Vtx k)} {b : Vtx k}
    (hb : b ∈ doubles P S) : ∃ v ∈ S, sigma v = b := by
  have hne := ProofsStructure.double_imp_added_inedge hb
  obtain ⟨e, he⟩ := hne
  rw [intoV, mem_into, Finset.mem_singleton] at he
  obtain ⟨heA, he2⟩ := he
  rw [addedEdges, Finset.mem_image] at heA
  obtain ⟨v, hvS, rfl⟩ := heA
  exact ⟨v, hvS, he2⟩

/-! ## Component vertex-disjointness (well-formedness) -/

/-- From pairwise vertex-disjointness of the components, a vertex shared by two components
forces the components to coincide. -/
theorem comp_eq_of_shared {ps : List (HPath k)}
    (hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset))
    {p q : HPath k} (hp : p ∈ ps) (hq : q ∈ ps) {v : Vtx k}
    (hvp : v ∈ p.verts) (hvq : v ∈ q.verts) : p = q := by
  by_contra hne
  haveI : Std.Symm (fun a b : HPath k => Disjoint a.vertsFinset b.vertsFinset) :=
    ⟨fun a b h => h.symm⟩
  have hdisj := hpair.forall hp hq hne
  have h1 : v ∈ p.vertsFinset := HPath.mem_vertsFinset.mpr hvp
  have h2 : v ∈ q.vertsFinset := HPath.mem_vertsFinset.mpr hvq
  exact absurd (Finset.mem_inter.mpr ⟨h1, h2⟩)
    (by rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]; exact Finset.notMem_empty v)

/-! ## The edge classification (the `⊆` direction) -/

/-- If the target of a `P`-edge is a head (a component first-vertex), then its source is a
non-last head, i.e. lies in `headSet`.  (In the walk, the predecessor of a head is the previous
head.) -/
theorem head_pred_mem_headSet {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {e : Vtx k × Vtx k}
    (he : e ∈ (unwindP ps hps hnd).edges) (hb : e.2 ∈ ps.map HPath.first) :
    e.1 ∈ headSet ps := by
  set P := unwindP ps hps hnd with hP
  set heads := ps.map HPath.first with hh
  set tails := (ps.reverse.map (fun p => p.verts.drop 1)).flatten with htl
  have hLeq : unwindVerts ps = heads ++ tails := rfl
  have he1mem : e.1 ∈ unwindVerts ps := by
    have := ProofsSpine.mem_edges_iff.mp he
    exact (List.of_mem_zip this).1
  have hidx_b : (unwindVerts ps).idxOf e.2 = heads.idxOf e.2 := by
    rw [hLeq, List.idxOf_append_of_mem hb]
  have hsucc : (unwindVerts ps).idxOf e.2 = (unwindVerts ps).idxOf e.1 + 1 :=
    ProofsStructure.edge_pos_succ he
  set t := heads.idxOf e.2 with ht
  have ht_lt : t < heads.length := List.idxOf_lt_length_of_mem hb
  have hidx_e1 : (unwindVerts ps).idxOf e.1 = t - 1 := by omega
  -- `e.1 ∈ heads`
  have he1_head : e.1 ∈ heads := by
    rcases List.mem_append.mp (hLeq ▸ he1mem) with h | h
    · exact h
    · exfalso
      have hnh : e.1 ∉ heads := tail_not_mem_heads hnd (htl ▸ h)
      have hval : (unwindVerts ps).idxOf e.1 = heads.length + tails.idxOf e.1 := by
        rw [hLeq, List.idxOf_append_of_notMem hnh]
      omega
  have hheads_idx : heads.idxOf e.1 = t - 1 := by
    have : (unwindVerts ps).idxOf e.1 = heads.idxOf e.1 := by
      rw [hLeq, List.idxOf_append_of_mem he1_head]
    omega
  have he1_dl : e.1 ∈ heads.dropLast :=
    (List.mem_dropLast_iff_idxOf_lt he1_head).mpr (by rw [hheads_idx]; omega)
  rw [headSet, List.mem_toFinset, hh, ← List.map_dropLast] at *
  exact he1_dl

/-- **The edge classification.**  Every edge of the unwound path `P` is one of:
(1) a surviving component edge (`∈ X`); (2) a head-chain edge (source in `headSet`); or
(3) a back-link (its target is `σv` for some `v ∈ headSet`, so it doubles that vertex). -/
theorem edge_classify {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges)
    {e : Vtx k × Vtx k} (he : e ∈ (unwindP ps hps hnd).edges) :
    e ∈ X ∨ e.1 ∈ headSet ps ∨ ∃ v ∈ headSet ps, sigma v = e.2 := by
  set P := unwindP ps hps hnd with hP
  have hb_mem : e.2 ∈ unwindVerts ps := by
    have hz := ProofsSpine.mem_edges_iff.mp he
    have h2 : e.2 ∈ P.verts := List.mem_of_mem_tail (List.of_mem_zip hz).2
    exact h2
  obtain ⟨pb, hpb, hbpb⟩ := mem_unwindVerts.mp hb_mem
  have hpbSE := hSE pb hpb
  set m := pb.pos e.2 with hm
  have hmlt : m < pb.numVerts := ProofsExitless.pos_lt pb hbpb
  have hbvm : pb.vert m = e.2 := ProofsExitless.vert_pos pb hbpb
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- m = 0: target is a component first-vertex → head-chain, source in headSet
    right; left
    have hbf : e.2 = pb.first := by rw [← hbvm, hm0, pb.vert_zero]
    exact head_pred_mem_headSet hps hnd he (List.mem_map.mpr ⟨pb, hpb, hbf.symm⟩)
  · -- m ≥ 1: consider the component edge (pb[m-1], pb[m])
    have hcons : (pb.vert (m - 1), pb.vert m) ∈ pb.edges := by
      have h := ProofsStructure.vert_consec_mem_edges (p := pb) (i := m - 1) (by omega)
      rwa [show m - 1 + 1 = m from by omega] at h
    by_cases hcP : (pb.vert (m - 1), pb.vert m) ∈ P.edges
    · -- component edge survives → e equals it (in-degree ≤ 1) → e ∈ X
      left
      have h1 : e ∈ intoV P.edges e.2 := by
        rw [intoV, mem_into, Finset.mem_singleton]; exact ⟨he, rfl⟩
      have h2 : (pb.vert (m - 1), pb.vert m) ∈ intoV P.edges e.2 := by
        rw [intoV, mem_into, Finset.mem_singleton]; exact ⟨hcP, hbvm⟩
      have heq : e = (pb.vert (m - 1), pb.vert m) :=
        Finset.card_le_one.mp (ProofsSpine.path_into_le_one P e.2) e h1 _ h2
      rw [heq]; exact (hXdef _).mpr ⟨pb, hpb, hcons⟩
    · -- component edge detoured → it is a non-last first-edge → back-link, option (3)
      have hm_eq1 : m = 1 := by
        by_contra hmne
        apply hcP
        have h := interior_edge_mem hps hnd hpb (show 1 ≤ m - 1 by omega)
          (show (m - 1) + 1 < pb.numVerts by omega)
        rwa [show m - 1 + 1 = m from by omega] at h
      have hpdl : pb ∈ ps.dropLast := by
        by_contra hpdl'
        apply hcP
        have hsplit := List.dropLast_append_getLast hps
        have hmem2 : pb ∈ ps.dropLast ++ [ps.getLast hps] := hsplit.symm ▸ hpb
        rw [List.mem_append, List.mem_singleton] at hmem2
        have hpeq : pb = ps.getLast hps := hmem2.resolve_left hpdl'
        have h11 : (1 : ℕ) - 1 = 0 := rfl
        rw [hm_eq1, h11, pb.vert_zero, vert1_eq_sigma_first hpbSE hk, hpeq]
        exact junction_edge_mem hps hnd hSE hk
      right; right
      refine ⟨pb.first, mem_headSet.mpr ⟨pb, hpdl, rfl⟩, ?_⟩
      have hb1 : pb.vert 1 = e.2 := by rw [← hm_eq1]; exact hbvm
      rw [vert1_eq_sigma_first hpbSE hk] at hb1
      exact hb1

/-! ## Assembling `hdec` and the disjointnesses -/

/-- **The edge decomposition `hdec`.**  `E(P) = (X ∖ FE) ∪ E1removed ∪ E2removed`. -/
theorem edges_decomp {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    (unwindP ps hps hnd).edges =
      (X \ addedEdges (headSet ps)) ∪ E1removed (unwindP ps hps hnd) (headSet ps) ∪
        E2removed (unwindP ps hps hnd) (headSet ps) := by
  set P := unwindP ps hps hnd with hP
  apply Finset.Subset.antisymm
  · -- `⊆`: classify each `P`-edge
    intro e heP
    rcases edge_classify hps hnd hSE hk hXdef heP with hX | hSrc | ⟨v, hvS, hσ⟩
    · -- `e ∈ X`, and `e ∉ FE` (a first-edge is never a `P`-edge)
      have heFE : e ∉ addedEdges (headSet ps) := by
        intro hFE
        obtain ⟨q, hq, rfl⟩ := mem_addedEdges_iff.mp hFE
        exact first_edge_not_mem_edges hps hnd hq (hSE q (List.dropLast_subset ps hq)) hk heP
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hX, heFE⟩))
    · -- source in `headSet` → `E1removed`
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (by rw [E1removed, Finset.mem_filter]; exact ⟨heP, hSrc⟩))
    · -- back-link: `σv = e.2`.  If source ∈ S use `E1removed`, else `e.2` is a double
      by_cases hsrc : e.1 ∈ headSet ps
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (by rw [E1removed, Finset.mem_filter]; exact ⟨heP, hsrc⟩))
      · have hd : e.2 ∈ doubles P (headSet ps) := by
          have : ((e.1, e.2) : Vtx k × Vtx k) ∈ P.edges := heP
          exact mem_doubles_of P (headSet ps) this hsrc hvS hσ
        exact Finset.mem_union_right _ (by rw [E2removed, Finset.mem_filter]; exact ⟨heP, hd⟩)
  · -- `⊇`: each piece is a subset of `E(P)`
    apply Finset.union_subset
    apply Finset.union_subset
    · exact sdiff_subset_edges hps hnd hSE hk hXdef
    · exact E1removed_subset _ _
    · exact E2removed_subset _ _

/-- `Disjoint (E1removed) X` — a head-chain edge is not a component edge. -/
theorem disjoint_E1_X {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    (hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset))
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    Disjoint (E1removed (unwindP ps hps hnd) (headSet ps)) X := by
  rw [Finset.disjoint_left]
  intro e he1 hX
  rw [E1removed, Finset.mem_filter] at he1
  obtain ⟨heP, hsrc⟩ := he1
  obtain ⟨q, hq, hqf⟩ := mem_headSet.mp hsrc
  have hqmem : q ∈ ps := List.dropLast_subset ps hq
  obtain ⟨p, hp, hep⟩ := (hXdef e).mp hX
  have hvp : e.1 ∈ p.verts := by
    have := ProofsSpine.mem_edges_iff.mp hep; exact (List.of_mem_zip this).1
  have hvq : e.1 ∈ q.verts := by rw [← hqf]; exact q.first_mem
  have hpq : p = q := comp_eq_of_shared hpair hp hqmem hvp hvq
  rw [hpq] at hep
  obtain ⟨heqc, -⟩ := edge_eq_consec hep
  have hp0 : q.pos e.1 = 0 := by rw [← hqf]; exact ProofsStructure.pos_first q
  rw [hp0, q.vert_zero, show q.vert (0 + 1) = q.vert 1 from rfl,
    vert1_eq_sigma_first (hSE q hqmem) hk] at heqc
  exact first_edge_not_mem_edges hps hnd hq (hSE q hqmem) hk (heqc ▸ heP)

/-- `Disjoint X (E2removed)` — a back-link is not a component edge. -/
theorem disjoint_X_E2 {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    (hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset))
    {X : Finset (Vtx k × Vtx k)} (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    Disjoint X (E2removed (unwindP ps hps hnd) (headSet ps)) := by
  rw [Finset.disjoint_left]
  intro e hX he2
  rw [E2removed, Finset.mem_filter] at he2
  obtain ⟨heP, hd⟩ := he2
  obtain ⟨v, hvS, hσ⟩ := mem_doubles_imp hd
  obtain ⟨q, hq, hqf⟩ := mem_headSet.mp hvS
  have hqmem : q ∈ ps := List.dropLast_subset ps hq
  have hq1lt : 1 < q.numVerts := one_lt_numVerts (hSE q hqmem) hk
  -- e.2 = σv = q.vert 1
  have hb1 : q.vert 1 = e.2 := by
    rw [vert1_eq_sigma_first (hSE q hqmem) hk, hqf, hσ]
  obtain ⟨p, hp, hep⟩ := (hXdef e).mp hX
  have hvp : e.2 ∈ p.verts := by
    have := ProofsSpine.mem_edges_iff.mp hep
    exact List.mem_of_mem_tail (List.of_mem_zip this).2
  have hvq : e.2 ∈ q.verts := by rw [← hb1]; exact ProofsExitless.vert_mem q hq1lt
  have hpq : p = q := comp_eq_of_shared hpair hp hqmem hvp hvq
  rw [hpq] at hep
  obtain ⟨heqc, hltc⟩ := edge_eq_consec hep
  -- e.2 = q.vert (pos e.1 + 1) = q.vert 1  ⟹ pos e.1 = 0
  have hsnd : e.2 = q.vert (q.pos e.1 + 1) := congrArg Prod.snd heqc
  have hposeq : q.pos e.1 + 1 = 1 := by
    have h1 := ProofsExitless.pos_vert q hltc
    have h2 := ProofsExitless.pos_vert q hq1lt
    have hvv : q.vert (q.pos e.1 + 1) = q.vert 1 := by rw [← hsnd, ← hb1]
    rw [hvv] at h1
    rw [← h1, h2]
  have hp0 : q.pos e.1 = 0 := by omega
  rw [hp0, q.vert_zero, show q.vert (0 + 1) = q.vert 1 from rfl,
    vert1_eq_sigma_first (hSE q hqmem) hk] at heqc
  exact first_edge_not_mem_edges hps hnd hq (hSE q hqmem) hk (heqc ▸ heP)

/-- `Disjoint (E1removed) (E2removed)` — a removed head-chain edge cannot be a removed
back-link (the target of a back-link keeps its unique `P`-in-edge, which is *not* the
`E1removed` edge). -/
theorem disjoint_E1_E2 {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) :
    Disjoint (E1removed (unwindP ps hps hnd) (headSet ps))
      (E2removed (unwindP ps hps hnd) (headSet ps)) := by
  set P := unwindP ps hps hnd with hP
  set S := headSet ps with hS
  rw [Finset.disjoint_left]
  intro e he1 he2
  rw [E1removed, Finset.mem_filter] at he1
  rw [E2removed, Finset.mem_filter] at he2
  obtain ⟨heP, hsrc1⟩ := he1
  obtain ⟨-, hd⟩ := he2
  have hd2 : (intoV (Xstep1 P S) e.2).card = 2 := by
    rw [doubles, Finset.mem_filter] at hd; exact hd.2
  have hdecomp : intoV (Xstep1 P S) e.2 =
      intoV (P.edges \ E1removed P S) e.2 ∪ intoV (addedEdges S) e.2 := by
    unfold Xstep1; exact ProofsSpine.intoV_union _ _ e.2
  have hBle : (intoV (addedEdges S) e.2).card ≤ 1 := ProofsSpine.intoV_addedEdges_le_one S e.2
  have hApos : 1 ≤ (intoV (P.edges \ E1removed P S) e.2).card := by
    have hunion : (intoV (Xstep1 P S) e.2).card ≤
        (intoV (P.edges \ E1removed P S) e.2).card + (intoV (addedEdges S) e.2).card := by
      rw [hdecomp]; exact Finset.card_union_le _ _
    omega
  obtain ⟨e', he'⟩ := Finset.card_pos.mp hApos
  rw [intoV, mem_into, Finset.mem_singleton] at he'
  obtain ⟨he'mem, he'2⟩ := he'
  have he'P : e' ∈ P.edges := (Finset.mem_sdiff.mp he'mem).1
  -- e and e' are both the unique P-in-edge to e.2, hence equal
  have hee' : e = e' := by
    refine Finset.card_le_one.mp (ProofsSpine.path_into_le_one P e.2) e ?_ e' ?_
    · rw [intoV, mem_into, Finset.mem_singleton]; exact ⟨heP, rfl⟩
    · rw [intoV, mem_into, Finset.mem_singleton]; exact ⟨he'P, he'2⟩
  -- but e' ∉ E1removed while e ∈ E1removed
  have he'notE1 : e' ∉ E1removed P S := (Finset.mem_sdiff.mp he'mem).2
  exact he'notE1 (hee' ▸ (by rw [E1removed, Finset.mem_filter]; exact ⟨heP, hsrc1⟩))

end Hunter.ProofsUnwind3

/-! ## Delivered target — the unwinding with the edge-decomposition discharged -/

namespace Hunter.Proved

open Hunter.ProofsUnwind
open Hunter.ProofsUnwind2
open Hunter.ProofsUnwind3
open scoped Classical

variable {k : ℕ}

/-- **`prp_Xk_se_sufficiency`, general case — the `hdec` residual DISCHARGED.**

Compared to `prp_Xk_se_sufficiency_unwind2`, all five edge-structure hypotheses (the edge
decomposition `hdec` and the three disjointnesses, plus `addedEdges ⊆ X`) are now *proved*
outright from the concrete unwinding, given only:

* `hps` / `hnd` / `hcover` — the vertex-list well-formedness (as in `..._unwind`);
* `hSE` — every component is strongly exitless;
* `hpair` — the components are pairwise vertex-disjoint (a well-formedness fact, equivalent to
  `hnd` but taken directly — it is exactly what `Comps(X)` supplies);
* `hXdef` — `X` is the union of the component edge-sets `⋃ᵢ E(pᵢ)` (which holds for the
  `prp_Xk_se_sufficiency` `X`, whose edges partition into its path-components).

This is the paper's `ADD DIAGRAM` step, computed from the explicit list adjacency
(`edge_classify`) and the `doubles` in-degree-2 bookkeeping (`mem_doubles_of`). -/
theorem prp_Xk_se_sufficiency_unwind3 {X : Finset (Vtx k × Vtx k)}
    {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts)
    (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    (hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset))
    (hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges) :
    X ∈ Xk k :=
  prp_Xk_se_sufficiency_unwind2 hps hnd hcover hSE hk
    (edges_decomp hps hnd hSE hk hXdef)
    (addedEdges_subset_X hSE hk hXdef)
    (disjoint_E1_X hps hnd hSE hk hpair hXdef)
    (disjoint_E1_E2 hps hnd)
    (disjoint_X_E2 hps hnd hSE hk hpair hXdef)

end Hunter.Proved

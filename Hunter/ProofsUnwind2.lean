/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsUnwind

/-!
# Discharging the unwinding residual `hFPX : F (unwindP ps) = X` (Hunter §5)

This file continues `Hunter/ProofsUnwind.lean`.  Its goal is to prove the paper's
"ADD DIAGRAM" step — that the unwinding construction `P = P(p₁,…,pₙ)` satisfies
`F(P) = X = ⋃ᵢ E(pᵢ)` — thereby removing the `hFPX` hypothesis from
`prp_Xk_se_sufficiency_unwind`.

The argument has two independent halves:

* **Edge accounting (`fPS_eq_of_edges`).**  A purely set-theoretic Step-1/Step-2 calculation:
  if `E(P)` decomposes as `(X ∖ FE) ∪ HC ∪ BL` with `FE = addedEdges S`, `HC = E₁`,
  `BL = E₂` and the natural disjointnesses, then `f(P,S) = X`.  This is the `E1removed` /
  `addedEdges` / `doubles` / `E2removed` bookkeeping the handoff flagged, and it is proved
  outright here.

* **Structure of the construction.**  Computing `S(P)`, `E(P)`, the head-chain `HC`, the
  back-links `BL`, and the doubles for the concrete `unwindVerts` list.  These are the
  positional facts.

See `PROGRESS-unwind2.md`.
-/

namespace Hunter.ProofsUnwind2

open List
open Hunter.ProofsUnwind
open scoped Classical

variable {k : ℕ}

/-! ## The abstract Step-1/Step-2 edge accounting

This is the `f(P,S) = X` calculation, isolated from any positional reasoning: it takes the
decomposition of `E(P)` into `X ∖ FE`, the removed head-chain `HC = E₁`, and the removed
back-links `BL = E₂` (with `FE = addedEdges S` the restored 1-edges), and does the
Step-1/Step-2 algebra.  -/

/-- **Edge accounting.**  If `E(P) = (X ∖ addedEdges S) ∪ E₁ ∪ E₂` with the natural
disjointnesses and `addedEdges S ⊆ X`, then `f(P,S) = X`.

Concretely, in the unwinding: `addedEdges S = FE` = the restored first-edges
`pᵢ[1]→pᵢ[2]`, `E₁ = HC` = the head-chain `pᵢ[1]→p_{i+1}[1]`, `E₂ = BL` = the back-links
`p_{i+1}[last]→pᵢ[2]`.  Step 1 turns `E(P)` into `(X ∖ FE) ∪ BL ∪ FE = X ∪ BL`; Step 2
removes `BL`, leaving `X`. -/
theorem fPS_eq_of_edges (P : HPath k) (S : Finset (Vtx k)) (X : Finset (Vtx k × Vtx k))
    (hEdges : P.edges = (X \ addedEdges S) ∪ E1removed P S ∪ E2removed P S)
    (hFEsub : addedEdges S ⊆ X)
    (hHCX : Disjoint (E1removed P S) X)
    (hHCBL : Disjoint (E1removed P S) (E2removed P S))
    (hXBL : Disjoint X (E2removed P S)) :
    fPS P S = X := by
  set FE := addedEdges S with hFE
  set HC := E1removed P S with hHC
  set BL := E2removed P S with hBL
  -- Disjointnesses of `HC` with the pieces of `X ∖ FE`.
  have hHC_XFE : Disjoint (X \ FE) HC := (hHCX.mono_right Finset.sdiff_subset).symm
  -- Step 1: `(E(P) ∖ HC) ∪ FE = X ∪ BL`.
  have hstep1 : (P.edges \ HC) ∪ FE = X ∪ BL := by
    rw [hEdges]
    -- `((X∖FE) ∪ HC ∪ BL) ∖ HC = (X∖FE) ∪ BL`
    have hrm : ((X \ FE) ∪ HC ∪ BL) \ HC = (X \ FE) ∪ BL := by
      rw [Finset.union_sdiff_distrib, Finset.union_sdiff_distrib,
        Finset.sdiff_eq_self_of_disjoint hHC_XFE, Finset.sdiff_self,
        Finset.sdiff_eq_self_of_disjoint hHCBL.symm, Finset.union_empty]
    rw [hrm]
    -- `((X∖FE) ∪ BL) ∪ FE = X ∪ BL`
    rw [Finset.union_right_comm, Finset.sdiff_union_of_subset hFEsub]
  rw [fPS, Xstep1, ← hFE, ← hHC, ← hBL, hstep1]
  -- Step 2: `(X ∪ BL) ∖ BL = X`.
  rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hXBL]

/-! ## Ordering inside a `flatten` and the KEY ORDER lemma

The positional heart: in the constructed path `P = unwindP ps`, the `P`-order *restricted to
a single component* `pᵢ` agrees with `pᵢ`'s own order.  This is because `pᵢ.first` sits in
the head block (before all tails) and the rest of `pᵢ` sits, in forward order, in one
contiguous block of the tail flatten. -/

/-- Within a duplicate-free `flatten`, elements of one block are ordered by their order in
that block. -/
theorem idxOf_flatten_lt {α : Type*} [BEq α] [LawfulBEq α] {blocks : List (List α)}
    (hnd : blocks.flatten.Nodup) {D : List α} (hD : D ∈ blocks) {a b : α}
    (ha : a ∈ D) (hb : b ∈ D) (hab : D.idxOf a < D.idxOf b) :
    blocks.flatten.idxOf a < blocks.flatten.idxOf b := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hD
  have hform : (pre ++ D :: post).flatten = pre.flatten ++ (D ++ post.flatten) := by
    rw [List.flatten_append, List.flatten_cons]
  rw [hform] at hnd ⊢
  have hdisj : List.Disjoint pre.flatten (D ++ post.flatten) :=
    List.disjoint_of_nodup_append hnd
  have ha_pre : a ∉ pre.flatten := fun h => (List.disjoint_left.mp hdisj h) (List.mem_append_left _ ha)
  have hb_pre : b ∉ pre.flatten := fun h => (List.disjoint_left.mp hdisj h) (List.mem_append_left _ hb)
  rw [List.idxOf_append_of_notMem ha_pre, List.idxOf_append_of_notMem hb_pre,
    List.idxOf_append_of_mem ha, List.idxOf_append_of_mem hb]
  omega

/-- `unwindVerts ps = heads ++ tails` with `heads = ps.map first`, `tails` the reversed
remainder flatten. -/
theorem unwindVerts_eq (ps : List (HPath k)) :
    unwindVerts ps = ps.map HPath.first ++ (ps.reverse.map (fun p => p.verts.drop 1)).flatten :=
  rfl

/-- A tail vertex (one lying in some `p.verts.drop 1`) is not a head. -/
theorem tail_not_mem_heads {ps : List (HPath k)} (hnd : (unwindVerts ps).Nodup)
    {v : Vtx k} (hv : v ∈ ((ps.reverse.map (fun p => p.verts.drop 1)).flatten)) :
    v ∉ ps.map HPath.first :=
  fun h => (List.disjoint_left.mp
    ((List.disjoint_of_nodup_append hnd).symm) hv) h

/-- **KEY ORDER LEMMA.**  In `P = unwindP ps`, the position order restricted to a single
component `p ∈ ps` agrees with `p`'s own order: `p.pos a < p.pos b ⟹ P.pos a < P.pos b`.

(Stated on the raw `idxOf`, since `(unwindP ps _ _).pos v = (unwindVerts ps).idxOf v`
definitionally.) -/
theorem idxOf_lt_of_comp_pos_lt {ps : List (HPath k)} (hnd : (unwindVerts ps).Nodup)
    {p : HPath k} (hp : p ∈ ps) {a b : Vtx k}
    (ha : a ∈ p.verts) (hb : b ∈ p.verts) (hab : p.pos a < p.pos b) :
    (unwindVerts ps).idxOf a < (unwindVerts ps).idxOf b := by
  set heads := ps.map HPath.first with hheads
  set tails := (ps.reverse.map (fun p => p.verts.drop 1)).flatten with htails
  have hLeq : unwindVerts ps = heads ++ tails := rfl
  rw [hLeq]
  -- `p.verts = c :: t` with `first = c`, `tail = t`, `drop 1 = t`.
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil p.ne
  have hfirst : p.first = c := ProofsSpine.first_eq hct
  have hdrop : p.verts.drop 1 = t := by rw [hct, List.drop_one, List.tail_cons]
  -- position vs `idxOf` in `c :: t`
  have hposa : p.pos a = (c :: t).idxOf a := by rw [HPath.pos, hct]
  have hposb : p.pos b = (c :: t).idxOf b := by rw [HPath.pos, hct]
  by_cases hac : a = c
  · -- `a = first`: a is a head, b is a tail
    have hbne : b ≠ c := by
      intro hbc; rw [hposa, hposb, hac, hbc] at hab; omega
    have haheads : a ∈ heads := by
      rw [hheads]; exact List.mem_map.mpr ⟨p, hp, by rw [hfirst, hac]⟩
    have hbt : b ∈ t := (List.mem_cons.mp (hct ▸ hb)).resolve_left hbne
    have hbtails : b ∈ tails := by
      rw [htails]; exact List.mem_flatten.mpr ⟨t, List.mem_map.mpr
        ⟨p, List.mem_reverse.mpr hp, hdrop⟩, hbt⟩
    have hbnh : b ∉ heads := tail_not_mem_heads hnd (htails ▸ hbtails)
    rw [List.idxOf_append_of_mem haheads, List.idxOf_append_of_notMem hbnh]
    have h1 : heads.idxOf a < heads.length := List.idxOf_lt_length_of_mem haheads
    omega
  · -- `a ≠ first`: both a, b are tails
    have hbne : b ≠ c := by
      intro hbc
      have : (c :: t).idxOf b = 0 := by rw [hbc]; exact List.idxOf_cons_self
      rw [hposa, hposb, this] at hab; omega
    have hat : a ∈ t := (List.mem_cons.mp (hct ▸ ha)).resolve_left hac
    have hbt : b ∈ t := (List.mem_cons.mp (hct ▸ hb)).resolve_left hbne
    have hatails : a ∈ tails := by
      rw [htails]; exact List.mem_flatten.mpr ⟨t, List.mem_map.mpr
        ⟨p, List.mem_reverse.mpr hp, hdrop⟩, hat⟩
    have hbtails : b ∈ tails := by
      rw [htails]; exact List.mem_flatten.mpr ⟨t, List.mem_map.mpr
        ⟨p, List.mem_reverse.mpr hp, hdrop⟩, hbt⟩
    have hanh : a ∉ heads := tail_not_mem_heads hnd (htails ▸ hatails)
    have hbnh : b ∉ heads := tail_not_mem_heads hnd (htails ▸ hbtails)
    rw [List.idxOf_append_of_notMem hanh, List.idxOf_append_of_notMem hbnh]
    -- reduce to ordering inside `tails`, then inside the block `t`
    have htnd : tails.Nodup := (List.nodup_append.mp (by rw [← hLeq]; exact hnd)).2.1
    have hDmem : t ∈ ps.reverse.map (fun p => p.verts.drop 1) :=
      List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, hdrop⟩
    have hidxlt : t.idxOf a < t.idxOf b := by
      have hia : (c :: t).idxOf a = (t.idxOf a).succ := List.idxOf_cons_ne _ (fun h => hac h.symm)
      have hib : (c :: t).idxOf b = (t.idxOf b).succ := List.idxOf_cons_ne _ (fun h => hbne h.symm)
      rw [hposa, hia, hposb, hib] at hab
      omega
    have hkey := idxOf_flatten_lt (htails ▸ htnd) hDmem hat hbt hidxlt
    rw [htails]; omega

/-! ## `firstInCycle`, `C₀`, `C₋₁` for the unwinding, from KEY ORDER

`(unwindP ps _ _).pos v = (unwindVerts ps).idxOf v` definitionally. -/

theorem unwindP_pos {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (v : Vtx k) :
    (unwindP ps hps hnd).pos v = (unwindVerts ps).idxOf v := rfl

/-- **Lifting `firstInCycle`.**  A `p`-first-in-cycle vertex (of a strongly exitless
component `p ∈ ps`) is `P`-first-in-cycle, since its whole 1-cycle lies inside `p` and the
`P`-order restricted to `p` is `p`'s order. -/
theorem firstInCycle_lift {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp : p ∈ ps)
    (hpSE : p.StronglyExitless) {w : Vtx k} (hw : w ∈ p.verts)
    (hfic : firstInCycle p w) :
    firstInCycle (unwindP ps hps hnd) w := by
  intro u hrc
  have hUC := Proved.clm_1cyclesubset hpSE
  have hucyc : u ∈ cyc w := ProofsExitless.mem_cyc.mpr hrc
  have huv : u ∈ p.verts := HPath.mem_vertsFinset.mp (hUC w hw hucyc)
  have hple : p.pos w ≤ p.pos u := hfic u hrc
  show (unwindVerts ps).idxOf w ≤ (unwindVerts ps).idxOf u
  rcases Nat.lt_or_ge (p.pos w) (p.pos u) with hlt | hge
  · exact le_of_lt (idxOf_lt_of_comp_pos_lt hnd hp hw huv hlt)
  · have heq : p.pos w = p.pos u := le_antisymm hple hge
    have hwu : w = u := by
      have h1 := ProofsExitless.vert_pos p hw
      have h2 := ProofsExitless.vert_pos p huv
      rw [← h1, ← h2, heq]
    rw [hwu]

/-- `pᵢ[1] ∈ C₀(P)`: the first vertex of each component is first-in-cycle. -/
theorem first_mem_C0 {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp : p ∈ ps)
    (hpSE : p.StronglyExitless) (hk : 1 ≤ k) :
    p.first ∈ C0 (unwindP ps hps hnd) := by
  rw [C0, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk hpSE
  have hkle : 0 + k ≤ p.numVerts := by
    have := Nat.le_of_dvd p.numVerts_pos hdvd; omega
  have hfic0 : firstInCycle p (p.vert 0) :=
    firstInCycle_block_start hk hpSE.1 (dvd_zero k) hkle
  rw [p.vert_zero] at hfic0
  exact firstInCycle_lift hps hnd hp hpSE p.first_mem hfic0

/-- `pᵢ[1] ∉ C₋₁(P)`: since `σ(pᵢ[1]) = pᵢ[2]` is *not* first-in-cycle (`pᵢ[1]` is, and comes
earlier).  Needs `2 ≤ k`. -/
theorem first_not_mem_Cm1 {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp : p ∈ ps)
    (hpSE : p.StronglyExitless) (hk : 2 ≤ k) :
    p.first ∉ Cm1 (unwindP ps hps hnd) := by
  intro hmem
  rw [Cm1, Finset.mem_filter] at hmem
  have hsC0 := hmem.2
  have hk1 : 1 ≤ k := by omega
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk1 hpSE
  have hkle : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
  have h1lt : 1 < p.numVerts := by omega
  have hkndvd : ¬ k ∣ (0 + 1) := by
    intro h; have := Nat.le_of_dvd (show 0 < 0 + 1 by omega) h; omega
  have hv1 : p.vert 1 = sigma p.first := by
    have h := ProofsExitless.vert_succ hk1 hpSE.1 (i := 0) (show 0 + 1 < p.numVerts by omega) hkndvd
    rwa [p.vert_zero] at h
  have hficP : firstInCycle (unwindP ps hps hnd) (sigma p.first) := by
    rw [C0, Finset.mem_filter] at hsC0; exact hsC0.2
  have hrc : rotClass (p.first).1 = rotClass (sigma p.first).1 :=
    (ProofsStructure.rotClass_sigma p.first).symm
  have hle : (unwindVerts ps).idxOf (sigma p.first) ≤ (unwindVerts ps).idxOf p.first :=
    hficP p.first hrc
  have hposw : p.pos p.first = 0 := ProofsStructure.pos_first p
  have hv1mem : p.vert 1 ∈ p.verts := ProofsExitless.vert_mem p h1lt
  have hposv1 : p.pos (p.vert 1) = 1 := ProofsExitless.pos_vert p h1lt
  have hlt : p.pos p.first < p.pos (p.vert 1) := by rw [hposw, hposv1]; omega
  have hkey := idxOf_lt_of_comp_pos_lt hnd hp p.first_mem hv1mem hlt
  rw [hv1] at hkey
  omega

/-- Any *non-first* block start of a component is `P`-first-in-cycle (the general form used
for the `C₋₁` analysis of `Sset`). -/
theorem blockStart_mem_C0 {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp : p ∈ ps)
    (hpSE : p.StronglyExitless) (hk : 1 ≤ k) {B : ℕ} (hdvd : k ∣ B)
    (hB : B + k ≤ p.numVerts) :
    p.vert B ∈ C0 (unwindP ps hps hnd) := by
  rw [C0, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hBlt : B < p.numVerts := by omega
  exact firstInCycle_lift hps hnd hp hpSE (ProofsExitless.vert_mem p hBlt)
    (firstInCycle_block_start hk hpSE.1 hdvd hB)

/-! ## Edge-adjacency of the explicit list

The last ingredient: which ordered pairs are consecutive in `heads ++ tails`.  `(NEG)` the
detoured first-edges are absent; `(POS)` every other component-edge survives. -/

/-- A vertex at component-index `≥ 1` lies in that component's tail `drop 1`. -/
theorem vert_mem_drop1 {p : HPath k} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < p.numVerts) :
    p.vert j ∈ p.verts.drop 1 := by
  rw [List.drop_one]
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil p.ne
  have hne_first : p.vert j ≠ p.first := by
    intro h
    have h0 := ProofsExitless.pos_vert p hj
    rw [h, ProofsStructure.pos_first] at h0
    omega
  have hmem : p.vert j ∈ p.verts := ProofsExitless.vert_mem p hj
  rw [hct, List.tail_cons]
  rw [hct] at hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact absurd (h.trans (ProofsSpine.first_eq hct).symm) hne_first
  · exact h

/-- Membership in the tail flatten from membership in one component's `drop 1`. -/
theorem mem_tails {ps : List (HPath k)} {p : HPath k} (hp : p ∈ ps) {v : Vtx k}
    (hv : v ∈ p.verts.drop 1) :
    v ∈ (ps.reverse.map (fun p => p.verts.drop 1)).flatten :=
  List.mem_flatten.mpr ⟨p.verts.drop 1, List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩, hv⟩

/-- **(NEG).**  For a non-last component `p ∈ ps.dropLast`, its first-edge `pᵢ[1]→σ(pᵢ[1])`
is detoured away and is *not* an edge of `P`. -/
theorem first_edge_not_mem_edges {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp_dl : p ∈ ps.dropLast)
    (hpSE : p.StronglyExitless) (hk : 2 ≤ k) :
    (p.first, sigma p.first) ∉ (unwindP ps hps hnd).edges := by
  intro hedge
  have hp : p ∈ ps := List.dropLast_subset ps hp_dl
  have hk1 : 1 ≤ k := by omega
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk1 hpSE
  have hkle : k ≤ p.numVerts := Nat.le_of_dvd p.numVerts_pos hdvd
  have h1lt : 1 < p.numVerts := by omega
  have hkndvd : ¬ k ∣ (0 + 1) := by
    intro h; have := Nat.le_of_dvd (show 0 < 0 + 1 by omega) h; omega
  have hv1 : p.vert 1 = sigma p.first := by
    have h := ProofsExitless.vert_succ hk1 hpSE.1 (i := 0) (show 0 + 1 < p.numVerts by omega) hkndvd
    rwa [p.vert_zero] at h
  set L := unwindVerts ps with hL
  set heads := ps.map HPath.first with hh
  have hLeq : L = heads ++ (ps.reverse.map (fun p => p.verts.drop 1)).flatten := rfl
  have hfhead : p.first ∈ heads := List.mem_map.mpr ⟨p, hp, rfl⟩
  have hposfirst : L.idxOf p.first < heads.length - 1 := by
    rw [hLeq, List.idxOf_append_of_mem hfhead]
    have hdl : p.first ∈ heads.dropLast := by
      rw [hh, ← List.map_dropLast]; exact List.mem_map.mpr ⟨p, hp_dl, rfl⟩
    exact (List.mem_dropLast_iff_idxOf_lt hfhead).mp hdl
  have hv1tail : sigma p.first ∈ (ps.reverse.map (fun p => p.verts.drop 1)).flatten := by
    rw [← hv1]; exact mem_tails hp (vert_mem_drop1 (by omega) h1lt)
  have hv1nh : sigma p.first ∉ heads := tail_not_mem_heads hnd hv1tail
  have hpossig : heads.length ≤ L.idxOf (sigma p.first) := by
    rw [hLeq, List.idxOf_append_of_notMem hv1nh]; omega
  have hsucc := ProofsStructure.edge_pos_succ hedge
  have e1 : (unwindP ps hps hnd).pos (sigma p.first) = L.idxOf (sigma p.first) := rfl
  have e2 : (unwindP ps hps hnd).pos p.first = L.idxOf p.first := rfl
  rw [e1, e2] at hsucc
  omega

/-- Within a nodup `flatten`, a within-block successor is a global successor. -/
theorem idxOf_flatten_succ {α : Type*} [BEq α] [LawfulBEq α] {blocks : List (List α)}
    (hnd : blocks.flatten.Nodup) {D : List α} (hD : D ∈ blocks) {a b : α}
    (ha : a ∈ D) (hb : b ∈ D) (hab : D.idxOf b = D.idxOf a + 1) :
    blocks.flatten.idxOf b = blocks.flatten.idxOf a + 1 := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hD
  have hform : (pre ++ D :: post).flatten = pre.flatten ++ (D ++ post.flatten) := by
    rw [List.flatten_append, List.flatten_cons]
  rw [hform] at hnd ⊢
  have hdisj := List.disjoint_of_nodup_append hnd
  have ha_pre : a ∉ pre.flatten := fun h => (List.disjoint_left.mp hdisj h) (List.mem_append_left _ ha)
  have hb_pre : b ∉ pre.flatten := fun h => (List.disjoint_left.mp hdisj h) (List.mem_append_left _ hb)
  rw [List.idxOf_append_of_notMem ha_pre, List.idxOf_append_of_notMem hb_pre,
    List.idxOf_append_of_mem ha, List.idxOf_append_of_mem hb]
  omega

/-- `idxOf` of `p[j]` inside `p.verts.drop 1` is `j - 1` (for `j ≥ 1`). -/
theorem idxOf_drop1_vert {p : HPath k} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < p.numVerts) :
    (p.verts.drop 1).idxOf (p.vert j) = j - 1 := by
  have hnd1 : (p.verts.drop 1).Nodup := p.nodup.sublist (List.drop_sublist _ _)
  have hnv : p.numVerts = p.verts.length := rfl
  have hlen : j - 1 < (p.verts.drop 1).length := by rw [List.length_drop]; omega
  have hget : (p.verts.drop 1)[j - 1]'hlen = p.vert j := by
    rw [List.getElem_drop, ProofsExitless.vert_getElem p hj]
    exact ProofsStructure.getElem_eq_of_index_eq (by omega) _ _
  rw [← hget]; exact hnd1.idxOf_getElem (j - 1) hlen

/-- **(POS, interior).**  Every component-edge `p[j]→p[j+1]` with `j ≥ 1` survives in `P`
(it lies inside the contiguous tail block `p.verts.drop 1`). -/
theorem interior_edge_mem {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) {p : HPath k} (hp : p ∈ ps) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j + 1 < p.numVerts) :
    (p.vert j, p.vert (j + 1)) ∈ (unwindP ps hps hnd).edges := by
  have hjlt : j < p.numVerts := by omega
  set L := unwindVerts ps with hL
  set tails := (ps.reverse.map (fun p => p.verts.drop 1)).flatten with htl
  have hLeq : L = ps.map HPath.first ++ tails := rfl
  have haD : p.vert j ∈ p.verts.drop 1 := vert_mem_drop1 hj1 hjlt
  have hbD : p.vert (j + 1) ∈ p.verts.drop 1 := vert_mem_drop1 (by omega) hj
  have hida : (p.verts.drop 1).idxOf (p.vert j) = j - 1 := idxOf_drop1_vert hj1 hjlt
  have hidb : (p.verts.drop 1).idxOf (p.vert (j + 1)) = j := by
    have h := idxOf_drop1_vert (p := p) (j := j + 1) (by omega) hj
    simpa using h
  have htnd : tails.Nodup := (List.nodup_append.mp (by rw [← hLeq]; exact hnd)).2.1
  have hDmem : p.verts.drop 1 ∈ ps.reverse.map (fun p => p.verts.drop 1) :=
    List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
  have hsucc_t : tails.idxOf (p.vert (j + 1)) = tails.idxOf (p.vert j) + 1 :=
    idxOf_flatten_succ (htl ▸ htnd) hDmem haD hbD (by rw [hida, hidb]; omega)
  have haT : p.vert j ∈ tails := htl ▸ mem_tails hp haD
  have hbT : p.vert (j + 1) ∈ tails := htl ▸ mem_tails hp hbD
  have hanh : p.vert j ∉ ps.map HPath.first := tail_not_mem_heads hnd (htl ▸ haT)
  have hbnh : p.vert (j + 1) ∉ ps.map HPath.first := tail_not_mem_heads hnd (htl ▸ hbT)
  have hsucc_L : L.idxOf (p.vert (j + 1)) = L.idxOf (p.vert j) + 1 := by
    rw [hLeq, List.idxOf_append_of_notMem hanh, List.idxOf_append_of_notMem hbnh]; omega
  set P := unwindP ps hps hnd with hP
  have hmemLa : p.vert j ∈ P.verts :=
    mem_unwindVerts.mpr ⟨p, hp, ProofsExitless.vert_mem p hjlt⟩
  have hmemLb : p.vert (j + 1) ∈ P.verts :=
    mem_unwindVerts.mpr ⟨p, hp, ProofsExitless.vert_mem p hj⟩
  have hbL : p.vert (j + 1) ∈ L := hmemLb
  have hi1 : L.idxOf (p.vert j) + 1 < P.numVerts := by
    rw [← hsucc_L]; exact List.idxOf_lt_length_of_mem hbL
  have key := ProofsStructure.vert_consec_mem_edges (p := P) (i := L.idxOf (p.vert j)) hi1
  have hva : P.vert (L.idxOf (p.vert j)) = p.vert j := ProofsExitless.vert_pos P hmemLa
  have hvb : P.vert (L.idxOf (p.vert j) + 1) = p.vert (j + 1) := by
    rw [← hsucc_L]; exact ProofsExitless.vert_pos P hmemLb
  rw [hva, hvb] at key
  exact key

/-- **(POS, junction).**  The *last* component's first-edge `pₙ[1]→σ(pₙ[1])` survives — it is
the head→tail junction of the walk. -/
theorem junction_edge_mem {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k) :
    ((ps.getLast hps).first, sigma (ps.getLast hps).first) ∈ (unwindP ps hps hnd).edges := by
  set q := ps.getLast hps with hqdef
  have hqmem : q ∈ ps := List.getLast_mem hps
  have hqSE := hSE q hqmem
  have hk1 : 1 ≤ k := by omega
  have hdvd := Proved.dvd_numVerts_of_stronglyExitless hk1 hqSE
  have hkle : k ≤ q.numVerts := Nat.le_of_dvd q.numVerts_pos hdvd
  have h1lt : 1 < q.numVerts := by omega
  have hkndvd : ¬ k ∣ (0 + 1) := by
    intro h; have := Nat.le_of_dvd (show 0 < 0 + 1 by omega) h; omega
  have hv1 : q.vert 1 = sigma q.first := by
    have h := ProofsExitless.vert_succ hk1 hqSE.1 (i := 0) (show 0 + 1 < q.numVerts by omega) hkndvd
    rwa [q.vert_zero] at h
  set L := unwindVerts ps with hL
  set heads := ps.map HPath.first with hh
  set tails := (ps.reverse.map (fun p => p.verts.drop 1)).flatten with htl
  have hLeq : L = heads ++ tails := rfl
  have hheads_ne : heads ≠ [] := by rw [hh, ne_eq, List.map_eq_nil_iff]; exact hps
  set n := heads.length with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact List.length_pos_of_ne_nil hheads_ne
  have hheads_nd : heads.Nodup := (List.nodup_append.mp (by rw [← hLeq]; exact hnd)).1
  -- q.first is the last head, at index n-1
  have hqf_head : q.first ∈ heads := List.mem_map.mpr ⟨q, hqmem, rfl⟩
  have hheads_last : heads.getLast hheads_ne = q.first := by
    rw [hqdef]; exact List.getLast_map hheads_ne
  have hbound : n - 1 < heads.length := by omega
  have hlast_get : heads[n - 1]'hbound = q.first := by
    rw [← hheads_last]; exact (List.getLast_eq_getElem hheads_ne).symm
  have hidx_heads : heads.idxOf q.first = n - 1 := by
    rw [← hlast_get]; exact hheads_nd.idxOf_getElem (n - 1) hbound
  have hidx_qf : L.idxOf q.first = n - 1 := by
    rw [hLeq, List.idxOf_append_of_mem hqf_head, hidx_heads]
  -- σ q.first is the first tail element, at index n
  have hrev_ne : ps.reverse ≠ [] := by rw [ne_eq, List.reverse_eq_nil_iff]; exact hps
  obtain ⟨qr, rr, hqr⟩ := List.exists_cons_of_ne_nil hrev_ne
  have hqr_q : qr = q := by
    have h1 : ps.reverse.head? = some qr := by rw [hqr]; rfl
    have h2 : ps.reverse.head? = some q := by
      rw [List.head?_reverse, hqdef]; exact List.getLast?_eq_some_getLast hps
    exact Option.some_inj.mp (h1.symm.trans h2)
  have htl_split : tails = q.verts.drop 1 ++ (rr.map (fun p => p.verts.drop 1)).flatten := by
    rw [htl, hqr, List.map_cons, List.flatten_cons, hqr_q]
  have hsig_mem_dq : sigma q.first ∈ q.verts.drop 1 := by
    rw [← hv1]; exact vert_mem_drop1 (le_refl 1) h1lt
  have hsig_tails : sigma q.first ∈ (ps.reverse.map (fun p => p.verts.drop 1)).flatten :=
    mem_tails hqmem hsig_mem_dq
  have hsig_nh : sigma q.first ∉ heads := tail_not_mem_heads hnd hsig_tails
  have hidx_tails : tails.idxOf (sigma q.first) = 0 := by
    rw [htl_split, List.idxOf_append_of_mem hsig_mem_dq, ← hv1]
    have h := idxOf_drop1_vert (p := q) (j := 1) (le_refl 1) h1lt
    simpa using h
  have hidx_sig : L.idxOf (sigma q.first) = n := by
    rw [hLeq, List.idxOf_append_of_notMem hsig_nh, hidx_tails]; omega
  -- assemble the edge
  have hsucc_L : L.idxOf (sigma q.first) = L.idxOf q.first + 1 := by rw [hidx_sig, hidx_qf]; omega
  set P := unwindP ps hps hnd with hP
  have hmemLa : q.first ∈ P.verts := mem_unwindVerts.mpr ⟨q, hqmem, q.first_mem⟩
  have hmemLb : sigma q.first ∈ P.verts := by
    rw [← hv1]; exact mem_unwindVerts.mpr ⟨q, hqmem, ProofsExitless.vert_mem q h1lt⟩
  have hi1 : L.idxOf q.first + 1 < P.numVerts := by
    rw [← hsucc_L]; exact List.idxOf_lt_length_of_mem hmemLb
  have key := ProofsStructure.vert_consec_mem_edges (p := P) (i := L.idxOf q.first) hi1
  have hva : P.vert (L.idxOf q.first) = q.first := ProofsExitless.vert_pos P hmemLa
  have hvb : P.vert (L.idxOf q.first + 1) = sigma q.first := by
    rw [← hsucc_L]; exact ProofsExitless.vert_pos P hmemLb
  rw [hva, hvb] at key
  exact key

/-! ## `S(P) = headSet` -/

/-- **`S(unwindP ps) = {pᵢ[1] : i < n}`** — the firsts of all but the last component.  This is
the paper's asserted `S(P)`.  ⊇ from `first_not_mem_Cm1` + `(NEG)`; ⊆ by the `sset_empty`
dichotomy (block-interior ⇒ its edge survives by `(POS)`; block-end ⇒ `∈ C₋₁`), with the
`j=0` case pinned to a non-last component via `(POS, junction)`. -/
theorem Sset_eq_headSet {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts)
    (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k) :
    Sset (unwindP ps hps hnd) = ((ps.dropLast).map HPath.first).toFinset := by
  set P := unwindP ps hps hnd with hP
  have hk1 : 1 ≤ k := by omega
  ext v
  rw [Sset, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨-, hvC, hedge⟩
    obtain ⟨p, hp, hvp⟩ := hcover v
    have hpSE := hSE p hp
    set i := p.pos v with hi
    have hilt : i < p.numVerts := ProofsExitless.pos_lt p hvp
    have hvi : p.vert i = v := ProofsExitless.vert_pos p hvp
    by_cases hdvd : k ∣ (i + 1)
    · exfalso; apply hvC
      set B := k * (i / k) with hB
      have hBdvd : k ∣ B := ⟨i / k, hB⟩
      have himod : i % k = k - 1 := ProofsExitless.mod_eq_pred_of_dvd_succ hk1 hdvd
      have hiB : B + (k - 1) = i := by have hdm := Nat.div_add_mod i k; rw [← hB] at hdm; omega
      have hBk : B + k ≤ p.numVerts := by omega
      have hstruct := ProofsExitless.vert_eq_sigma_iter hk1 hpSE.1 i hilt
      rw [himod, ← hB] at hstruct
      have hv_eq : v = sigma^[k - 1] (p.vert B) := by rw [← hvi]; exact hstruct
      have hsig : sigma v = p.vert B := by
        rw [hv_eq, Proved.sigma_iter_succ' (k - 1) (p.vert B), show k - 1 + 1 = k from by omega,
          ProofsExitless.sigma_iter_period]
      rw [Cm1, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hsig]; exact blockStart_mem_C0 hps hnd hp hpSE hk1 hBdvd hBk⟩
    · have hi1 : i + 1 < p.numVerts := by
        rcases Nat.lt_or_ge (i + 1) p.numVerts with h | h
        · exact h
        · exact absurd ((show i + 1 = p.numVerts by omega) ▸
            Proved.dvd_numVerts_of_stronglyExitless hk1 hpSE) hdvd
      have hsucc := ProofsExitless.vert_succ hk1 hpSE.1 hi1 hdvd
      rw [hvi] at hsucc
      by_cases hi0 : i = 0
      · rw [hi0] at hvi
        rw [p.vert_zero] at hvi
        by_cases hpdl : p ∈ ps.dropLast
        · exact List.mem_map.mpr ⟨p, hpdl, hvi⟩
        · exfalso; apply hedge
          have hsplit := List.dropLast_append_getLast hps
          have hmem2 : p ∈ ps.dropLast ++ [ps.getLast hps] := hsplit.symm ▸ hp
          rw [List.mem_append, List.mem_singleton] at hmem2
          have hpeq : p = ps.getLast hps := hmem2.resolve_left hpdl
          rw [← hvi, hpeq]
          exact junction_edge_mem hps hnd hSE hk
      · exfalso; apply hedge
        rw [← hsucc, ← hvi]
        exact interior_edge_mem hps hnd hp (by omega) hi1
  · intro hvmem
    obtain ⟨p, hpdl, hpf⟩ := List.mem_map.mp hvmem
    have hp : p ∈ ps := List.dropLast_subset ps hpdl
    have hpSE := hSE p hp
    subst hpf
    exact ⟨Finset.mem_univ _, first_not_mem_Cm1 hps hnd hp hpSE hk,
      first_edge_not_mem_edges hps hnd hpdl hpSE hk⟩

/-! ## Assembling `F(unwindP ps) = X`

With `S(P) = headSet` proved (`Sset_eq_headSet`), `F(P) = f(P, headSet)`, and the abstract
accounting lemma `fPS_eq_of_edges` reduces `f(P, headSet) = X` to the **edge decomposition**
`E(P) = (X ∖ FE) ∪ E₁ ∪ E₂` plus the natural disjointnesses.  The conceptually hard half of
`hFPX` (the global `S(P) = {pᵢ[1]}` computation, needing all of KEY ORDER / `firstInCycle` /
`C₀` / `C₋₁`) is fully discharged; what remains is identifying `E(P)`, `E₁ = E1removed` and
`E₂ = E2removed` with the head-chain / back-links (the `doubles` in-degree bookkeeping). -/

/-- `F(unwindP ps) = X` given the edge decomposition of `P` (the accounting-lemma inputs, with
`S = headSet`).  The `S(P)` computation and the Step-1/Step-2 algebra are discharged. -/
theorem F_unwindP_eq_of_edges {X : Finset (Vtx k × Vtx k)} {ps : List (HPath k)}
    (hps : ps ≠ []) (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts)
    (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    (hdec : (unwindP ps hps hnd).edges =
      (X \ addedEdges ((ps.dropLast.map HPath.first).toFinset)) ∪
        E1removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset) ∪
        E2removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset))
    (hFEsub : addedEdges ((ps.dropLast.map HPath.first).toFinset) ⊆ X)
    (hHCX : Disjoint (E1removed (unwindP ps hps hnd)
      ((ps.dropLast.map HPath.first).toFinset)) X)
    (hHCBL : Disjoint (E1removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset))
      (E2removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset)))
    (hXBL : Disjoint X (E2removed (unwindP ps hps hnd)
      ((ps.dropLast.map HPath.first).toFinset))) :
    F (unwindP ps hps hnd) = X := by
  rw [F, Sset_eq_headSet hps hnd hcover hSE hk]
  exact fPS_eq_of_edges _ _ X hdec hFEsub hHCX hHCBL hXBL

end Hunter.ProofsUnwind2

namespace Hunter.Proved

open Hunter.ProofsUnwind
open Hunter.ProofsUnwind2
open scoped Classical

variable {k : ℕ}

/-- **`prp_Xk_se_sufficiency`, general case — reduced to the explicit edge-decomposition of the
unwound path.**  Compared to `prp_Xk_se_sufficiency_unwind`, the mathematical `F(P) = X`
hypothesis `hFPX` is replaced by the *elementary list-adjacency* decomposition of `E(P)` (plus
the natural disjointnesses): the entire `S(P) = {pᵢ[1]}` computation and the Step-1/Step-2
surgery are now discharged (`Sset_eq_headSet`, `fPS_eq_of_edges`).  -/
theorem prp_Xk_se_sufficiency_unwind2 {X : Finset (Vtx k × Vtx k)} {ps : List (HPath k)}
    (hps : ps ≠ []) (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts)
    (hSE : ∀ p ∈ ps, p.StronglyExitless) (hk : 2 ≤ k)
    (hdec : (unwindP ps hps hnd).edges =
      (X \ addedEdges ((ps.dropLast.map HPath.first).toFinset)) ∪
        E1removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset) ∪
        E2removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset))
    (hFEsub : addedEdges ((ps.dropLast.map HPath.first).toFinset) ⊆ X)
    (hHCX : Disjoint (E1removed (unwindP ps hps hnd)
      ((ps.dropLast.map HPath.first).toFinset)) X)
    (hHCBL : Disjoint (E1removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset))
      (E2removed (unwindP ps hps hnd) ((ps.dropLast.map HPath.first).toFinset)))
    (hXBL : Disjoint X (E2removed (unwindP ps hps hnd)
      ((ps.dropLast.map HPath.first).toFinset))) :
    X ∈ Xk k :=
  ⟨unwindP ps hps hnd, unwind_isHamiltonian hps hnd hcover,
    F_unwindP_eq_of_edges hps hnd hcover hSE hk hdec hFEsub hHCX hHCBL hXBL⟩

end Hunter.Proved

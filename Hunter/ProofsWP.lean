/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsStructure

/-!
# Proofs — Bound 1 core (`prp_wPgivenX`) of Hunter, *A New Lower Bound for Superpermutations*

This file proves `prp_wPgivenX` (`main_version.tex` §5 l.305), the weight bound
`w(P) ≥ (|Comps(X)|−1) + MinThrough(X) + w(X)` for `X = F(P)`, `P` Hamiltonian, and composes
it with `Hunter.Proved.b1` (from `Hunter/ProofsSpine.lean`) to obtain Bound 1 unconditionally.

The argument is the paper's:

* `lem_weightrule` (proved in `ProofsSpine`, discharged here via `clm_eqq_amended`) gives
  `w(P) ≥ w(X) + Σ_{into(P,T'(P))}(w−1) − I + Σ_{out(P,H'(P))} w`.
* the tail-sum is `≥ MinThrough(X) − (|Comps|−1)` (via `cor_pathfirst`, the
  `Comps ↔ tails` bijection, and dropping the `max`);
* the head-sum is `≥ 2·|H'(P)| = 2(|Comps|−1+I)` (the naive `w(out) ≥ 2` bound, and the
  `Comps ↔ heads` bijection).

Helper lemmas live in namespace `Hunter.ProofsWP`; the targets are proved as
`Hunter.Proved.*`.

**Hypothesis taken.** `lem_pathrule` (`Comps(F P)` is a set of path-components) is a §5 target
not proved outright by the structure track (it is the "linearize an acyclic degree-≤1 finite
digraph" construction, ≈150–250 lines, flagged as the keystone obstruction in
`PROGRESS-structure.md`).  It is taken here as the explicit hypothesis `h_pathrule` with the
verbatim `Statements` type.  See `PROGRESS-wp.md`.

**Guard added.** `2 ≤ k` (needed for `vertsOf (F P) = univ`, i.e. no isolated vertices, so the
`Comps ↔ tails/heads` bijections are onto).  Consistent with the paper's `k ≥ 3` regime.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsWP

variable {k : ℕ}

/-! ## Weak-component partition infrastructure

`Comps X` is the image of the block map `v ↦ (vertsOf X).filter (weakConn X v)`.  We record the
standard "equivalence classes partition the vertex set" facts. -/

/-- The weak-connectivity block of `v` in `X` (a canonical representative of its component). -/
noncomputable def block (X : Finset (Vtx k × Vtx k)) (v : Vtx k) : Finset (Vtx k) :=
  (vertsOf X).filter (fun u => weakConn X v u)

theorem weakStep_symm {X : Finset (Vtx k × Vtx k)} {u v : Vtx k}
    (h : weakStep X u v) : weakStep X v u := Or.symm h

/-- Weak connectivity is symmetric (the underlying step relation is). -/
theorem weakConn_symm {X : Finset (Vtx k × Vtx k)} {u v : Vtx k}
    (h : weakConn X u v) : weakConn X v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (weakStep_symm hbc) ih

theorem mem_block {X : Finset (Vtx k × Vtx k)} {v u : Vtx k} :
    u ∈ block X v ↔ u ∈ vertsOf X ∧ weakConn X v u := Finset.mem_filter

theorem self_mem_block {X : Finset (Vtx k × Vtx k)} {v : Vtx k} (hv : v ∈ vertsOf X) :
    v ∈ block X v := mem_block.mpr ⟨hv, Relation.ReflTransGen.refl⟩

/-- Connected vertices have the same block. -/
theorem block_eq_of_conn {X : Finset (Vtx k × Vtx k)} {v w : Vtx k}
    (h : weakConn X v w) : block X v = block X w := by
  ext u
  simp only [mem_block]
  constructor
  · rintro ⟨hu, hvu⟩; exact ⟨hu, (weakConn_symm h).trans hvu⟩
  · rintro ⟨hu, hwu⟩; exact ⟨hu, h.trans hwu⟩

theorem comps_eq_image (X : Finset (Vtx k × Vtx k)) :
    Comps X = (vertsOf X).image (block X) := rfl

theorem mem_comps {X : Finset (Vtx k × Vtx k)} {C : Finset (Vtx k)} :
    C ∈ Comps X ↔ ∃ v ∈ vertsOf X, block X v = C := by
  rw [comps_eq_image, Finset.mem_image]

theorem block_mem_comps {X : Finset (Vtx k × Vtx k)} {v : Vtx k} (hv : v ∈ vertsOf X) :
    block X v ∈ Comps X := mem_comps.mpr ⟨v, hv, rfl⟩

/-- The membership `u ∈ C` pins `C` down to `block X u` (blocks partition `vertsOf X`). -/
theorem comp_eq_block_of_mem {X : Finset (Vtx k × Vtx k)} {C : Finset (Vtx k)} {u : Vtx k}
    (hC : C ∈ Comps X) (hu : u ∈ C) : C = block X u := by
  obtain ⟨v, hv, rfl⟩ := mem_comps.mp hC
  exact (block_eq_of_conn (mem_block.mp hu).2)

/-- A vertex lies in `vertsOf X` iff it is incident to an `X`-edge. -/
theorem mem_vertsOf {X : Finset (Vtx k × Vtx k)} {v : Vtx k} :
    v ∈ vertsOf X ↔ ∃ e ∈ X, v = e.1 ∨ v = e.2 := by
  rw [vertsOf, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Distinct components are disjoint (they partition `vertsOf X`). -/
theorem comps_disjoint {X : Finset (Vtx k × Vtx k)} {C C' : Finset (Vtx k)}
    (hC : C ∈ Comps X) (hC' : C' ∈ Comps X) (hne : C ≠ C') : Disjoint C C' := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hne ((comp_eq_block_of_mem hC hv).trans (comp_eq_block_of_mem hC' hv').symm)

/-! ## Component heads (the out-degree-0 analogue of `compTails`) -/

/-- The out-degree-0 vertices of a component `C` under `X` (its *head*; for a path component,
the singleton `{p[|p|]}`). -/
noncomputable def compHeads (X : Finset (Vtx k × Vtx k)) (C : Finset (Vtx k)) :
    Finset (Vtx k) := C.filter (fun v => outV X v = ∅)

theorem compTails_subset {X : Finset (Vtx k × Vtx k)} {C : Finset (Vtx k)} :
    compTails X C ⊆ C := Finset.filter_subset _ _

theorem compHeads_subset {X : Finset (Vtx k × Vtx k)} {C : Finset (Vtx k)} :
    compHeads X C ⊆ C := Finset.filter_subset _ _

/-- On a path-component `p` of `X`, the (component-)heads are exactly `{p[|p|]}`. -/
theorem compHeads_eq {p : HPath k} {X : Finset (Vtx k × Vtx k)}
    (hp : IsPathComponent p X) : compHeads X p.vertsFinset = {p.last} := by
  ext v
  rw [compHeads, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hvV, hout⟩
    by_contra hne
    obtain ⟨w, hw⟩ := ProofsStructure.out_edge_of_ne_last (HPath.mem_vertsFinset.mp hvV) hne
    have hwX : (v, w) ∈ X := hp.1 hw
    have hmem : (v, w) ∈ outV X v := by
      rw [outV, mem_out]; exact ⟨hwX, Finset.mem_singleton_self v⟩
    rw [hout] at hmem; exact absurd hmem (Finset.notMem_empty _)
  · rintro rfl
    refine ⟨HPath.mem_vertsFinset.mpr p.last_mem, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro e he
    rw [outV, mem_out, Finset.mem_singleton] at he
    obtain ⟨heX, he1⟩ := he
    have h1V : e.1 ∈ p.vertsFinset := by rw [he1]; exact HPath.mem_vertsFinset.mpr p.last_mem
    have hee : e ∈ p.edges := hp.2.2 e heX h1V
    exact (ProofsStructure.ne_last_of_out_edge hee) he1

/-! ## The `Comps ↔ tails` and `Comps ↔ heads` cardinality identities -/

/-- `tails X` is the disjoint union of the singleton component-tails. -/
theorem tails_eq_biUnion {X : Finset (Vtx k × Vtx k)} (hV : vertsOf X = Finset.univ) :
    tails X = (Comps X).biUnion (compTails X) := by
  ext t
  rw [Finset.mem_biUnion]
  constructor
  · intro ht
    rw [tails, Finset.mem_filter] at ht
    have htv : t ∈ vertsOf X := hV ▸ Finset.mem_univ t
    refine ⟨block X t, block_mem_comps htv, ?_⟩
    rw [compTails, Finset.mem_filter]
    exact ⟨self_mem_block htv, ht.2⟩
  · rintro ⟨C, _, htC⟩
    rw [compTails, Finset.mem_filter] at htC
    rw [tails, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, htC.2⟩

/-- `heads X` is the disjoint union of the singleton component-heads. -/
theorem heads_eq_biUnion {X : Finset (Vtx k × Vtx k)} (hV : vertsOf X = Finset.univ) :
    heads X = (Comps X).biUnion (compHeads X) := by
  ext t
  rw [Finset.mem_biUnion]
  constructor
  · intro ht
    rw [heads, Finset.mem_filter] at ht
    have htv : t ∈ vertsOf X := hV ▸ Finset.mem_univ t
    refine ⟨block X t, block_mem_comps htv, ?_⟩
    rw [compHeads, Finset.mem_filter]
    exact ⟨self_mem_block htv, ht.2⟩
  · rintro ⟨C, _, htC⟩
    rw [compHeads, Finset.mem_filter] at htC
    rw [heads, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, htC.2⟩

/-- `|tails X| = |Comps X|` when there are no isolated vertices and every component has a
unique tail. -/
theorem card_tails_eq_numComps {X : Finset (Vtx k × Vtx k)} (hV : vertsOf X = Finset.univ)
    (hsingle : ∀ C ∈ Comps X, ∃ t, compTails X C = {t}) :
    (tails X).card = numComps X := by
  rw [tails_eq_biUnion hV,
    Finset.card_biUnion (fun C hC C' hC' hne =>
      (comps_disjoint hC hC' hne).mono compTails_subset compTails_subset)]
  have hone : ∀ C ∈ Comps X, (compTails X C).card = 1 := by
    intro C hC; obtain ⟨t, ht⟩ := hsingle C hC; rw [ht, Finset.card_singleton]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, numComps]

/-- `|heads X| = |Comps X|` when there are no isolated vertices and every component has a
unique head. -/
theorem card_heads_eq_numComps {X : Finset (Vtx k × Vtx k)} (hV : vertsOf X = Finset.univ)
    (hsingle : ∀ C ∈ Comps X, ∃ t, compHeads X C = {t}) :
    (heads X).card = numComps X := by
  rw [heads_eq_biUnion hV,
    Finset.card_biUnion (fun C hC C' hC' hne =>
      (comps_disjoint hC hC' hne).mono compHeads_subset compHeads_subset)]
  have hone : ∀ C ∈ Comps X, (compHeads X C).card = 1 := by
    intro C hC; obtain ⟨t, ht⟩ := hsingle C hC; rw [ht, Finset.card_singleton]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, numComps]

/-! ## Facts about the Hamiltonian path `P` itself -/

/-- A Hamiltonian path spans all vertices. -/
theorem vertsFinset_univ_of_ham {P : HPath k} (hP : P.IsHamiltonian) :
    P.vertsFinset = Finset.univ :=
  Finset.eq_univ_of_forall (fun v => HPath.mem_vertsFinset.mpr (hP v))

/-- Both endpoints of a path edge lie on the path. -/
theorem edge_ends_mem {p : HPath k} {e : Vtx k × Vtx k} (he : e ∈ p.edges) :
    e.1 ∈ p.verts ∧ e.2 ∈ p.verts := by
  rw [ProofsSpine.mem_edges_iff] at he
  obtain ⟨h1, h2⟩ := List.of_mem_zip he
  exact ⟨h1, p.verts.tail_sublist.subset h2⟩

/-- Every path is a path-component of its own edge set. -/
theorem isPathComponent_self (p : HPath k) : IsPathComponent p p.edges := by
  refine ⟨subset_rfl, fun e he => ?_, fun e he _ => he⟩
  constructor
  · intro _; exact HPath.mem_vertsFinset.mpr (edge_ends_mem he).2
  · intro _; exact HPath.mem_vertsFinset.mpr (edge_ends_mem he).1

/-- The tail of a Hamiltonian path is exactly its start `P[1]`.  (`tails P.edges` is
definitionally `compTails P.edges univ`.) -/
theorem tails_edges_ham {P : HPath k} (hP : P.IsHamiltonian) :
    tails P.edges = {P.first} := by
  have h := ProofsSpine.compTails_eq (isPathComponent_self P)
  rw [vertsFinset_univ_of_ham hP] at h
  exact h

/-- The head of a Hamiltonian path is exactly its end `P[|P|]`.  (`heads P.edges` is
definitionally `compHeads P.edges univ`.) -/
theorem heads_edges_ham {P : HPath k} (hP : P.IsHamiltonian) :
    heads P.edges = {P.last} := by
  have h := compHeads_eq (isPathComponent_self P)
  rw [vertsFinset_univ_of_ham hP] at h
  exact h

/-! ## The singleton component-tail / component-head facts for `X = F(P)` (from `h_pathrule`) -/

theorem compTails_F_single {P : HPath k}
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P))
    {C : Finset (Vtx k)} (hC : C ∈ Comps (F P)) : ∃ t, compTails (F P) C = {t} := by
  obtain ⟨p, hpv, hpc⟩ := h_pathrule C hC
  exact ⟨p.first, hpv ▸ ProofsSpine.compTails_eq hpc⟩

theorem compHeads_F_single {P : HPath k}
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P))
    {C : Finset (Vtx k)} (hC : C ∈ Comps (F P)) : ∃ t, compHeads (F P) C = {t} := by
  obtain ⟨p, hpv, hpc⟩ := h_pathrule C hC
  exact ⟨p.last, hpv ▸ compHeads_eq hpc⟩

/-! ## The naive bound `w(out(P,v)) ≥ 2` for a new head (via `E₂`) -/

/-- Every `E₂`-edge has weight `≥ 2` (the "naive bound"): if `(v→x) ∈ E₂` then `x` is a double,
so `x` receives an *added* 1-edge from `σ⁻¹x ∈ S`; were `(v→x)` a 1-edge we would have `v ∈ S`
with `(v→σv) ∈ E(P)`, contradicting the S-precondition. -/
theorem two_le_ew_E2 {P : HPath k} (hk : 1 ≤ k) {e : Vtx k × Vtx k}
    (he : e ∈ E2removed P (Sset P)) : 2 ≤ ew k e.1 e.2 := by
  rw [E2removed, Finset.mem_filter] at he
  obtain ⟨heP, hd⟩ := he
  have h1 : 1 ≤ ew k e.1 e.2 := ProofsSpine.one_le_ew_of_mem_edges heP
  rcases Nat.lt_or_ge (ew k e.1 e.2) 2 with hlt | hge
  · exfalso
    have hone : ew k e.1 e.2 = 1 := by omega
    have hsig : e.2 = sigma e.1 := (ProofsExitless.ew_eq_one_iff hk).mp hone
    have hd' : sigma e.1 ∈ doubles P (Sset P) := hsig ▸ hd
    have hmemS : e.1 ∈ Sset P := ProofsStructure.mem_S_of_sigma_double hd'
    have hnp : (e.1, sigma e.1) ∉ P.edges := sset_sPrecond P e.1 hmemS
    rw [← hsig] at hnp
    exact hnp heP
  · exact hge

/-- `P.last` has no `P`-out-edge (it is the head of the Hamiltonian path). -/
theorem outV_last_empty {P : HPath k} (hP : P.IsHamiltonian) : outV P.edges P.last = ∅ := by
  have h := heads_edges_ham hP
  have hmem : P.last ∈ heads P.edges := by rw [h]; exact Finset.mem_singleton_self _
  rw [heads, Finset.mem_filter] at hmem
  exact hmem.2

/-- `P.last` is a head of `F(P)` iff it lies in `C₋₁` (iff `P.last ∉ S(P)`, i.e. `I = 0`). -/
theorem last_mem_heads_F_iff {P : HPath k} (hP : P.IsHamiltonian) :
    P.last ∈ heads (F P) ↔ P.last ∈ Cm1 P := by
  rw [heads, Finset.mem_filter]
  constructor
  · rintro ⟨-, hout⟩
    by_contra hc
    rw [Hunter.Proved.clm_rule2 hP hc] at hout
    exact absurd hout (Finset.singleton_ne_empty _)
  · intro hc
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hne
    have h1 := Hunter.Proved.clm_rule1 hP hc hne
    rw [outV_last_empty hP] at h1
    exact hne h1

/-! ## Head-count and the head-sum lower bound (naive bound, Bound 1 term (B)) -/

/-- `F(P)` has at least one component (no isolated vertices, and `Vtx k` is inhabited). -/
theorem one_le_numComps_F {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    1 ≤ numComps (F P) := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  obtain ⟨v⟩ := ProofsSpine.vtx_nonempty k
  have hvV : v ∈ vertsOf (F P) := hV ▸ Finset.mem_univ v
  exact Finset.card_pos.mpr ⟨block (F P) v, block_mem_comps hvV⟩

/-- `|out(P, U)| = |U|` when every vertex of `U` has a `P`-out-edge (the source map is a
bijection on a simple path). -/
theorem card_out_source_eq {P : HPath k} {U : Finset (Vtx k)}
    (hU : ∀ v ∈ U, outV P.edges v ≠ ∅) : (out P.edges U).card = U.card := by
  have himg : (out P.edges U).image Prod.fst = U := by
    ext v
    simp only [Finset.mem_image, out, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨-, he1⟩, rfl⟩; exact he1
    · intro hv
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr (hU v hv)
      simp only [outV, mem_out, Finset.mem_singleton] at he
      exact ⟨e, ⟨he.1, he.2 ▸ hv⟩, he.2⟩
  have hinj : Set.InjOn Prod.fst (out P.edges U : Set (Vtx k × Vtx k)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, out, Finset.mem_filter] at ha hb
    exact Finset.card_le_one.mp (ProofsSpine.path_out_le_one P a.1) a
      (by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨ha.1, trivial⟩) b
      (by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hb.1, hab.symm⟩)
  rw [← Finset.card_image_of_injOn hinj, himg]

/-- The 1-edge out of the head is never a `P`-edge (the head has no out-edge). -/
theorem last_notMem_out_edge {P : HPath k} : (P.last, sigma P.last) ∉ P.edges :=
  fun h => (ProofsStructure.ne_last_of_out_edge h) rfl

/-- `I = 𝟙[P.last ∈ S(P)]` equals `1` exactly when `P.last` is *not* a head of `F(P)`. -/
theorem indicatorI_eq_ite {P : HPath k} (hP : P.IsHamiltonian) :
    indicatorI P (Sset P) = if P.last ∈ heads (F P) then 0 else 1 := by
  have hSiff : P.last ∈ Sset P ↔ P.last ∉ Cm1 P := by
    rw [Sset, Finset.mem_filter]
    exact ⟨fun h => h.2.1, fun h => ⟨Finset.mem_univ _, h, last_notMem_out_edge⟩⟩
  rw [indicatorI]
  by_cases hh : P.last ∈ heads (F P)
  · rw [if_pos hh, if_neg]
    rw [hSiff]; exact fun hc => hc ((last_mem_heads_F_iff hP).mp hh)
  · rw [if_neg hh, if_pos]
    rw [hSiff]; exact fun hc => hh ((last_mem_heads_F_iff hP).mpr hc)

/-- The head-count identity `|H(X) ∖ H(P)| + 𝟙[P.last ∈ H(X)] = |Comps(X)|`. -/
theorem head_count {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    (heads (F P) \ heads P.edges).card + (if P.last ∈ heads (F P) then 1 else 0)
      = numComps (F P) := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  have hnc : (heads (F P)).card = numComps (F P) :=
    card_heads_eq_numComps hV (fun C hC => compHeads_F_single h_pathrule hC)
  rw [heads_edges_ham hP]
  have hinter : (heads (F P) ∩ {P.last}).card = if P.last ∈ heads (F P) then 1 else 0 := by
    by_cases hh : P.last ∈ heads (F P)
    · rw [if_pos hh, Finset.inter_singleton_of_mem hh, Finset.card_singleton]
    · rw [if_neg hh, Finset.inter_singleton_of_notMem hh, Finset.card_empty]
  rw [← hinter, Finset.card_sdiff_add_card_inter, hnc]

/-- **Bound 1, term (B)** — the naive head-sum bound
`Σ_{out(P,H'(P))} w ≥ 2(|Comps|−1) + I`. -/
theorem head_sum_lower {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    2 * ((numComps (F P) : ℤ) - 1) + (indicatorI P (Sset P) : ℤ)
      ≤ ∑ e ∈ out P.edges (heads (F P) \ heads P.edges), (ew k e.1 e.2 : ℤ) := by
  set Hp := heads (F P) \ heads P.edges with hHp
  set OUT := out P.edges Hp with hOUT
  -- OUT = E₂removed, so every edge has weight ≥ 2
  have hOUTE2 : OUT = E2removed P (Sset P) := (Hunter.Proved.clm_e2 (sset_sPrecond P)).symm
  have htwo : ∀ e ∈ OUT, 2 ≤ ew k e.1 e.2 := by
    intro e he; rw [hOUTE2] at he; exact two_le_ew_E2 (by omega) he
  -- 2·|OUT| ≤ Σ w  (ℕ), then cast to ℤ
  have hns : 2 * OUT.card ≤ ∑ e ∈ OUT, ew k e.1 e.2 := by
    have := Finset.card_nsmul_le_sum OUT (fun e => ew k e.1 e.2) 2 htwo
    simpa [smul_eq_mul, mul_comm] using this
  have hcastsum : (∑ e ∈ OUT, (ew k e.1 e.2 : ℤ)) = ((∑ e ∈ OUT, ew k e.1 e.2 : ℕ) : ℤ) := by
    push_cast; rfl
  -- |OUT| = |Hp|
  have hOUTcard : OUT.card = Hp.card := by
    apply card_out_source_eq
    intro v hv
    rw [hHp, Finset.mem_sdiff] at hv
    intro hcon
    exact hv.2 (by rw [heads, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcon⟩)
  -- head count pins |Hp| against numComps and I
  have hcount := head_count hP hk h_pathrule
  rw [← hHp] at hcount
  have hI := indicatorI_eq_ite hP
  have hnc1 := one_le_numComps_F hP hk
  rw [hcastsum]
  have hge : (2 * OUT.card : ℤ) ≤ (∑ e ∈ OUT, ew k e.1 e.2 : ℕ) := by exact_mod_cast hns
  refine le_trans ?_ hge
  rw [hOUTcard, hI]
  -- ℤ arithmetic: case on whether P.last is a head of F(P)
  by_cases hh : P.last ∈ heads (F P)
  · rw [if_pos hh] at hcount ⊢
    push_cast; omega
  · rw [if_neg hh] at hcount ⊢
    push_cast; omega

/-! ## Tail-side data (component of a tail, and `cor_pathfirst` order) -/

/-- For a tail `t` of `F(P)`, its component is realized by a path-component `p` with
`p[1] = t`, and `t` is the `P`-earliest vertex of that component (`cor_pathfirst`). -/
theorem tail_data {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P))
    {t : Vtx k} (ht : t ∈ tails (F P)) :
    ∃ p : HPath k, p.vertsFinset = block (F P) t ∧ p.first = t ∧ IsPathComponent p (F P) ∧
      ∀ u ∈ block (F P) t, P.pos t ≤ P.pos u := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  have htv : t ∈ vertsOf (F P) := hV ▸ Finset.mem_univ t
  have hC : block (F P) t ∈ Comps (F P) := block_mem_comps htv
  obtain ⟨p, hpv, hpc⟩ := h_pathrule _ hC
  have hct : compTails (F P) (block (F P) t) = {p.first} := hpv ▸ ProofsSpine.compTails_eq hpc
  have htin : t ∈ compTails (F P) (block (F P) t) := by
    rw [compTails, Finset.mem_filter]
    refine ⟨self_mem_block htv, ?_⟩
    rw [tails, Finset.mem_filter] at ht; exact ht.2
  rw [hct, Finset.mem_singleton] at htin
  refine ⟨p, hpv, htin.symm, hpc, ?_⟩
  intro u hu
  rw [← hpv] at hu
  rw [htin]
  exact Hunter.Proved.cor_pathfirst hP hpc (HPath.mem_vertsFinset.mp hu)

/-- The start `P[1]` of the Hamiltonian path is a tail of `F(P)`. -/
theorem first_mem_tails {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    P.first ∈ tails (F P) := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  have hfv : P.first ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have hC : block (F P) P.first ∈ Comps (F P) := block_mem_comps hfv
  obtain ⟨p, hpv, hpc⟩ := h_pathrule _ hC
  have hct : compTails (F P) (block (F P) P.first) = {p.first} :=
    hpv ▸ ProofsSpine.compTails_eq hpc
  have hpfmem : P.first ∈ p.verts := by
    rw [← HPath.mem_vertsFinset, hpv]; exact self_mem_block hfv
  have hcp := Hunter.Proved.cor_pathfirst hP hpc hpfmem
  rw [ProofsStructure.pos_first] at hcp
  have hpf0 : P.pos p.first = 0 := Nat.le_zero.mp hcp
  have hpfeq : P.first = p.first := by
    have := ProofsExitless.vert_pos P (hP p.first)
    rw [hpf0, P.vert_zero] at this; exact this
  rw [tails, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hmem : P.first ∈ compTails (F P) (block (F P) P.first) := by
    rw [hct, Finset.mem_singleton]; exact hpfeq
  rw [compTails, Finset.mem_filter] at hmem
  exact hmem.2

/-- **Pointwise `minto` bound** — the `P`-in-edge of a tail `t ≠ P[1]` has weight
`≥ compMinto` of `t`'s component (its source lies outside the component, by `cor_pathfirst`). -/
theorem compMinto_le_ew {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P))
    {e : Vtx k × Vtx k} (heP : e ∈ P.edges) (ht : e.2 ∈ tails (F P)) :
    compMinto (F P) (block (F P) e.2) ≤ ew k e.1 e.2 := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  obtain ⟨p, hpv, hpf, hpc, hmin⟩ := tail_data hP hk h_pathrule ht
  have h2v : e.2 ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
  have h1notin : e.1 ∉ block (F P) e.2 := by
    intro hc
    have hle := hmin e.1 hc
    have hlt : P.pos e.1 < P.pos e.2 := by rw [ProofsStructure.edge_pos_succ heP]; omega
    omega
  apply Nat.sInf_le
  refine ⟨e.1, h1notin, e.2, ?_, rfl⟩
  rw [compTails, Finset.mem_filter]
  refine ⟨self_mem_block h2v, ?_⟩
  rw [tails, Finset.mem_filter] at ht; exact ht.2

/-! ## `MinThrough` drops the single largest `compMinto` -/

/-- Dropping the component `C₀` of `P[1]` from `Σ compMinto` still dominates `MinThrough`
(which drops the *maximum* `compMinto`). -/
theorem minThrough_add_compMinto_le {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    MinThrough (F P) + compMinto (F P) (block (F P) P.first)
      ≤ ∑ C ∈ Comps (F P), compMinto (F P) C := by
  have hfv : P.first ∈ vertsOf (F P) := (ProofsStructure.vertsOf_F_eq_univ hP hk) ▸ Finset.mem_univ _
  have hC₀ : block (F P) P.first ∈ Comps (F P) := block_mem_comps hfv
  rw [MinThrough]
  by_cases hle : (Comps (F P)).card ≤ 1
  · rw [if_pos hle, zero_add]
    exact Finset.single_le_sum (f := fun C => compMinto (F P) C) (fun _ _ => Nat.zero_le _) hC₀
  · rw [if_neg hle]
    have hsup : compMinto (F P) (block (F P) P.first)
        ≤ (Comps (F P)).sup (fun C => compMinto (F P) C) := Finset.le_sup hC₀
    have hsupsum : (Comps (F P)).sup (fun C => compMinto (F P) C)
        ≤ ∑ C ∈ Comps (F P), compMinto (F P) C :=
      Finset.sup_le (fun C hC => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hC)
    omega

/-- **Bound 1, term (A)** — the tail `minto` bound
`Σ_{into(P,T'(P))}(w−1) ≥ MinThrough(X) − (|Comps|−1)`. -/
theorem tail_sum_lower {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    (MinThrough (F P) : ℤ) - ((numComps (F P) : ℤ) - 1)
      ≤ ∑ e ∈ into P.edges (tails (F P) \ tails P.edges), ((ew k e.1 e.2 : ℤ) - 1) := by
  have hV := ProofsStructure.vertsOf_F_eq_univ hP hk
  set E := into P.edges (tails (F P) \ tails P.edges) with hE
  set C₀ := block (F P) P.first with hC₀def
  set D := Comps (F P) \ {C₀} with hDdef
  have hC₀ : C₀ ∈ Comps (F P) :=
    block_mem_comps (hV ▸ Finset.mem_univ (P.first))
  have hfirstT : P.first ∈ tails (F P) := first_mem_tails hP hk h_pathrule
  -- helper: a tail's component has a unique tail
  have huniqTail : ∀ {a b : Vtx k}, a ∈ tails (F P) → b ∈ tails (F P) →
      block (F P) a = block (F P) b → a = b := by
    intro a b ha hb hab
    have hav : a ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
    have hbv : b ∈ vertsOf (F P) := hV ▸ Finset.mem_univ _
    obtain ⟨t, htsingle⟩ := compTails_F_single h_pathrule (block_mem_comps hav)
    have hain : a ∈ compTails (F P) (block (F P) a) := by
      rw [compTails, Finset.mem_filter]
      exact ⟨self_mem_block hav, (Finset.mem_filter.mp ha).2⟩
    have hbin : b ∈ compTails (F P) (block (F P) a) := by
      rw [compTails, Finset.mem_filter]
      refine ⟨?_, (Finset.mem_filter.mp hb).2⟩
      rw [hab]; exact self_mem_block hbv
    rw [htsingle, Finset.mem_singleton] at hain hbin
    rw [hain, hbin]
  -- the bijection e ↦ block e.2 from E onto D
  have hmemE : ∀ {e : Vtx k × Vtx k}, e ∈ E →
      e ∈ P.edges ∧ e.2 ∈ tails (F P) ∧ e.2 ≠ P.first := by
    intro e he
    rw [hE, mem_into, Finset.mem_sdiff, tails_edges_ham hP, Finset.mem_singleton] at he
    exact ⟨he.1, he.2.1, he.2.2⟩
  have hi : ∀ e (he : e ∈ E), block (F P) e.2 ∈ D := by
    intro e he
    obtain ⟨heP, ht, hne⟩ := hmemE he
    rw [hDdef, Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨block_mem_comps (hV ▸ Finset.mem_univ _), ?_⟩
    intro hcon
    exact hne (huniqTail ht hfirstT hcon)
  have i_inj : ∀ e₁ (he₁ : e₁ ∈ E) e₂ (he₂ : e₂ ∈ E),
      block (F P) e₁.2 = block (F P) e₂.2 → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ hb
    obtain ⟨he₁P, ht₁, -⟩ := hmemE he₁
    obtain ⟨he₂P, ht₂, -⟩ := hmemE he₂
    have h22 : e₁.2 = e₂.2 := huniqTail ht₁ ht₂ hb
    exact Finset.card_le_one.mp (ProofsSpine.path_into_le_one P e₁.2) e₁
      (by rw [intoV, mem_into]; exact ⟨he₁P, Finset.mem_singleton_self _⟩) e₂
      (by rw [intoV, mem_into]; exact ⟨he₂P, h22 ▸ Finset.mem_singleton_self _⟩)
  have i_surj : ∀ C ∈ D, ∃ e, ∃ (_ : e ∈ E), block (F P) e.2 = C := by
    intro C hCD
    rw [hDdef, Finset.mem_sdiff, Finset.mem_singleton] at hCD
    obtain ⟨hCcomp, hCne⟩ := hCD
    obtain ⟨t, htsingle⟩ := compTails_F_single h_pathrule hCcomp
    have htC : t ∈ C := compTails_subset (by rw [htsingle]; exact Finset.mem_singleton_self _)
    have htT : t ∈ tails (F P) := by
      rw [tails, Finset.mem_filter]
      have : t ∈ compTails (F P) C := by rw [htsingle]; exact Finset.mem_singleton_self _
      rw [compTails, Finset.mem_filter] at this
      exact ⟨Finset.mem_univ _, this.2⟩
    have hblockt : block (F P) t = C := (comp_eq_block_of_mem hCcomp htC).symm
    have htne : t ≠ P.first := by
      intro hcon; exact hCne (by rw [← hblockt, hcon])
    obtain ⟨u, hu⟩ := ProofsSpine.exists_pred (hP t) htne
    refine ⟨(u, t), ?_, hblockt⟩
    rw [hE, mem_into, Finset.mem_sdiff, tails_edges_ham hP, Finset.mem_singleton]
    exact ⟨hu, htT, htne⟩
  -- reindex ∑_{C∈D}(compMinto−1) = ∑_{e∈E}(compMinto(block e.2)−1)
  have hbij : ∑ e ∈ E, ((compMinto (F P) (block (F P) e.2) : ℤ) - 1)
      = ∑ C ∈ D, ((compMinto (F P) C : ℤ) - 1) :=
    Finset.sum_bij (fun e _ => block (F P) e.2) hi i_inj i_surj (fun e _ => rfl)
  -- pointwise: compMinto(block e.2) ≤ ew e
  have hpt : ∑ e ∈ E, ((compMinto (F P) (block (F P) e.2) : ℤ) - 1)
      ≤ ∑ e ∈ E, ((ew k e.1 e.2 : ℤ) - 1) := by
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨heP, ht, -⟩ := hmemE he
    have hle := compMinto_le_ew hP hk h_pathrule heP ht
    have : (compMinto (F P) (block (F P) e.2) : ℤ) ≤ (ew k e.1 e.2 : ℤ) := by exact_mod_cast hle
    linarith
  -- evaluate ∑_{C∈D}(compMinto−1)
  have hnc1 := one_le_numComps_F hP hk
  have hDcard : D.card = numComps (F P) - 1 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hC₀)
    rw [Finset.card_singleton, ← hDdef] at h
    rw [numComps]
    omega
  have hsumsdiff : (∑ C ∈ D, (compMinto (F P) C : ℤ)) + (compMinto (F P) C₀ : ℤ)
      = ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
    have := Finset.sum_sdiff (f := fun C => (compMinto (F P) C : ℤ))
      (Finset.singleton_subset_iff.mpr hC₀)
    rwa [Finset.sum_singleton, ← hDdef] at this
  have hDval : ∑ C ∈ D, ((compMinto (F P) C : ℤ) - 1)
      = (∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ)) - (compMinto (F P) C₀ : ℤ)
        - ((numComps (F P) : ℤ) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hDcard]
    push_cast [hnc1]
    linarith [hsumsdiff]
  -- MinThrough bound, cast to ℤ
  have hmt : (MinThrough (F P) : ℤ) + (compMinto (F P) C₀ : ℤ)
      ≤ ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by
    have := minThrough_add_compMinto_le hP hk
    rw [← hC₀def] at this
    calc (MinThrough (F P) : ℤ) + (compMinto (F P) C₀ : ℤ)
        = ((MinThrough (F P) + compMinto (F P) C₀ : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((∑ C ∈ Comps (F P), compMinto (F P) C : ℕ) : ℤ) := by exact_mod_cast this
      _ = ∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ) := by push_cast; rfl
  -- assemble
  calc (MinThrough (F P) : ℤ) - ((numComps (F P) : ℤ) - 1)
      ≤ ((∑ C ∈ Comps (F P), (compMinto (F P) C : ℤ)) - (compMinto (F P) C₀ : ℤ))
          - ((numComps (F P) : ℤ) - 1) := by linarith [hmt]
    _ = ∑ C ∈ D, ((compMinto (F P) C : ℤ) - 1) := by rw [hDval]
    _ = ∑ e ∈ E, ((compMinto (F P) (block (F P) e.2) : ℤ) - 1) := hbij.symm
    _ ≤ ∑ e ∈ E, ((ew k e.1 e.2 : ℤ) - 1) := hpt

end ProofsWP

/-! ## Targets (`Hunter.Proved.*`) -/

namespace Proved

open scoped Classical

variable {k : ℕ}

/-- **prp-wPgivenX** — `main_version.tex` §5 l.305.  For a Hamiltonian `P`, `X = F(P)`:
`w(P) ≥ (|Comps(X)|−1) + MinThrough(X) + w(X)`.

Proved from `lem_weightrule` (discharged via `clm_eqq_amended`), the tail `minto` bound
(`ProofsWP.tail_sum_lower`, using `cor_pathfirst`), and the naive head bound
(`ProofsWP.head_sum_lower`).

**Hypothesis taken:** `h_pathrule` — the `Statements` type of `lem_pathrule` (`Comps(F P)` is a
set of path-components), a §5 target not proved outright by the structure track.
**Guard added:** `2 ≤ k` (so `vertsOf (F P) = univ`, i.e. no isolated vertices).  Both are
consistent with the paper's Hamiltonian-`P`, `k ≥ 3` regime; see `PROGRESS-wp.md`. -/
theorem prp_wPgivenX {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (h_pathrule : ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    P.wtP ≥ (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) := by
  have hSV : Sset P ⊆ P.vertsFinset := by
    rw [ProofsWP.vertsFinset_univ_of_ham hP]; exact Finset.subset_univ _
  have h_eqq := Hunter.Proved.clm_eqq_amended (by omega : (1 : ℕ) ≤ k) hSV (sset_sPrecond P)
  have hwr := Hunter.Proved.lem_weightrule (sset_sPrecond P) h_eqq
  rw [← ProofsStructure.F_eq] at hwr
  have hA := ProofsWP.tail_sum_lower hP hk h_pathrule
  have hB := ProofsWP.head_sum_lower hP hk h_pathrule
  have hnc1 := ProofsWP.one_le_numComps_F hP hk
  have hz : (P.wtP : ℤ)
      ≥ (wEdges (F P) : ℤ) + (MinThrough (F P) : ℤ) + ((numComps (F P) : ℤ) - 1) := by
    linarith [hwr, hA, hB]
  have hgoal : (((numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) : ℕ) : ℤ)
      ≤ (P.wtP : ℤ) := by
    calc (((numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) : ℕ) : ℤ)
        = (numComps (F P) : ℤ) - 1 + (MinThrough (F P) : ℤ) + (wEdges (F P) : ℤ) := by
          push_cast [Nat.cast_sub hnc1]; ring
      _ ≤ (P.wtP : ℤ) := by linarith [hz]
  exact_mod_cast hgoal

/-- **b1 (unconditional in `P`)** — Bound 1, `main_version.tex` §"Outline" l.183, obtained by
feeding `prp_wPgivenX` into `Hunter.Proved.b1` (from `ProofsSpine`).  Carries the same
`h_pathrule` (`lem_pathrule`, now quantified over all Hamiltonian `P`) and `2 ≤ k` guard as
`prp_wPgivenX`. -/
theorem b1_unconditional (hk : 2 ≤ k)
    (h_pathrule : ∀ (P : HPath k), P.IsHamiltonian →
      ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P)) :
    L k ≥ sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} :=
  Hunter.Proved.b1 (fun P hP => prp_wPgivenX hP hk (h_pathrule P hP))

end Proved

end Hunter

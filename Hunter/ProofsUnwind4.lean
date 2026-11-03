/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsUnwind3
import Hunter.ProofsB2

/-!
# Closing the bridge to verbatim `prp_Xk_se_sufficiency` (Hunter §5)

`Hunter/ProofsUnwind3.lean` proved `prp_Xk_se_sufficiency_unwind3`: from a list `ps` of
pairwise vertex-disjoint strongly-exitless paths that cover `𝒮_k` and whose edge-sets union to
`X`, we get `X ∈ 𝒳_k`.  This file supplies the remaining **`Comps(X) → ps` construction**:
given the *verbatim* sufficiency hypotheses (`vertsOf X = univ`, `IsUnionOfStronglyExitlessPaths X`),
we pick one path witness per weak component of `X`, order the components as a list, and discharge
each of the six hypotheses of `..._unwind3`.  This delivers `Hunter.Proved.prp_Xk_se_sufficiency`
(with the `2 ≤ k` guard, consistent with the `prp_Xk_se_necessity` amendment).

See `PROGRESS-unwind4.md`.
-/

namespace Hunter.ProofsUnwind4

open List
open Hunter.ProofsUnwind
open scoped Classical

variable {k : ℕ}

/-! ## Generic `unwindVerts` nodup from pairwise vertex-disjointness -/

/-- The first vertex of a path is not among the remaining (dropped-first) vertices — the head of
a `Nodup` list is not in its tail. -/
theorem first_not_mem_drop1 (p : HPath k) : p.first ∉ p.verts.drop 1 := by
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil p.ne
  have hf : p.first = a := ProofsSpine.first_eq hat
  have hd : p.verts.drop 1 = t := by rw [hat, List.drop_one, List.tail_cons]
  rw [hf, hd]
  have hnd : (a :: t).Nodup := hat ▸ p.nodup
  exact (List.nodup_cons.mp hnd).1

/-- **Key well-formedness fact.**  If a list of paths is pairwise vertex-disjoint, then the
unwinding vertex list `unwindVerts ps = (firsts) ++ (reversed remainders)` is duplicate-free.
This discharges the `hnd` hypothesis of `prp_Xk_se_sufficiency_unwind3` from the cleaner
`hpair` (pairwise `Disjoint vertsFinset`) supplied by `Comps(X)`. -/
theorem unwindVerts_nodup_of_pairwise {ps : List (HPath k)}
    (hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset)) :
    (unwindVerts ps).Nodup := by
  -- symmetric extraction of disjointness for any two distinct list members
  haveI : Std.Symm (fun a b : HPath k => Disjoint a.vertsFinset b.vertsFinset) :=
    ⟨fun a b h => h.symm⟩
  rw [unwindVerts, List.nodup_append']
  refine ⟨?_, ?_, ?_⟩
  · -- (A) the firsts are pairwise distinct
    rw [show ((ps.map HPath.first).Nodup) = ((ps.map HPath.first).Pairwise (· ≠ ·)) from rfl,
      List.pairwise_map]
    refine hpair.imp ?_
    intro p q hd heq
    have : p.first ∈ q.vertsFinset := by rw [heq]; exact HPath.mem_vertsFinset.mpr q.first_mem
    exact Finset.disjoint_left.mp hd (HPath.mem_vertsFinset.mpr p.first_mem) this
  · -- (B) the reversed remainders flatten to a nodup list
    rw [List.nodup_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      rw [List.mem_map] at hl
      obtain ⟨p, _, rfl⟩ := hl
      exact p.nodup.sublist (List.drop_sublist 1 p.verts)
    · rw [List.pairwise_map, List.pairwise_reverse]
      refine hpair.imp ?_
      intro p q hd a haq hap
      have hap' : a ∈ p.verts := List.mem_of_mem_drop hap
      have haq' : a ∈ q.verts := List.mem_of_mem_drop haq
      exact Finset.disjoint_left.mp hd (HPath.mem_vertsFinset.mpr hap')
        (HPath.mem_vertsFinset.mpr haq')
  · -- (C) firsts are disjoint from the remainders
    intro a ha hfl
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    simp only [List.mem_flatten, List.mem_map] at hfl
    obtain ⟨l, ⟨q, hq, rfl⟩, hal⟩ := hfl
    have hq' : q ∈ ps := List.mem_reverse.mp hq
    have hal' : p.first ∈ q.verts := List.mem_of_mem_drop hal
    by_cases hpq : p = q
    · subst hpq
      exact first_not_mem_drop1 p hal
    · exact Finset.disjoint_left.mp (hpair.forall hp hq' hpq)
        (HPath.mem_vertsFinset.mpr p.first_mem) (HPath.mem_vertsFinset.mpr hal')

end Hunter.ProofsUnwind4

namespace Hunter.Proved

open Hunter.ProofsUnwind
open scoped Classical

variable {k : ℕ}

/-- **`prp_Xk_se_sufficiency`, verbatim (`2 ≤ k`).**  `main_version.tex` §5 l.315, ⟸: if
`V(X) = V(𝒮_k)` and `Comps(X)` is a set of strongly exitless paths, then `X ∈ 𝒳_k`.

This is the paper's "unwinding" `P(p₁,…,pₙ)` construction (`ADD DIAGRAM`), fully formalized:
`prp_Xk_se_sufficiency_unwind3` (`ProofsUnwind3.lean`) does the edge-accounting given a list
`ps` of pairwise vertex-disjoint SE paths covering `𝒮_k` whose edges union to `X`; here we
build that list by picking one path witness per weak component of `X` (`Comps X`) and discharge
all six of its hypotheses from `hspan`+`hse`.

**AMENDED from paper: added guard `2 ≤ k`** (consistent with `prp_Xk_se_necessity`'s
`2 ≤ k` amendment; the verbatim statement is degenerate for `k ≤ 1`, where `𝒮_k` has `≤ 1`
vertex).  See `PROGRESS-unwind4.md`. -/
theorem prp_Xk_se_sufficiency (hk : 2 ≤ k) {X : Finset (Vtx k × Vtx k)}
    (hspan : vertsOf X = Finset.univ) (hse : IsUnionOfStronglyExitlessPaths X) :
    X ∈ Xk k := by
  classical
  haveI := ProofsSpine.vtx_nonempty k
  -- the ordered list of component path-witnesses
  set ps : List (HPath k) := (Comps X).attach.toList.map (fun C => (hse C.1 C.2).choose)
    with hps_def
  -- forward membership: each `p ∈ ps` is the chosen witness for some component
  have hmem_ps : ∀ p ∈ ps, ∃ (C : Finset (Vtx k)) (hC : C ∈ Comps X),
      p = (hse C hC).choose ∧ p.vertsFinset = C ∧ IsPathComponent p X ∧ p.StronglyExitless := by
    intro p hp
    rw [hps_def, List.mem_map] at hp
    obtain ⟨⟨C, hC⟩, _, rfl⟩ := hp
    obtain ⟨hV, hPC, hSE⟩ := (hse C hC).choose_spec
    exact ⟨C, hC, rfl, hV, hPC, hSE⟩
  -- reverse membership: the witness for any component lies in `ps`
  have hmem_f : ∀ (C : Finset (Vtx k)) (hC : C ∈ Comps X), (hse C hC).choose ∈ ps := by
    intro C hC
    rw [hps_def, List.mem_map]
    exact ⟨⟨C, hC⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩
  -- `Comps X` is nonempty (`vertsOf X = univ` is nonempty)
  have hvne : (vertsOf X).Nonempty := by rw [hspan]; exact Finset.univ_nonempty
  have hCne : (Comps X).Nonempty := by rw [Comps]; exact hvne.image _
  -- (hps) nonempty list
  have hps : ps ≠ [] := by
    rw [hps_def, Ne, List.map_eq_nil_iff, Finset.toList_eq_nil, Finset.attach_eq_empty_iff]
    exact hCne.ne_empty
  -- (hSE) each is strongly exitless
  have hSE : ∀ p ∈ ps, p.StronglyExitless := fun p hp => (hmem_ps p hp).choose_spec.choose_spec.2.2.2
  -- (hpair) pairwise vertex-disjoint (distinct components are disjoint)
  have hpair : ps.Pairwise (fun p q : HPath k => Disjoint p.vertsFinset q.vertsFinset) := by
    rw [hps_def, List.pairwise_map]
    refine (Finset.nodup_toList _).imp ?_
    rintro ⟨C, hC⟩ ⟨C', hC'⟩ hne
    have hCC' : C ≠ C' := fun h => hne (Subtype.ext h)
    rw [(hse C hC).choose_spec.1, (hse C' hC').choose_spec.1]
    exact ProofsWP.comps_disjoint hC hC' hCC'
  -- (hcover) every vertex lies in some component-path
  have hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts := by
    intro v
    have hvV : v ∈ vertsOf X := by rw [hspan]; exact Finset.mem_univ v
    have hblk : ProofsWP.block X v ∈ Comps X := ProofsWP.block_mem_comps hvV
    refine ⟨(hse _ hblk).choose, hmem_f _ hblk, ?_⟩
    rw [← HPath.mem_vertsFinset, (hse _ hblk).choose_spec.1]
    exact ProofsWP.self_mem_block hvV
  -- (hnd) the unwinding vertex list is nodup
  have hnd : (unwindVerts ps).Nodup := ProofsUnwind4.unwindVerts_nodup_of_pairwise hpair
  -- (hXdef) `X` is the union of the component edge-sets
  have hXdef : ∀ e, e ∈ X ↔ ∃ p ∈ ps, e ∈ p.edges := by
    intro e
    constructor
    · intro heX
      have h1V : e.1 ∈ vertsOf X := ProofsWP.mem_vertsOf.mpr ⟨e, heX, Or.inl rfl⟩
      have hblk : ProofsWP.block X e.1 ∈ Comps X := ProofsWP.block_mem_comps h1V
      obtain ⟨hVeq, hPC, _⟩ := (hse _ hblk).choose_spec
      refine ⟨(hse _ hblk).choose, hmem_f _ hblk, ?_⟩
      have h1p : e.1 ∈ (hse _ hblk).choose.vertsFinset := by
        rw [hVeq]; exact ProofsWP.self_mem_block h1V
      exact hPC.2.2 e heX h1p
    · rintro ⟨p, hp, hep⟩
      obtain ⟨C, hC, _, _, hPC, _⟩ := hmem_ps p hp
      exact hPC.1 hep
  exact prp_Xk_se_sufficiency_unwind3 hps hnd hcover hSE hk hpair hXdef

/-! ## Downstream compositions (`prp_Xkcomps`, `red_pstar`)

`prp_Xk_se_sufficiency` above is the FULL (multi-path) sufficiency.  The reductions track needs
the **single-path corollary** `hrev : {SE paths} ⊆ 𝒳'_k` — that *every* strongly exitless path
`p` is a path-component of *some* `X ∈ 𝒳_k`.  For a spanning `p` this is `X = E(p)`; for a
non-spanning `p` it needs a spanning cover `X = E(p) ∪ ⋃(orbit paths on 𝒮_k ∖ V(p))`, whose
weak components are exactly `p` together with the added orbit-paths — a genuine second
construction (the complement-cover + component-identification) that also rests on the still-open
`bridge_se_cycles`/orbit-partition facts.  It is therefore **not** discharged here and is carried
as the explicit hypothesis `hrev`, exactly as in `ProofsB2.prp_Xkcomps_amended` /
`red_pstar_tightened`.  These `_final` re-exports pin down the minimal remaining interface. -/

/-- **prp-Xkcomps (final)** — `𝒳'_k = {strongly exitless paths}`.  `⊆` is proved outright
(`ProofsB2.Xkcomps_subset`); `⊇` is `hrev` (the single-path unwinding corollary — the only
remaining input).  Guard `2 ≤ k`. -/
theorem prp_Xkcomps_final (hk : 2 ≤ k)
    (hrev : {p : HPath k | p.StronglyExitless} ⊆ Xk' k) :
    Xk' k = {p : HPath k | p.StronglyExitless} :=
  prp_Xkcomps_amended hk hrev

/-- **red-p\* (final)** — take23's `≥`-reduction, with `prp_Xkcomps` discharged (down to `hrev`)
and `𝒳'_k`-nonemptiness reduced to `𝒳_k`-nonemptiness.  Remaining hypotheses: `1 < r`, `2 ≤ k`,
`hrev` (the single-path unwinding corollary), `hne_Xk` (`𝒳_k` nonempty). -/
theorem red_pstar_final {r : ℝ} (hr : 1 < r) (hk : 2 ≤ k)
    (hrev : {p : HPath k | p.StronglyExitless} ⊆ Xk' k) (hne_Xk : (Xk k).Nonempty) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
  red_pstar_tightened hr hk hrev hne_Xk

end Hunter.Proved


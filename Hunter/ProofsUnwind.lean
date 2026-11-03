/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsPathrule

/-!
# The unwinding construction (Hunter §5, `prp-Xk-se` sufficiency)

Target: `prp_Xk_se_sufficiency` — given `V(X) = V(𝒮_k)` and `Comps(X)` a set of strongly
exitless paths, construct a Hamiltonian `P` with `F(P) = X`, i.e. `X ∈ 𝒳_k`.

The paper marks the construction "ADD DIAGRAM" and never writes the proof.  This file:

* proves the **base case fully** (`prp_Xk_se_sufficiency_single`): when `|Comps(X)| ≤ 1`,
  `X` is itself a strongly exitless Hamiltonian path `p`, and `F(p) = X` — verbatim the
  paper's `|Comp(X)| = 1` special case.  The engine is `sset_empty_of_stronglyExitless`
  (`S(p) = ∅` for a strongly exitless Hamiltonian path), a reusable structural lemma.

* builds the general **unwinding vertex list** and the derived facts (see the later
  sections), reducing the full theorem to an explicitly named residual.

See `PROGRESS-unwind.md` for the fallback level reached and the ordering convention.
-/

namespace Hunter.ProofsUnwind

open List
open scoped Classical

variable {k : ℕ}

/-! ## Block starts are first-in-cycle (the normal-form crux) -/

/-- For an exitless path, the start of a **complete** block (`k ∣ B`, `B + k ≤ |p|`) is the
`P.pos`-earliest vertex of its 1-cycle — i.e. it is `firstInCycle`.  This is the reason the
paper's `p_i[1]` become `C₀` vertices in the unwinding, and the reason `S(p) = ∅`. -/
theorem firstInCycle_block_start (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {B : ℕ} (hdvd : k ∣ B) (hB : B + k ≤ p.numVerts) :
    firstInCycle p (p.vert B) := by
  intro u hu
  have hBlt : B < p.numVerts := by omega
  rw [ProofsExitless.pos_vert p hBlt]
  by_cases hmem : u ∈ p.verts
  · -- `u = p.vert j`, `j := pos u`
    set j := p.pos u with hj
    have hjlt : j < p.numVerts := ProofsExitless.pos_lt p hmem
    have hvj : p.vert j = u := ProofsExitless.vert_pos p hmem
    by_contra hlt
    push Not at hlt  -- `j < B`
    -- block of `j`
    set B'' := k * (j / k) with hB''
    have hB''dvd : k ∣ B'' := ⟨j / k, hB''⟩
    have hjmod : k * (j / k) + j % k = j := Nat.div_add_mod j k
    have hBB : k * (B / k) = B := Nat.mul_div_cancel' hdvd
    have hquot : j / k < B / k := by
      by_contra hc
      push Not at hc
      have h1 : k * (B / k) ≤ k * (j / k) := Nat.mul_le_mul_left k hc
      omega
    have hB''k : B'' + k ≤ B := by
      have h2 : k * (j / k + 1) ≤ k * (B / k) := Nat.mul_le_mul_left k hquot
      have : k * (j / k) + k = k * (j / k + 1) := by ring
      omega
    have hnre := ProofsExitless.no_reentry hk hp hB''dvd hB''k hBlt
    -- but `rotClass (p.vert B'') = rotClass u = rotClass (p.vert B)` — contradiction
    apply hnre
    have hjstruct := ProofsExitless.vert_eq_sigma_iter hk hp j hjlt
    have hrc_j : rotClass (p.vert j).1 = rotClass (p.vert B'').1 := by
      rw [hjstruct, ProofsExitless.rotClass_sigma_iter]
    have hrc_u : rotClass u.1 = rotClass (p.vert B'').1 := by rw [← hvj]; exact hrc_j
    rw [hrc_u] at hu
    exact hu
  · rw [ProofsExitless.pos_of_not_mem p hmem]
    omega

/-! ## `S(p) = ∅` for a strongly exitless Hamiltonian path -/

/-- **Base of the unwinding.**  For a strongly exitless **Hamiltonian** path `p`, the
S-construction set `S(p)` is empty: every vertex either already carries its 1-edge inside
`p` (block-interior vertices) or lies in `C₋₁` (block-end vertices, whose `σ` is the
`C₀`/first-in-cycle vertex).  Hence `F(p) = p.edges` (see `F_eq_edges_of_sset_empty`). -/
theorem sset_empty_of_stronglyExitless (hk : 1 ≤ k) {p : HPath k}
    (hham : p.IsHamiltonian) (hp : p.StronglyExitless) : Sset p = ∅ := by
  rw [Sset, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨-, hvC, hedge⟩ := hv
  -- position of `v`
  set i := p.pos v with hi
  have hmem : v ∈ p.verts := hham v
  have hilt : i < p.numVerts := ProofsExitless.pos_lt p hmem
  have hvi : p.vert i = v := ProofsExitless.vert_pos p hmem
  by_cases hdvd : k ∣ (i + 1)
  · -- block end: show `v ∈ C₋₁` (i.e. `σ v ∈ C₀`), contradicting `v ∉ C₋₁`
    apply hvC
    rw [Cm1, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- `σ v = p.vert B` with `B = k*(i/k)` a complete block start
    set B := k * (i / k) with hB
    have hBdvd : k ∣ B := ⟨i / k, hB⟩
    have himod : i % k = k - 1 := ProofsExitless.mod_eq_pred_of_dvd_succ hk hdvd
    have hiB : B + (k - 1) = i := by
      have hdm := Nat.div_add_mod i k; rw [← hB] at hdm; omega
    have hBk : B + k ≤ p.numVerts := by omega
    -- compute `σ v`
    have hstruct := ProofsExitless.vert_eq_sigma_iter hk hp.1 i hilt
    rw [himod, ← hB] at hstruct
    -- `v = σ^[k-1] (p.vert B)`
    have hv_eq : v = sigma^[k - 1] (p.vert B) := by rw [← hvi]; exact hstruct
    have hsig : sigma v = p.vert B := by
      rw [hv_eq, Proved.sigma_iter_succ' (k - 1) (p.vert B),
        show k - 1 + 1 = k from by omega, ProofsExitless.sigma_iter_period]
    rw [ProofsPathrule.mem_C0_iff, hsig]
    exact firstInCycle_block_start hk hp.1 hBdvd hBk
  · -- block interior: `(v → σ v) ∈ p.edges`, contradicting `hedge`
    apply hedge
    -- `i + 1 < |p|`: else `i+1 = |p|`, but `k ∣ |p|`, so `k ∣ (i+1)`, contradiction
    have hi1 : i + 1 < p.numVerts := by
      rcases Nat.lt_or_ge (i + 1) p.numVerts with h | h
      · exact h
      · exfalso
        have hle : p.numVerts ≤ i + 1 := h
        have : i + 1 = p.numVerts := by omega
        exact hdvd (this ▸ Proved.dvd_numVerts_of_stronglyExitless hk hp)
    have hsucc := ProofsExitless.vert_succ hk hp.1 hi1 hdvd
    have hedgemem := ProofsStructure.vert_consec_mem_edges hi1
    rw [hsucc, hvi] at hedgemem
    exact hedgemem

/-! ## `f(P, ∅) = E(P)` and `F(p) = E(p)` for exitless-Hamiltonian `p` -/

/-- The transformation with an empty `S` is the identity on the edge set (Step 1 removes and
adds nothing; Step 2 has no doubles because a path has in-degree `≤ 1`). -/
theorem fPS_empty (p : HPath k) : fPS p (∅ : Finset (Vtx k)) = p.edges := by
  have hE1 : E1removed p ∅ = ∅ := by
    rw [E1removed]; apply Finset.filter_false_of_mem
    intro e _; exact Finset.notMem_empty _
  have hadd : addedEdges (∅ : Finset (Vtx k)) = ∅ := by rw [addedEdges, Finset.image_empty]
  have hstep1 : Xstep1 p ∅ = p.edges := by
    rw [Xstep1, hE1, hadd, Finset.sdiff_empty, Finset.union_empty]
  have hdbl : doubles p ∅ = ∅ := by
    rw [doubles]; apply Finset.filter_false_of_mem
    intro u _; rw [hstep1]
    have := ProofsSpine.path_into_le_one p u; omega
  have hE2 : E2removed p ∅ = ∅ := by
    rw [E2removed, hdbl]; apply Finset.filter_false_of_mem
    intro e _; exact Finset.notMem_empty _
  rw [fPS, hstep1, hE2, Finset.sdiff_empty]

/-- For a strongly exitless **Hamiltonian** path, `F` fixes it: `F(p) = E(p)`. -/
theorem F_eq_edges_of_sset_empty (hk : 1 ≤ k) {p : HPath k}
    (hham : p.IsHamiltonian) (hp : p.StronglyExitless) : F p = p.edges := by
  rw [F, sset_empty_of_stronglyExitless hk hham hp, fPS_empty]

end Hunter.ProofsUnwind

/-! ## Delivered target — the single-component (`|Comps(X)| ≤ 1`) base case -/

namespace Hunter.Proved

open Hunter.ProofsUnwind
open scoped Classical

variable {k : ℕ}

/-- **`prp_Xk_se_sufficiency`, base case (`|Comps(X)| ≤ 1`), PROVED.**  This is the paper's
own `|Comp(X)| = 1` special case (`main_version.tex` l.487): if `X` spans `𝒮_k` and its
single component is a strongly exitless path `p`, then `p` is a strongly exitless
*Hamiltonian* path with `E(p) = X`, so `X = E(p) = F(p) ∈ 𝒳_k`.

Guarded by `1 ≤ k` (the `k = 0` alphabet is degenerate — `Vtx 0` is a singleton and the
verbatim statement is vacuous there; the paper's regime is `k ≥ 3`, and the pathrule track
already amends the companion `necessity` direction to `2 ≤ k`). -/
theorem prp_Xk_se_sufficiency_single (hk : 1 ≤ k)
    {X : Finset (Vtx k × Vtx k)}
    (hspan : vertsOf X = Finset.univ) (hse : IsUnionOfStronglyExitlessPaths X)
    (hone : numComps X ≤ 1) : X ∈ Xk k := by
  haveI := ProofsSpine.vtx_nonempty k
  -- `Comps X` is nonempty (it is the image of the nonempty `vertsOf X = univ`)
  have hvne : (vertsOf X).Nonempty := by rw [hspan]; exact Finset.univ_nonempty
  have hCompNe : (Comps X).Nonempty := by
    rw [Comps]; exact hvne.image _
  obtain ⟨C, hCmem⟩ := hCompNe
  obtain ⟨p, hpV, hpPC, hpSE⟩ := hse C hCmem
  -- the single component covers everything: `C = univ`
  have hCuniv : C = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    have hwV : w ∈ vertsOf X := by rw [hspan]; exact Finset.mem_univ w
    set blk := (vertsOf X).filter (fun u => weakConn X w u) with hblkdef
    have hblkmem : blk ∈ Comps X := by
      rw [Comps]; exact Finset.mem_image.mpr ⟨w, hwV, rfl⟩
    have hCeq : C = blk := Finset.card_le_one.mp hone C hCmem blk hblkmem
    have hwblk : w ∈ blk := by
      rw [hblkdef, Finset.mem_filter]
      exact ⟨hwV, Relation.ReflTransGen.refl⟩
    rw [hCeq]; exact hwblk
  -- hence `p` is Hamiltonian
  have hVuniv : p.vertsFinset = Finset.univ := by rw [hpV, hCuniv]
  have hham : p.IsHamiltonian := by
    intro v
    exact HPath.mem_vertsFinset.mp (by rw [hVuniv]; exact Finset.mem_univ v)
  -- and `E(p) = X`
  have hmemV : ∀ e : Vtx k × Vtx k, e.1 ∈ p.vertsFinset := by
    intro e; rw [hVuniv]; exact Finset.mem_univ _
  have hXsub : X ⊆ p.edges := fun e he => hpPC.2.2 e he (hmemV e)
  have hedgesX : p.edges = X := Finset.Subset.antisymm hpPC.1 hXsub
  -- conclude `X ∈ 𝒳_k` via `P = p`
  refine ⟨p, hham, ?_⟩
  rw [F_eq_edges_of_sset_empty hk hham hpSE, hedgesX]

end Hunter.Proved

/-! ## The general unwinding construction `P(p₁,…,pₙ)` (`main_version.tex` l.489)

The paper builds `P` from an *arbitrary* ordering `p₁,…,pₙ` of `Comps(X)` by the edge-set
formula
`E(P) = ⋃ᵢ E(pᵢ) ∖ ⋃_{i<n}{(pᵢ[1]→pᵢ[2])} ∪ ⋃_{i<n}{(pᵢ[1]→p_{i+1}[1]),(p_{i+1}[|p_{i+1}|]→pᵢ[2])}`.

Reading that edge set back as a **single Hamiltonian vertex walk** pins the ordering
convention the paper leaves implicit (its "ADD DIAGRAM"):

    P = p₁[1], p₂[1], …, pₙ[1],          -- the tails, in the given order (the added
        pₙ[2..|pₙ|], p_{n-1}[2..], …, p₁[2..]   -- `pᵢ[1]→p_{i+1}[1]` chain), then each
                                          -- component's remainder, in *reverse* order
                                          -- (the added `p_{i+1}[last]→pᵢ[2]` back-links).

`unwindVerts` below is exactly this list.  Concretely: the *head block* is the list of
first-vertices in forward order; the *tail block* is `drop 1` of each component's vertex
list, concatenated in reverse component order.  This is a bijective rearrangement of the
disjoint union of the `pᵢ`'s vertex lists, so it is Hamiltonian (`unwind_isHamiltonian`)
whenever the components cover `V(𝒮_k)`, and duplicate-free whenever they are disjoint. -/

namespace Hunter.ProofsUnwind

open List
open scoped Classical

variable {k : ℕ}

/-- The unwinding vertex list `P(p₁,…,pₙ)`: forward first-vertices, then reversed
component-remainders.  See the section comment for the exact form. -/
def unwindVerts (ps : List (HPath k)) : List (Vtx k) :=
  ps.map HPath.first ++ (ps.reverse.map (fun p => p.verts.drop 1)).flatten

/-- Membership in the unwinding: `v` occurs iff it occurs in some component. -/
theorem mem_unwindVerts {ps : List (HPath k)} {v : Vtx k} :
    v ∈ unwindVerts ps ↔ ∃ p ∈ ps, v ∈ p.verts := by
  rw [unwindVerts, List.mem_append, List.mem_flatten]
  constructor
  · rintro (h | ⟨l, hl, hvl⟩)
    · rw [List.mem_map] at h
      obtain ⟨p, hp, rfl⟩ := h
      exact ⟨p, hp, p.first_mem⟩
    · rw [List.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      exact ⟨p, List.mem_reverse.mp hp, List.mem_of_mem_drop hvl⟩
  · rintro ⟨p, hp, hv⟩
    -- decompose `p.verts = p.first :: (drop 1 p.verts)`
    obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil p.ne
    have hfirst : p.first = a := ProofsSpine.first_eq hat
    have hdrop : p.verts.drop 1 = t := by rw [hat, List.drop_one, List.tail_cons]
    rw [hat, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inl (List.mem_map.mpr ⟨p, hp, hfirst⟩)
    · refine Or.inr ⟨p.verts.drop 1, ?_, by rw [hdrop]; exact hv⟩
      exact List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩

/-- The unwinding list is nonempty when there is at least one component. -/
theorem unwindVerts_ne {ps : List (HPath k)} (hps : ps ≠ []) : unwindVerts ps ≠ [] := by
  cases ps with
  | nil => exact absurd rfl hps
  | cons a t => simp [unwindVerts]

/-- The unwinding as an `HPath`, given the (genuine, discharge-able-from-disjointness)
well-formedness data: a nonempty component list and a duplicate-free vertex list. -/
def unwindP (ps : List (HPath k)) (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup) : HPath k where
  verts := unwindVerts ps
  ne := unwindVerts_ne hps
  nodup := hnd

/-- **The unwinding is Hamiltonian** whenever the components cover `V(𝒮_k)`.  (This is the
one non-trivial fact about the *vertex list* of `P(p₁,…,pₙ)`; it needs nothing about the
ordering.) -/
theorem unwind_isHamiltonian {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts) :
    (unwindP ps hps hnd).IsHamiltonian := by
  intro v
  show v ∈ unwindVerts ps
  exact mem_unwindVerts.mpr (hcover v)

end Hunter.ProofsUnwind

namespace Hunter.Proved

open Hunter.ProofsUnwind
open scoped Classical

variable {k : ℕ}

/-- **`prp_Xk_se_sufficiency`, general case — reduced to the paper's unproven residual.**

Given an ordering `ps` of the components as strongly exitless paths that (i) covers
`V(𝒮_k)` and (ii) is duplicate-free as a vertex list, the unwinding `unwindP ps` is a
Hamiltonian path; if additionally its `F`-image is `X` — the paper's asserted-but-unproven
`F(P) = X` (the "ADD DIAGRAM" step, `main_version.tex` l.492–494) — then `X ∈ 𝒳_k`.

The two well-formedness hypotheses `hps`/`hnd`/`hcover` are discharge-able from the fact
that `Comps(X)` is a disjoint cover of `V(X) = V(𝒮_k)` (see `PROGRESS-unwind.md`); the sole
mathematical gap is `hFPX`, which is precisely the content the paper omits. -/
theorem prp_Xk_se_sufficiency_unwind {X : Finset (Vtx k × Vtx k)}
    {ps : List (HPath k)} (hps : ps ≠ [])
    (hnd : (unwindVerts ps).Nodup)
    (hcover : ∀ v : Vtx k, ∃ p ∈ ps, v ∈ p.verts)
    (hFPX : F (unwindP ps hps hnd) = X) : X ∈ Xk k :=
  ⟨unwindP ps hps hnd, unwind_isHamiltonian hps hnd hcover, hFPX⟩

end Hunter.Proved


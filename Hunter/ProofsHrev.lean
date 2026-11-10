/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsUnwind4
import Hunter.ProofsPu

/-!
# The single-path corollary `hrev` — every strongly exitless path is a component (Hunter §5)

`Hunter/ProofsUnwind4.lean` proved the FULL (multi-path) sufficiency
`prp_Xk_se_sufficiency`, and `prp_Xk_se_sufficiency_unwind3` gives `X ∈ 𝒳_k` from an explicit
list `ps` of pairwise vertex-disjoint strongly-exitless paths covering `𝒮_k` whose edges union
to `X`.  This file supplies the remaining **single-path corollary**

  `hrev : {p | p.StronglyExitless} ⊆ 𝒳'_k`  (guarded by `2 ≤ k`),

the paper's `P(p₁,…,pₙ)` "unwinding" specialized to realizing an *arbitrary* (non-spanning)
strongly-exitless path as a path-component of some `X ∈ 𝒳_k`.

## The construction

A strongly exitless `p` is a disjoint union of full 1-cycles (`clm_1cyclesubset`), so its
vertex complement `V(𝒮_k) ∖ V(p)` is again a union of full 1-cycles.  We cover the complement
with one **orbit path** per complement 1-cycle (`orbitList`, the single-cycle traversal
`[u, σu, …, σ^{k−1}u]`, which is strongly exitless).  Then `ps = p :: (orbit paths)` is a
spanning, pairwise vertex-disjoint strongly-exitless family; `X := ⋃ E(pᵢ)` lies in `𝒳_k` by
`prp_Xk_se_sufficiency_unwind3`.  Since the orbit edges are vertex-disjoint from `E(p)`, the
weak component of `X` on `V(p)` is exactly `p`, i.e. `IsPathComponent p X`, so `p ∈ 𝒳'_k`.

Delivered with the `2 ≤ k` guard (consistent with `prp_Xk_se_sufficiency`).  Zero `sorry`,
zero new axioms.  See `PROGRESS-hrev.md`.
-/

namespace Hunter.ProofsHrev

open List Hunter
open scoped Classical

variable {k : ℕ}

/-! ## The orbit path — a single 1-cycle as a strongly-exitless `HPath` -/

/-- `orbitList u = [u, σu, …, σ^{k−1}u]` is nonempty (length `k ≥ 1`). -/
theorem orbitList_ne (hk : 1 ≤ k) (u : Vtx k) : ProofsPu.orbitList u ≠ [] := by
  intro h
  have hl : (ProofsPu.orbitList u).length = k := ProofsPu.orbitList_length u
  rw [h, List.length_nil] at hl; omega

/-- The single-cycle **orbit path** `[u, σu, …, σ^{k−1}u]`. -/
noncomputable def orbitPath (hk : 1 ≤ k) (u : Vtx k) : HPath k :=
  ⟨ProofsPu.orbitList u, orbitList_ne hk u, ProofsPu.orbitList_nodup hk u⟩

theorem orbitPath_numVerts (hk : 1 ≤ k) (u : Vtx k) :
    (orbitPath hk u).numVerts = k := ProofsPu.orbitList_length u

theorem orbitPath_vert (hk : 1 ≤ k) (u : Vtx k) {i : ℕ} (hi : i < k) :
    (orbitPath hk u).vert i = sigma^[i] u := by
  have hi' : i < (ProofsPu.orbitList u).length := by rw [ProofsPu.orbitList_length]; exact hi
  have ht : i < (orbitPath hk u).numVerts := by
    show i < (ProofsPu.orbitList u).length; exact hi'
  rw [ProofsExitless.vert_getElem (orbitPath hk u) ht]
  exact ProofsPu.orbitList_getElem u hi'

/-- `V(orbit path u) = c(u)`, the 1-cycle of `u`. -/
theorem orbitPath_vertsFinset (hk : 1 ≤ k) (u : Vtx k) :
    (orbitPath hk u).vertsFinset = cyc u := by
  ext x
  rw [HPath.mem_vertsFinset]
  show x ∈ ProofsPu.orbitList u ↔ x ∈ cyc u
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := ProofsPu.mem_orbitList hx
    exact ProofsExitless.sigma_iter_mem_cyc i u
  · intro hx
    obtain ⟨r, hr, rfl⟩ := (ProofsExitless.mem_cyc_iff_exists hk).mp hx
    simp only [ProofsPu.orbitList, List.mem_map, List.mem_range]
    exact ⟨r, hr, rfl⟩

theorem orbitPath_exitless (hk : 1 ≤ k) (u : Vtx k) : (orbitPath hk u).Exitless := by
  rw [HPath.Exitless]
  rintro ⟨i, hi1, hw, _⟩
  rw [orbitPath_numVerts hk u] at hi1
  have hik : i < k := by omega
  have hik1 : i + 1 < k := hi1
  rw [orbitPath_vert hk u hik, orbitPath_vert hk u hik1,
    Function.iterate_succ_apply' sigma i u, ew_sigma hk] at hw
  omega

theorem orbitPath_SE (hk : 1 ≤ k) (u : Vtx k) : (orbitPath hk u).StronglyExitless := by
  refine ⟨orbitPath_exitless hk u, ?_⟩
  -- `σ(last) ∈ c(u) = V(orbit path u)`
  have hlast_mem : (orbitPath hk u).last ∈ (orbitPath hk u).verts := (orbitPath hk u).last_mem
  have hlast_cyc : (orbitPath hk u).last ∈ cyc u := by
    rw [← orbitPath_vertsFinset hk u]; exact HPath.mem_vertsFinset.mpr hlast_mem
  have hrc : rotClass ((orbitPath hk u).last).1 = rotClass u.1 := ProofsExitless.mem_cyc.mp hlast_cyc
  have hsig : sigma ((orbitPath hk u).last) ∈ (orbitPath hk u).vertsFinset := by
    rw [orbitPath_vertsFinset hk u, ProofsExitless.mem_cyc, ProofsStructure.rotClass_sigma]
    exact hrc
  exact HPath.mem_vertsFinset.mp hsig

/-! ## Canonical 1-cycle representatives (choosing one orbit per complement cycle) -/

/-- Nonemptiness of a 1-cycle (`u ∈ c(u)`). -/
theorem cyc_nonempty (u : Vtx k) : (cyc u).Nonempty := ⟨u, ProofsExitless.mem_cyc.mpr rfl⟩

/-- If `x` lies in `c(u)` then `c(x) = c(u)` (1-cycles are equivalence classes). -/
theorem cyc_eq_of_mem {x u : Vtx k} (h : x ∈ cyc u) : cyc x = cyc u := by
  have hr : rotClass x.1 = rotClass u.1 := ProofsExitless.mem_cyc.mp h
  simp only [cyc, hr]

/-- Distinct 1-cycles are disjoint. -/
theorem cyc_disjoint_of_ne {a b : Vtx k} (h : cyc a ≠ cyc b) : Disjoint (cyc a) (cyc b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact h ((cyc_eq_of_mem hxa).symm.trans (cyc_eq_of_mem hxb))

/-- A canonical vertex of a finset (its `choose` when nonempty, else the fallback `v₀`).  As a
function of the *finset value*, it is automatically constant on equal finsets. -/
noncomputable def repF (v₀ : Vtx k) (s : Finset (Vtx k)) : Vtx k :=
  if h : s.Nonempty then h.choose else v₀

/-- The chosen representative of `c(u)` lies in `c(u)`. -/
theorem repF_mem (v₀ u : Vtx k) : repF v₀ (cyc u) ∈ cyc u := by
  have h := cyc_nonempty u
  simp only [repF, dif_pos h]
  exact h.choose_spec

/-- If `p` is a union of full 1-cycles, the 1-cycle of any complement vertex avoids `V(p)`. -/
theorem compl_cyc_disjoint {p : HPath k} (huoc : p.IsUnionOfCycles) {w : Vtx k}
    (hw : w ∉ p.vertsFinset) : Disjoint (cyc w) p.vertsFinset := by
  rw [Finset.disjoint_left]
  intro x hxw hxp
  have hxpv : x ∈ p.verts := HPath.mem_vertsFinset.mp hxp
  have hsub : cyc x ⊆ p.vertsFinset := huoc x hxpv
  have hcxw : cyc x = cyc w := cyc_eq_of_mem hxw
  have hwcyc : w ∈ cyc w := ProofsExitless.mem_cyc.mpr rfl
  rw [← hcxw] at hwcyc
  exact hw (hsub hwcyc)

/-- Edge endpoints of a path lie in its vertex list. -/
theorem edge_endpoints_mem {p : HPath k} {e : Vtx k × Vtx k} (he : e ∈ p.edges) :
    e.1 ∈ p.verts ∧ e.2 ∈ p.verts := by
  rw [ProofsSpine.mem_edges_iff] at he
  obtain ⟨a, b⟩ := e
  obtain ⟨h1, h2⟩ := List.of_mem_zip he
  exact ⟨h1, List.mem_of_mem_tail h2⟩

/-- `2 * k ≤ k!` for `k ≥ 3` (so a `k`-vertex orbit path is non-spanning: `k ≤ k! − k`). -/
theorem two_k_le_factorial (hk : 3 ≤ k) : 2 * k ≤ k.factorial := by
  induction k with
  | zero => omega
  | succ n ih =>
    rw [Nat.factorial_succ]
    rcases Nat.lt_or_ge 3 (n + 1) with h | h
    · have hn : 3 ≤ n := by omega
      have ihn : 2 * n ≤ n.factorial := ih hn
      nlinarith [ihn, Nat.self_le_factorial n]
    · have hn2 : n = 2 := by omega
      subst hn2; decide

end Hunter.ProofsHrev

/-! ## Target 1 — `hrev`: every strongly exitless path is a path-component of some `X ∈ 𝒳_k` -/

namespace Hunter.Proved

open List Hunter Hunter.ProofsUnwind Hunter.ProofsHrev
open scoped Classical

variable {k : ℕ}

/-- **`hrev` — the single-path unwinding corollary (`2 ≤ k`).**  Every strongly exitless path
`p` is a path-component of some `X ∈ 𝒳_k`, i.e. `p ∈ 𝒳'_k`.  This is the last leaf of the
reduction side: it discharges the `hrev` hypothesis carried by `prp_Xkcomps_amended`,
`red_pstar_tightened`, and `Xk'_nonempty_of_Xk_nonempty`.

Construction: `p` is a disjoint union of full 1-cycles, so `V(𝒮_k) ∖ V(p)` is covered by orbit
paths (single 1-cycles); `ps = p :: (orbit paths)` is a spanning pairwise-disjoint SE family,
`X := ⋃ E(pᵢ) ∈ 𝒳_k` by `prp_Xk_se_sufficiency_unwind3`, and `p` is a component of `X` because
the orbit edges are vertex-disjoint from `E(p)`.

**Guard `2 ≤ k`** (consistent with `prp_Xk_se_sufficiency`; for `2 ≤ k` a strongly exitless
path has `≥ k ≥ 2` vertices, so no degenerate single-vertex cases arise). -/
theorem hrev (hk : 2 ≤ k) : {p : HPath k | p.StronglyExitless} ⊆ Xk' k := by
  intro p hp
  have hSE : p.StronglyExitless := hp
  have hk1 : 1 ≤ k := by omega
  have huoc : p.IsUnionOfCycles := Hunter.Proved.clm_1cyclesubset hSE
  -- complement of `V(p)`, and one canonical orbit-representative per complement 1-cycle
  set comp : Finset (Vtx k) := Finset.univ \ p.vertsFinset with hcomp
  set reps : Finset (Vtx k) := comp.image (fun u => repF p.first (cyc u)) with hreps
  set orbitPaths : List (HPath k) := reps.toList.map (orbitPath hk1) with horb
  set ps : List (HPath k) := p :: orbitPaths with hps_def
  -- every representative is idempotent (`rep(c(rep)) = rep`) and lies in the complement
  have hrep_idem : ∀ r ∈ reps, repF p.first (cyc r) = r := by
    intro r hr
    rw [hreps, Finset.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    rw [cyc_eq_of_mem (repF_mem p.first u)]
  have hrep_in_comp : ∀ r ∈ reps, r ∈ comp := by
    intro r hr
    rw [hreps, Finset.mem_image] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    have hucomp : u ∉ p.vertsFinset := by rw [hcomp, Finset.mem_sdiff] at hu; exact hu.2
    have hdis : Disjoint (cyc u) p.vertsFinset := compl_cyc_disjoint huoc hucomp
    rw [hcomp, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, Finset.disjoint_left.mp hdis (repF_mem p.first u)⟩
  -- `p` is vertex-disjoint from every orbit path
  have hp_disj_orbit : ∀ q ∈ orbitPaths, Disjoint p.vertsFinset q.vertsFinset := by
    intro q hq
    rw [horb, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    rw [Finset.mem_toList] at hr
    rw [orbitPath_vertsFinset hk1 r]
    have hrp : r ∉ p.vertsFinset := by
      have := hrep_in_comp r hr; rw [hcomp, Finset.mem_sdiff] at this; exact this.2
    exact (compl_cyc_disjoint huoc hrp).symm
  -- (hps)
  have hps : ps ≠ [] := by rw [hps_def]; exact List.cons_ne_nil _ _
  -- (hSE)  every member of `ps` is strongly exitless
  have hSE_all : ∀ q ∈ ps, q.StronglyExitless := by
    intro q hq
    rw [hps_def, List.mem_cons] at hq
    rcases hq with rfl | hqo
    · exact hSE
    · rw [horb, List.mem_map] at hqo
      obtain ⟨r, _, rfl⟩ := hqo
      exact orbitPath_SE hk1 r
  -- (hpair) pairwise vertex-disjoint
  have hpair : ps.Pairwise (fun a b : HPath k => Disjoint a.vertsFinset b.vertsFinset) := by
    rw [hps_def, List.pairwise_cons]
    refine ⟨hp_disj_orbit, ?_⟩
    rw [horb, List.pairwise_map]
    refine (Finset.nodup_toList reps).pairwise_of_forall_ne ?_
    intro r1 hr1 r2 hr2 hne12
    rw [Finset.mem_toList] at hr1 hr2
    rw [orbitPath_vertsFinset hk1 r1, orbitPath_vertsFinset hk1 r2]
    apply cyc_disjoint_of_ne
    intro heq
    exact hne12 (by rw [← hrep_idem r1 hr1, ← hrep_idem r2 hr2, heq])
  -- (hcover) every vertex lies in some member of `ps`
  have hcover : ∀ v : Vtx k, ∃ q ∈ ps, v ∈ q.verts := by
    intro v
    by_cases hv : v ∈ p.verts
    · exact ⟨p, by rw [hps_def]; exact List.mem_cons_self, hv⟩
    · have hvcomp : v ∈ comp := by
        rw [hcomp, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, fun h => hv (HPath.mem_vertsFinset.mp h)⟩
      have hrreps : repF p.first (cyc v) ∈ reps := by
        rw [hreps, Finset.mem_image]; exact ⟨v, hvcomp, rfl⟩
      refine ⟨orbitPath hk1 (repF p.first (cyc v)), ?_, ?_⟩
      · rw [hps_def]; refine List.mem_cons_of_mem _ ?_
        rw [horb, List.mem_map]; exact ⟨_, Finset.mem_toList.mpr hrreps, rfl⟩
      · have hcycr : cyc (repF p.first (cyc v)) = cyc v := cyc_eq_of_mem (repF_mem p.first v)
        refine HPath.mem_vertsFinset.mp ?_
        rw [orbitPath_vertsFinset hk1 _, hcycr]
        exact ProofsExitless.mem_cyc.mpr rfl
  -- (hnd)
  have hnd : (unwindVerts ps).Nodup := ProofsUnwind4.unwindVerts_nodup_of_pairwise hpair
  -- the union `X` of all component edge-sets
  set X : Finset (Vtx k × Vtx k) := Finset.univ.filter (fun e => ∃ q ∈ ps, e ∈ q.edges)
    with hXset
  have hXdef : ∀ e, e ∈ X ↔ ∃ q ∈ ps, e ∈ q.edges := by
    intro e; rw [hXset, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩
  have hXmem : X ∈ Xk k :=
    prp_Xk_se_sufficiency_unwind3 hps hnd hcover hSE_all hk hpair hXdef
  -- `p` is a path-component of `X`
  have hPC : IsPathComponent p X := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rw [hXdef]; exact ⟨p, by rw [hps_def]; exact List.mem_cons_self, he⟩
    · intro e heX
      rw [hXdef] at heX
      obtain ⟨q, hq, heq⟩ := heX
      obtain ⟨h1q, h2q⟩ := edge_endpoints_mem heq
      rw [hps_def, List.mem_cons] at hq
      rcases hq with rfl | hqo
      · exact ⟨fun _ => HPath.mem_vertsFinset.mpr h2q, fun _ => HPath.mem_vertsFinset.mpr h1q⟩
      · have hdisj := hp_disj_orbit q hqo
        constructor
        · intro h1
          exact absurd (HPath.mem_vertsFinset.mpr h1q) (Finset.disjoint_left.mp hdisj h1)
        · intro h2
          exact absurd (HPath.mem_vertsFinset.mpr h2q) (Finset.disjoint_left.mp hdisj h2)
    · intro e heX h1
      rw [hXdef] at heX
      obtain ⟨q, hq, heq⟩ := heX
      rw [hps_def, List.mem_cons] at hq
      rcases hq with rfl | hqo
      · exact heq
      · obtain ⟨h1q, _⟩ := edge_endpoints_mem heq
        have hdisj := hp_disj_orbit q hqo
        exact absurd (HPath.mem_vertsFinset.mpr h1q) (Finset.disjoint_left.mp hdisj h1)
  exact ⟨X, hXmem, hPC⟩

/-! ## Target 2 — the downstream closures now that `hrev` is proved -/

/-- **prp-Xkcomps (closed)** — `𝒳'_k = {strongly exitless paths}`, fully proved for `2 ≤ k`
(the `⊇` half `hrev` is now discharged).  Only remaining guard: `2 ≤ k`. -/
theorem prp_Xkcomps_closed (hk : 2 ≤ k) :
    Xk' k = {p : HPath k | p.StronglyExitless} :=
  prp_Xkcomps_amended hk (hrev hk)

/-- **red-p\* (closed)** — take23's `≥`-reduction, with `prp_Xkcomps` and the `𝒳'_k`-nonempty
side condition fully discharged (`hrev` proved, `𝒳_k` nonempty via `Xk_nonempty`).  Remaining
guards only: `1 < r`, `2 ≤ k`. -/
theorem red_pstar_closed {r : ℝ} (hr : 1 < r) (hk : 2 ≤ k) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
  red_pstar_tightened hr hk (hrev hk) (Xk_nonempty k)

/-- **red-R (closed)** — take23 l.744 `≥` form, **fully discharged** for `3 ≤ k`.  The only
former leaf `hne` (a non-spanning strongly-exitless component exists in `𝒳'_k`) is now supplied
by an orbit path: a single 1-cycle `orbitPath u` is strongly exitless (so lies in `𝒳'_k` by
`hrev`) with `|orbitPath u| = k ≤ k! − k` for `k ≥ 3` (`two_k_le_factorial`).  Guard `3 ≤ k`
(genuinely needed: for `k ≤ 2` there is only one 1-cycle, so every SE component is spanning). -/
theorem red_R_closed (hk : 3 ≤ k) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  set u : Vtx k := (ProofsSpine.vtx_nonempty k).some with hu
  have hmem : (orbitPath hk1 u) ∈ Xk' k := hrev hk2 (orbitPath_SE hk1 u)
  have hle : (orbitPath hk1 u).numVerts ≤ k.factorial - k := by
    rw [orbitPath_numVerts hk1 u]
    have := two_k_le_factorial hk; omega
  exact red_R_final hk2 ⟨orbitPath hk1 u, hmem, hle⟩

end Hunter.Proved

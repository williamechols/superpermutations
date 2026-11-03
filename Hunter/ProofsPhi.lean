/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsExitless

/-!
# `clm-phi` sufficiency and the `StronglyExitless` ↔ `IsUnionOfCycles` bridge (Hunter §6)

This file closes the `φ`-form leaf of the exitless track:

* `ProofsPhi.getElem?_flatten_blocks` / `ProofsPhi.phi_vert` — the **flatten-indexing lemma**
  the original sketch flagged as missing: for a list `vs` of "block seeds", position
  `k·s + r` (`s < |vs|`, `r < k`) of the flatten of the uniform `σ`-orbit blocks is
  `σ^r(vs[s])`.  Proved generically for lists of `k`-length blocks.
* `Proved.clm_phi_sufficiency` — **clm-phi (⟸)**: a path in `φ`-form is `StronglyExitless`.
  Delivered *unguarded* (verbatim faithful to the paper), because `IsPhiForm` is already
  **false at `k = 0`** (it forces `p.verts = []`, contradicting `p.ne`), so the `k = 0`
  case is vacuous — unlike *necessity*, which genuinely needed `1 ≤ k`.
* `Proved.bridge_stronglyExitless_iff_phiForm` — the clean iff that necessity + sufficiency
  actually compose to: `StronglyExitless ↔ IsPhiForm` (guard `1 ≤ k`, inherited from
  necessity).
* `Proved.bridge_stronglyExitless_iff_unionOfCycles` — **AMENDED with the guard `p.Exitless`.**
  The unguarded iff of `Hunter/Statements.lean` is **FALSE**: `IsUnionOfCycles` is a purely
  *set-level* condition (`∀ v ∈ p, c(v) ⊆ V(p)`) that does not constrain the traversal order,
  whereas `StronglyExitless` does.  Concrete counterexample at `k = 3`: interleaving the two
  rotation classes,
  `p = [[1,2,3],[1,3,2],[2,3,1],[3,2,1],[3,1,2],[2,1,3]]`, is a union of cycles as a *set*
  but the first edge `[1,2,3]→[1,3,2]` is an early exit (weight `≥ 2` while `σ[1,2,3]=[2,3,1]`
  is only reached later), so `p` is not exitless.  Hence no `k`-guard repairs it (it fails at
  `k = 3`, the regime of interest).  Under the guard `p.Exitless` the iff *is* true and is
  what the paper's `⟸`-flag ("may need the path's traversal order") was gesturing at:
  `→` is `clm-1cyclesubset`; `←` is `σ(last) ∈ c(last) ⊆ V(p)`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsPhi

open HPath ProofsExitless

variable {k : ℕ}

/-! ## The flatten-indexing lemma (for uniform `k`-length `σ`-orbit blocks) -/

/-- **Flatten-indexing lemma (`getElem?` form).**  In the flatten of the uniform blocks
`vs.map (v ↦ [v, σv, …, σ^{k-1}v])`, the entry at flat position `k·s + r` (`s < |vs|`,
`r < k`) is `σ^r(vs[s])`.  Proved by induction on `vs` at the `getElem?` level (free indices,
no proof-carrying `getElem`). -/
theorem getElem?_flatten_blocks (vs : List (Vtx k)) {s : ℕ} (hs : s < vs.length)
    {r : ℕ} (hr : r < k) :
    (vs.map (fun v => (List.range k).map (fun r => sigma^[r] v))).flatten[k * s + r]?
      = some (sigma^[r] (vs[s]'hs)) := by
  induction vs generalizing s with
  | nil => simp at hs
  | cons v vs ih =>
    have hblen : ((List.range k).map (fun r => sigma^[r] v)).length = k := by
      rw [List.length_map, List.length_range]
    rw [List.map_cons, List.flatten_cons]
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0
      rw [Nat.mul_zero, Nat.zero_add,
        List.getElem?_append_left (by rw [hblen]; exact hr),
        List.getElem?_map, List.getElem?_range hr]
      simp
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hge : ((List.range k).map (fun r => sigma^[r] v)).length ≤ k * (s' + 1) + r := by
        rw [hblen]; have e : k * (s' + 1) = k * s' + k := by ring
        omega
      rw [List.getElem?_append_right hge, hblen]
      have hidxeq : k * (s' + 1) + r - k = k * s' + r := by
        have e : k * (s' + 1) = k * s' + k := by ring
        omega
      rw [hidxeq]
      have hs' : s' < vs.length := by
        have := hs; simp only [List.length_cons] at this; omega
      rw [ih hs']
      simp

/-- Every `φ`-form path has `|p| = k·|vs|` (each of the `|vs|` blocks has length `k`). -/
theorem phi_numVerts {p : HPath k} {vs : List (Vtx k)}
    (hverts : p.verts
      = (vs.map (fun v => (List.range k).map (fun r => sigma^[r] v))).flatten) :
    p.numVerts = k * vs.length := by
  rw [HPath.numVerts, hverts, List.length_flatten, List.map_map]
  have hmap : (vs.map (List.length ∘ fun v => (List.range k).map (fun r => sigma^[r] v)))
      = vs.map (fun _ => k) := by
    apply List.map_congr_left
    intro v _
    simp
  rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-- **Flatten-indexing lemma (`vert` form).**  For a `φ`-form path, `p[k·s + r] = σ^r(vs[s])`
(`s < |vs|`, `r < k`). -/
theorem phi_vert {p : HPath k} {vs : List (Vtx k)}
    (hverts : p.verts
      = (vs.map (fun v => (List.range k).map (fun r => sigma^[r] v))).flatten)
    {s : ℕ} (hs : s < vs.length) {r : ℕ} (hr : r < k) :
    p.vert (k * s + r) = sigma^[r] (vs[s]'hs) := by
  have hlen := phi_numVerts hverts
  have hlt : k * s + r < p.numVerts := by
    rw [hlen]
    have hks : k * (s + 1) ≤ k * vs.length := Nat.mul_le_mul (le_refl k) hs
    have e : k * (s + 1) = k * s + k := by ring
    omega
  have h1 : p.verts[k * s + r]? = some (sigma^[r] (vs[s]'hs)) := by
    rw [hverts]; exact getElem?_flatten_blocks vs hs hr
  have h2 : p.verts[k * s + r]? = some (p.vert (k * s + r)) := by
    rw [List.getElem?_eq_getElem hlt, vert_getElem p hlt]
  exact (Option.some_inj.mp (h2.symm.trans h1))

end ProofsPhi

namespace Proved

open HPath ProofsExitless ProofsPhi

/-! ## `clm-phi` (⟸): φ-form ⟹ strongly exitless -/

/-- **clm-phi (sufficiency)** — Hunter §6 l.523, ⟸.  Every `φ(c⃗,v⃗)` is a strongly exitless
path.  Delivered *unguarded* (verbatim to the paper): at `k = 0`, `IsPhiForm p` forces
`p.verts = []`, contradicting `p.ne`, so that case is vacuous. -/
theorem clm_phi_sufficiency {k : ℕ} {p : HPath k} (hp : IsPhiForm p) : p.StronglyExitless := by
  obtain ⟨vs, _hnodup, hverts⟩ := hp
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `IsPhiForm` is impossible (`p.verts` would be empty).
    exfalso
    subst hk0
    apply p.ne
    rw [hverts]
    simp
  · -- `k ≥ 1`.
    have hlen : p.numVerts = k * vs.length := phi_numVerts hverts
    have ht0 : 0 < vs.length := by
      rcases Nat.eq_zero_or_pos vs.length with h | h
      · exfalso; have := p.numVerts_pos; rw [hlen, h, Nat.mul_zero] at this; omega
      · exact h
    have hvert : ∀ (s : ℕ) (hs : s < vs.length) (r : ℕ), r < k →
        p.vert (k * s + r) = sigma^[r] (vs[s]'hs) :=
      fun s hs r hr => phi_vert hverts hs hr
    refine ⟨?_, ?_⟩
    · -- Exitless.
      intro he
      obtain ⟨i, hi2, hw, hlt⟩ := he
      set s := i / k with hsdef
      set r := i % k with hrdef
      have hik : k * s + r = i := Nat.div_add_mod i k
      have hrk : r < k := Nat.mod_lt i hk
      have hs : s < vs.length := by
        rcases lt_or_ge s vs.length with h | h
        · exact h
        · exfalso
          have hle : k * vs.length ≤ k * s := Nat.mul_le_mul (le_refl k) h
          rw [hlen] at hi2
          omega
      have hv0 : p.vert i = sigma^[r] (vs[s]'hs) := by
        rw [← hik]; exact hvert s hs r hrk
      rcases Nat.lt_or_ge (r + 1) k with hlt' | hge'
      · -- interior of a block: the step is `σ` (weight 1), contradicting `w ≥ 2`.
        have hv1 : p.vert (i + 1) = sigma^[r + 1] (vs[s]'hs) := by
          have he1 : k * s + (r + 1) = i + 1 := by omega
          rw [← he1]; exact hvert s hs (r + 1) hlt'
        have hstep : p.vert (i + 1) = sigma (p.vert i) := by
          rw [hv1, hv0, sigma_iter_succ']
        have hone : ew k (p.vert i) (p.vert (i + 1)) = 1 := by
          rw [hstep]; exact ew_sigma hk _
        omega
      · -- block seam (`r = k-1`): `σ(p[i]) = vs[s] = p[k·s]`, already visited at `k·s ≤ i`.
        have hrk1 : r + 1 = k := by omega
        have hsig : sigma (p.vert i) = vs[s]'hs := by
          rw [hv0, sigma_iter_succ', hrk1, sigma_iter_period]
        have hks_lt : k * s < p.numVerts := by omega
        have hvs : vs[s]'hs = p.vert (k * s) := by
          have h0 := hvert s hs 0 hk
          simp only [Nat.add_zero, Function.iterate_zero, id_eq] at h0
          exact h0.symm
        have hpos : p.pos (sigma (p.vert i)) = k * s := by
          rw [hsig, hvs, pos_vert p hks_lt]
        rw [hpos] at hlt
        omega
    · -- `σ(p.last) ∈ V(p)`.
      rw [Proved.last_eq_vert]
      set t := vs.length with htdef
      have hNeq : p.numVerts - 1 = k * (t - 1) + (k - 1) := by
        rw [hlen]
        have hkt : k * t = k * (t - 1) + k := by
          conv_lhs => rw [show t = (t - 1) + 1 from by omega]
          ring
        omega
      rw [hNeq]
      have hst : t - 1 < vs.length := by omega
      have hv := hvert (t - 1) hst (k - 1) (by omega)
      rw [hv, sigma_iter_succ', show k - 1 + 1 = k from by omega, sigma_iter_period]
      have h0 := hvert (t - 1) hst 0 hk
      simp only [Nat.add_zero, Function.iterate_zero, id_eq] at h0
      rw [← h0]
      exact vert_mem p (by
        rw [hlen]; exact Nat.mul_lt_mul_of_pos_left (by omega) hk)

/-! ## Bridges -/

/-- **StronglyExitless ↔ IsPhiForm** (guard `1 ≤ k`).  The genuine composition of
necessity (`clm_phi_necessity_amended`) and sufficiency (`clm_phi_sufficiency`).  This is the
clean characterization the paper's `clm-phi` states; the `1 ≤ k` guard is inherited from
necessity (false at `k = 0`, see `Hunter/ProofsExitless.lean`). -/
theorem bridge_stronglyExitless_iff_phiForm {k : ℕ} (hk : 1 ≤ k) {p : HPath k} :
    p.StronglyExitless ↔ IsPhiForm p :=
  ⟨Proved.clm_phi_necessity_amended hk, clm_phi_sufficiency⟩

/-- **StronglyExitless ↔ IsUnionOfCycles**, **AMENDED with the guard `p.Exitless`**.  The
unguarded iff (as stated in `Hunter/Statements.lean`) is *false*: `IsUnionOfCycles` constrains
only the vertex *set*, not the traversal order (counterexample at `k = 3` — see the module
docstring).  Under `p.Exitless` the equivalence holds:
* `→` is `clm-1cyclesubset` (strongly exitless ⟹ union of cycles);
* `←` uses `σ(last) ∈ c(last) ⊆ V(p)` together with `hexit` to reassemble
  `StronglyExitless = Exitless ∧ σ(last) ∈ V(p)`. -/
theorem bridge_stronglyExitless_iff_unionOfCycles {k : ℕ} {p : HPath k} (hexit : p.Exitless) :
    p.StronglyExitless ↔ p.IsUnionOfCycles := by
  constructor
  · intro hse
    exact Proved.clm_1cyclesubset hse
  · intro huoc
    refine ⟨hexit, ?_⟩
    have hsub : cyc p.last ⊆ p.vertsFinset := huoc p.last p.last_mem
    have hmem : sigma p.last ∈ cyc p.last := by
      have h := ProofsExitless.sigma_iter_mem_cyc 1 p.last
      rwa [Function.iterate_one] at h
    exact HPath.mem_vertsFinset.mp (hsub hmem)

end Proved

end Hunter

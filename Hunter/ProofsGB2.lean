/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsB2
import Hunter.ProofsRecursion

/-!
# `prp_gives_b2` and the closing reduction-side leaves (`Hunter/ProofsGB2.lean`)

This file closes the remaining reduction-side gaps left open by `Hunter/ProofsB2.lean`:

* **`prp_gives_b2_amended`** — the per-`X` regrouping (take23 §"Getting Bounds"
  `Proposition (gives b2)`): from Bound 1's value `(|Comps X|−1) + MinThrough X + w(X)`,
  expand `MinThrough = Σ compMinto − max compMinto`, regroup into
  `Σ_{c∈Comps X} pValue(c) − 1 − max compMinto`, and bound each non-maximal component below via
  the `R_k` cost function on `𝒳'_k`.  Delivered **amended with `2 ≤ k`** (see STATEMENT
  DISCREPANCY in `PROGRESS-gb2.md`).  This unlocks `b2_of_gives_b2` → `b2_final`.
* **`Xk_nonempty`** — `𝒳_k` is nonempty for `2 ≤ k` (from `exists_ham`).
* the `red_R` side-conditions and the `g`-monotonicity leaf.

Helper lemmas live in `namespace Hunter.ProofsGB2`; delivered targets in `namespace
Hunter.Proved` with the type copied verbatim (Statements is **not** cited; it is only
transitively imported for the shared definitions).  Zero `sorry`, zero new axioms.
See `PROGRESS-gb2.md`.
-/

namespace Hunter

open scoped Classical
open Finset

namespace ProofsGB2

variable {k : ℕ}

/-! ## Weak-component partition of the vertex set and the edge set

`Comps X` is the image of the block map; its blocks partition `vertsOf X` (vertices) and the
sets `inducedEdges X C` partition `X` (edges).  We record the two resulting sum identities. -/

/-- The blocks of `Comps X` cover exactly `vertsOf X`. -/
theorem verts_biUnion (X : Finset (Vtx k × Vtx k)) :
    (Comps X).biUnion (fun C => C) = vertsOf X := by
  ext v
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hvC⟩
    obtain ⟨u, huV, hb⟩ := ProofsWP.mem_comps.mp hC
    rw [← hb] at hvC
    exact (ProofsWP.mem_block.mp hvC).1
  · intro hv
    exact ⟨ProofsWP.block X v, ProofsWP.block_mem_comps hv, ProofsWP.self_mem_block hv⟩

/-- Distinct blocks are disjoint (they partition `vertsOf X`); reindexes `card_biUnion`. -/
theorem card_verts_eq_sum (X : Finset (Vtx k × Vtx k)) :
    (vertsOf X).card = ∑ C ∈ Comps X, C.card := by
  rw [← verts_biUnion X,
    Finset.card_biUnion (fun _ hC _ hC' hne => ProofsWP.comps_disjoint hC hC' hne)]

/-- The induced-edge sets `inducedEdges X C` cover exactly `X`. -/
theorem edges_biUnion (X : Finset (Vtx k × Vtx k)) :
    (Comps X).biUnion (inducedEdges X) = X := by
  ext e
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, heC⟩
    exact (Finset.mem_filter.mp heC).1
  · intro heX
    have hv1 : e.1 ∈ vertsOf X := ProofsWP.mem_vertsOf.mpr ⟨e, heX, Or.inl rfl⟩
    exact ⟨ProofsWP.block X e.1, ProofsWP.block_mem_comps hv1,
      Finset.mem_filter.mpr ⟨heX, ProofsWP.self_mem_block hv1⟩⟩

/-- Distinct components' induced-edge sets are disjoint (an edge's source lies in one block). -/
theorem inducedEdges_disjoint {X : Finset (Vtx k × Vtx k)} {C C' : Finset (Vtx k)}
    (hC : C ∈ Comps X) (hC' : C' ∈ Comps X) (hne : C ≠ C') :
    Disjoint (inducedEdges X C) (inducedEdges X C') := by
  rw [Finset.disjoint_left]
  intro e he he'
  have h1 : e.1 ∈ C := (Finset.mem_filter.mp he).2
  have h2 : e.1 ∈ C' := (Finset.mem_filter.mp he').2
  exact (Finset.disjoint_left.mp (ProofsWP.comps_disjoint hC hC' hne) h1) h2

/-- `w(X)` decomposes as the sum of the induced weights over the components. -/
theorem wEdges_eq_sum (X : Finset (Vtx k × Vtx k)) :
    wEdges X = ∑ C ∈ Comps X, wEdges (inducedEdges X C) := by
  calc wEdges X = ∑ e ∈ X, ew k e.1 e.2 := rfl
    _ = ∑ e ∈ (Comps X).biUnion (inducedEdges X), ew k e.1 e.2 := by rw [edges_biUnion X]
    _ = ∑ C ∈ Comps X, ∑ e ∈ inducedEdges X C, ew k e.1 e.2 :=
        Finset.sum_biUnion (fun C hC C' hC' hne => inducedEdges_disjoint hC hC' hne)
    _ = ∑ C ∈ Comps X, wEdges (inducedEdges X C) := rfl

/-! ## `MinThrough` as `Σ compMinto − sup compMinto` (unconditionally) -/

theorem sup_compMinto_le_sum (X : Finset (Vtx k × Vtx k)) :
    (Comps X).sup (compMinto X) ≤ ∑ C ∈ Comps X, compMinto X C :=
  Finset.sup_le (fun _C hC => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hC)

/-- `MinThrough X + sup compMinto = Σ compMinto` in **both** the `≤ 1`-component branch (both
sides collapse) and the `≥ 2` branch (the honest `Σ − sup`). -/
theorem minThrough_add_sup (X : Finset (Vtx k × Vtx k)) :
    MinThrough X + (Comps X).sup (compMinto X) = ∑ C ∈ Comps X, compMinto X C := by
  rw [MinThrough]
  by_cases hc : (Comps X).card ≤ 1
  · rw [if_pos hc, zero_add]
    rcases Nat.eq_zero_or_pos (Comps X).card with h0 | hpos
    · rw [Finset.card_eq_zero] at h0; rw [h0]; simp
    · have h1 : (Comps X).card = 1 := le_antisymm hc hpos
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      rw [ha, Finset.sup_singleton, Finset.sum_singleton]
  · rw [if_neg hc, Nat.sub_add_cancel (sup_compMinto_le_sum X)]

/-! ## Per-component identities on `𝒳_k` -/

theorem card_vertsFinset (p : HPath k) : p.vertsFinset.card = p.numVerts :=
  List.toFinset_card_of_nodup p.nodup

/-- On a path-component, the induced-edge set is exactly the path's edge set. -/
theorem inducedEdges_eq_edges {p : HPath k} {X : Finset (Vtx k × Vtx k)}
    (hpc : IsPathComponent p X) : inducedEdges X p.vertsFinset = p.edges := by
  ext e
  simp only [inducedEdges, Finset.mem_filter]
  constructor
  · rintro ⟨heX, he1⟩; exact hpc.2.2 e heX he1
  · intro he; exact ⟨hpc.1 he, HPath.mem_vertsFinset.mpr (ProofsWP.edge_ends_mem he).1⟩

/-! ## The `R_k` cost-function bound -/

/-- The `R_k` value set is bounded below by `0` (all `pValue/|p|` are nonnegative). -/
theorem Rk_bddBelow (k : ℕ) :
    BddBelow {q : ℝ | ∃ p, p ∈ Xk' k ∧ p.numVerts ≤ k.factorial - k ∧
      q = (pValue p : ℝ) / (p.numVerts : ℝ)} := by
  refine ⟨0, ?_⟩
  rintro q ⟨p, -, -, rfl⟩
  positivity

/-- `R_k ≥ 0`. -/
theorem Rk_nonneg (k : ℕ) : 0 ≤ Rk k := by
  rw [Rk]
  apply Real.sInf_nonneg
  rintro q ⟨p, -, -, rfl⟩
  positivity

/-- **The per-component `R_k` cost bound** — for a non-maximal component `C` of `X = F(P)`
(so `|C| ≤ k!−k`, the maximal component `Cmax` alone contributing `≥ k` vertices), its
`p_value` dominates `R_k·|C|`.  This is the core inequality of `prp_gives_b2`. -/
theorem pv_ge {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    {C Cmax : Finset (Vtx k)} (hC : C ∈ Comps (F P)) (hCmax : Cmax ∈ Comps (F P))
    (hne : C ≠ Cmax) (hCmaxk : k ≤ Cmax.card)
    (hsumcard : ∑ D ∈ Comps (F P), D.card = k.factorial) :
    (1 : ℝ) + (compMinto (F P) C : ℝ) + (wEdges (inducedEdges (F P) C) : ℝ)
      ≥ Rk k * (C.card : ℝ) := by
  obtain ⟨p, hpV, hpc⟩ := Hunter.Proved.lem_pathrule hP C hC
  have hpse : p.StronglyExitless := ProofsB2.stronglyExitless_of_isPathComponent hP hk hpc
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hCcard : C.card = p.numVerts := by rw [← hpV]; exact card_vertsFinset p
  have hmintoC : compMinto (F P) C = p.minto := by
    rw [← hpV]; exact Hunter.Proved.bridge_compMinto_eq_minto hpc
  have hwEC : wEdges (inducedEdges (F P) C) = p.wtP := by
    rw [← hpV, inducedEdges_eq_edges hpc]; exact Hunter.Proved.bridge_wEdges_edges_eq_wtP p
  -- `p` is non-spanning: `|C| + |Cmax| ≤ k!` and `|Cmax| ≥ k`, so `|p| = |C| ≤ k!−k`.
  have hsum2 : C.card + Cmax.card ≤ k.factorial := by
    rw [← hsumcard, ← Finset.sum_erase_add (Comps (F P)) (fun D => D.card) hC]
    have hCmax_erase : Cmax ∈ (Comps (F P)).erase C :=
      Finset.mem_erase.mpr ⟨fun h => hne h.symm, hCmax⟩
    have hle := Finset.single_le_sum (f := fun D => D.card) (fun _ _ => Nat.zero_le _) hCmax_erase
    omega
  have hpnv_le : p.numVerts ≤ k.factorial - k := by rw [← hCcard]; omega
  -- `R_k ≤ pValue p / |p|`, then clear the (positive) denominator.
  have hpXk' : p ∈ Xk' k := ⟨F P, ⟨P, hP, rfl⟩, hpc⟩
  have hppos : 0 < p.numVerts := p.numVerts_pos
  have hmem : (pValue p : ℝ) / (p.numVerts : ℝ) ∈ {q : ℝ | ∃ p', p' ∈ Xk' k ∧
      p'.numVerts ≤ k.factorial - k ∧ q = (pValue p' : ℝ) / (p'.numVerts : ℝ)} :=
    ⟨p, hpXk', hpnv_le, rfl⟩
  have hRkle : Rk k ≤ (pValue p : ℝ) / (p.numVerts : ℝ) := csInf_le (Rk_bddBelow k) hmem
  have hnvpos : (0 : ℝ) < (p.numVerts : ℝ) := by exact_mod_cast hppos
  have hbound : Rk k * (p.numVerts : ℝ) ≤ (pValue p : ℝ) := (le_div_iff₀ hnvpos).mp hRkle
  have hcast : (1 : ℝ) + (compMinto (F P) C : ℝ) + (wEdges (inducedEdges (F P) C) : ℝ)
      = (pValue p : ℝ) := by
    rw [hmintoC, hwEC]; simp only [pValue]; push_cast; ring
  rw [hcast, hCcard]
  linarith [hbound]

/-! ## The concrete inner-min `gInner` and its monotonicity

`proof_thm1v2` (reductions track) takes an abstract `gInner : ℝ → ℝ` and the monotonicity of
`r ↦ r·k! + gInner r` as a hypothesis (`hg_mono`).  Here we pin `gInner` to the concrete
`b2` inner min `sInf{ w(p*) − r|p*| : p* ∈ 𝒳'_k }` and **prove** the monotonicity outright
(each affine term `w(p*) + r(k!−|p*|)` has slope `k!−|p*| ≥ 0`). -/

/-- The concrete reduction inner-min `gInner k r = min_{p*∈𝒳'_k}{ w(p*) − r|p*| }`. -/
noncomputable def gInner (k : ℕ) (r : ℝ) : ℝ :=
  sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}

theorem numVerts_le_factorial (p : HPath k) : (p.numVerts : ℝ) ≤ (k.factorial : ℝ) := by
  have := p.nodup.length_le_card
  rw [ProofsRecursion.card_Vtx] at this
  exact_mod_cast this

/-- The `b2`-inner value set `{ w(p*) − r|p*| }` is bounded below (`|p*| ≤ k!`). -/
theorem innerSet_bddBelow (k : ℕ) (r : ℝ) :
    BddBelow {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)} := by
  refine ⟨-(|r| * (k.factorial : ℝ)), ?_⟩
  rintro q ⟨p, -, rfl⟩
  have h1 : (p.numVerts : ℝ) ≤ (k.factorial : ℝ) := numVerts_le_factorial p
  have h3 : (0 : ℝ) ≤ (p.numVerts : ℝ) := by positivity
  have h4 : r * (p.numVerts : ℝ) ≤ |r| * (k.factorial : ℝ) :=
    calc r * (p.numVerts : ℝ) ≤ |r * (p.numVerts : ℝ)| := le_abs_self _
      _ = |r| * (p.numVerts : ℝ) := by rw [abs_mul, abs_of_nonneg h3]
      _ ≤ |r| * (k.factorial : ℝ) := mul_le_mul_of_nonneg_left h1 (abs_nonneg r)
  have h2 : (0 : ℝ) ≤ (p.wtP : ℝ) := by positivity
  linarith

/-- Monotonicity of `r ↦ r·k! + gInner k r` — the `hg_mono` leaf of `proof_thm1v2`, proved
outright for the concrete `gInner`.  Needs `𝒳'_k` nonempty (⟸ `𝒳_k` nonempty). -/
theorem gInner_mono (hk : 2 ≤ k) (hne_Xk : (Xk k).Nonempty) (r s : ℝ) (hrs : r ≤ s) :
    r * (k.factorial : ℝ) + gInner k r ≤ s * (k.factorial : ℝ) + gInner k s := by
  have hSne : {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - s * (p.numVerts : ℝ)}.Nonempty := by
    obtain ⟨p, hp⟩ := ProofsB2.Xk'_nonempty_of_Xk_nonempty hk hne_Xk
    exact ⟨_, p, hp, rfl⟩
  have hkey : gInner k r + (r - s) * (k.factorial : ℝ) ≤ gInner k s := by
    show gInner k r + (r - s) * (k.factorial : ℝ)
      ≤ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - s * (p.numVerts : ℝ)}
    apply le_csInf hSne
    rintro y ⟨p, hp, rfl⟩
    have hple : gInner k r ≤ (p.wtP : ℝ) - r * (p.numVerts : ℝ) :=
      csInf_le (innerSet_bddBelow k r) ⟨p, hp, rfl⟩
    have hnv : (p.numVerts : ℝ) ≤ (k.factorial : ℝ) := numVerts_le_factorial p
    nlinarith [hple, hnv, hrs]
  linarith [hkey]

/-- The `b2` value set `{ w(p*) + R_k(k!−|p*|) }` is bounded below by `0` (`R_k ≥ 0`,
`|p*| ≤ k!`).  This discharges the `hBddB` junk-guard of `b2_of_gives_b2`. -/
theorem b2Set_bddBelow (k : ℕ) :
    BddBelow {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} := by
  refine ⟨0, ?_⟩
  rintro q ⟨p, -, rfl⟩
  have h1 : (p.numVerts : ℝ) ≤ (k.factorial : ℝ) := numVerts_le_factorial p
  have h2 : 0 ≤ Rk k := Rk_nonneg k
  have h3 : 0 ≤ Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ)) := mul_nonneg h2 (by linarith)
  have h4 : (0 : ℝ) ≤ (p.wtP : ℝ) := by positivity
  linarith

/-- Constant-shift identity: the `b2` value set's `sInf` equals `R_k·k! + gInner k (R_k)`. -/
theorem b2Set_sInf_eq (k : ℕ) (hne : (Xk' k).Nonempty) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
        q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))}
      = Rk k * (k.factorial : ℝ) + gInner k (Rk k) := by
  have hRne : {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)}.Nonempty := by
    obtain ⟨p, hp⟩ := hne; exact ⟨_, p, hp, rfl⟩
  have hBne : {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))}.Nonempty := by
    obtain ⟨p, hp⟩ := hne; exact ⟨_, p, hp, rfl⟩
  rw [gInner]
  apply le_antisymm
  · -- `sInf B ≤ Rk·k! + sInf R`
    have h : sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
          q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))}
        - Rk k * (k.factorial : ℝ)
        ≤ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)} := by
      apply le_csInf hRne
      rintro x ⟨p, hp, rfl⟩
      have hb := csInf_le (b2Set_bddBelow k)
        (show (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ)) ∈ _ from ⟨p, hp, rfl⟩)
      have hdist : Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))
          = Rk k * (k.factorial : ℝ) - Rk k * (p.numVerts : ℝ) := by ring
      rw [hdist] at hb; linarith
    linarith [h]
  · -- `Rk·k! + sInf R ≤ sInf B`
    apply le_csInf hBne
    rintro y ⟨p, hp, rfl⟩
    have hR := csInf_le (innerSet_bddBelow k (Rk k))
      (show (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ) ∈ _ from ⟨p, hp, rfl⟩)
    have hdist : Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))
        = Rk k * (k.factorial : ℝ) - Rk k * (p.numVerts : ℝ) := by ring
    rw [hdist]; linarith

end ProofsGB2

namespace Proved

variable {k : ℕ}

/-- **prp-gives-b2 (amended)** — take23 §"Getting Bounds" `Proposition (gives b2)`, delivered
**amended with the guard `2 ≤ k`** (the verbatim statement is degenerate at `k ≤ 1`, where the
`vertsOf (F P) = univ` / strongly-exitless structure that drives the regrouping is unavailable;
consistent with the other `_amended` targets).  For `X ∈ 𝒳_k`:
`(|Comps X|−1) + MinThrough X + w(X) ≥ R_k·k! + min_{p*∈Comps X}{ w(p*) − R_k|p*| }`.

Proof (per the take23 regrouping): `MinThrough X = Σ compMinto − max compMinto`, so
`X_VALUE = Σ_{C} pValue(C) − 1 − compMinto(Cmax)` where `Cmax` attains the max.  Splitting off
`Cmax` collapses this to `Σ_{C ≠ Cmax} pValue(C) + w(Cmax)`.  Each non-maximal component is a
strongly-exitless path with `|C| ≤ k!−k` (the maximal component alone has `≥ k` vertices), so
`pValue(C) ≥ R_k|C|` by definition of `R_k`; summing gives `≥ R_k(k!−|Cmax|) + w(Cmax) =
R_k·k! + (w(Cmax) − R_k|Cmax|) ≥ R_k·k! + sInf`.  No cross-track hypotheses remain. -/
theorem prp_gives_b2_amended (hk : 2 ≤ k) {X : Finset (Vtx k × Vtx k)} (hX : X ∈ Xk k) :
    ((numComps X : ℝ) - 1) + (MinThrough X : ℝ) + (wEdges X : ℝ)
      ≥ Rk k * (k.factorial : ℝ)
        + sInf {q : ℝ | ∃ p, IsPathComponent p X ∧
            q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)} := by
  obtain ⟨P, hP, rfl⟩ := hX
  set X := F P with hXdef
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  -- `Comps X` is nonempty and `Σ_C |C| = k!`.
  have hncpos : 1 ≤ numComps X := ProofsWP.one_le_numComps_F hP hk
  have hne_comps : (Comps X).Nonempty := Finset.card_pos.mp hncpos
  have hverts : vertsOf X = Finset.univ := ProofsStructure.vertsOf_F_eq_univ hP hk
  have hsumcard : ∑ C ∈ Comps X, C.card = k.factorial := by
    rw [← ProofsGB2.card_verts_eq_sum X, hverts, Finset.card_univ, ProofsRecursion.card_Vtx]
  -- the maximal component `Cmax`, a strongly-exitless path with `≥ k` vertices.
  obtain ⟨Cmax, hCmax_mem, hsup⟩ :=
    Finset.exists_mem_eq_sup (Comps X) hne_comps (compMinto X)
  obtain ⟨pm, hpmV, hpmc⟩ := Hunter.Proved.lem_pathrule hP Cmax hCmax_mem
  have hpmse : pm.StronglyExitless := ProofsB2.stronglyExitless_of_isPathComponent hP hk hpmc
  have hCmaxcard : Cmax.card = pm.numVerts := by rw [← hpmV]; exact ProofsGB2.card_vertsFinset pm
  have hCmaxk : k ≤ Cmax.card := by
    rw [hCmaxcard]
    exact Nat.le_of_dvd pm.numVerts_pos
      (Hunter.Proved.dvd_numVerts_of_stronglyExitless hk1 hpmse)
  have hwEmax : wEdges (inducedEdges X Cmax) = pm.wtP := by
    rw [← hpmV, ProofsGB2.inducedEdges_eq_edges hpmc]
    exact Hunter.Proved.bridge_wEdges_edges_eq_wtP pm
  -- the per-component `p_value`, and its total.
  set g : Finset (Vtx k) → ℝ := fun C =>
    (1 : ℝ) + (compMinto X C : ℝ) + (wEdges (inducedEdges X C) : ℝ) with hg
  set A : ℝ := ∑ C ∈ (Comps X).erase Cmax, g C with hA
  -- `Σ_C |C| = k!` and `Σ_C w(inducedEdges C) = w(X)`, as real sums.
  have hcardR : ∑ C ∈ Comps X, (C.card : ℝ) = (k.factorial : ℝ) := by
    rw [← Nat.cast_sum, hsumcard]
  have hwecast : ∑ C ∈ Comps X, (wEdges (inducedEdges X C) : ℝ) = (wEdges X : ℝ) := by
    rw [← Nat.cast_sum, ← ProofsGB2.wEdges_eq_sum]
  -- `Σ g = numComps + Σ compMinto + w(X)`.
  have hgsum : ∑ C ∈ Comps X, g C
      = (numComps X : ℝ) + (∑ C ∈ Comps X, (compMinto X C : ℝ)) + (wEdges X : ℝ) := by
    simp only [hg, numComps, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      hwecast]
  -- split off `Cmax`.
  have hsplit : ∑ C ∈ Comps X, g C = A + g Cmax :=
    (Finset.sum_erase_add (Comps X) g hCmax_mem).symm
  -- `MinThrough X = Σ compMinto − compMinto Cmax`, over ℝ.
  have hMTcast : (MinThrough X : ℝ)
      = (∑ C ∈ Comps X, (compMinto X C : ℝ)) - (compMinto X Cmax : ℝ) := by
    have hmt := ProofsGB2.minThrough_add_sup X
    rw [hsup] at hmt
    have := congrArg (Nat.cast : ℕ → ℝ) hmt
    push_cast at this
    linarith
  -- lower-bound `A` via the per-component `R_k` cost bound.
  have hA_ge : A ≥ Rk k * (k.factorial : ℝ) - Rk k * (Cmax.card : ℝ) := by
    have hpt : ∀ C ∈ (Comps X).erase Cmax, Rk k * (C.card : ℝ) ≤ g C := by
      intro C hCe
      obtain ⟨hCne, hCmem⟩ := Finset.mem_erase.mp hCe
      exact ProofsGB2.pv_ge hP hk hCmem hCmax_mem hCne hCmaxk hsumcard
    have hsum_ge : ∑ C ∈ (Comps X).erase Cmax, Rk k * (C.card : ℝ) ≤ A :=
      Finset.sum_le_sum hpt
    have hcard_erase : ∑ C ∈ (Comps X).erase Cmax, (C.card : ℝ)
        = (k.factorial : ℝ) - (Cmax.card : ℝ) := by
      have h := Finset.sum_erase_add (Comps X) (fun C => (C.card : ℝ)) hCmax_mem
      linarith [h, hcardR]
    rw [← Finset.mul_sum, hcard_erase] at hsum_ge
    nlinarith [hsum_ge]
  -- the max-component term lands in the inner set.
  have hCmaxcardR : (Cmax.card : ℝ) = (pm.numVerts : ℝ) := by exact_mod_cast hCmaxcard
  have hR23 : Rk k * (Cmax.card : ℝ) = Rk k * (pm.numVerts : ℝ) := by rw [hCmaxcardR]
  have hwEmaxR : (wEdges (inducedEdges X Cmax) : ℝ) = (pm.wtP : ℝ) := by exact_mod_cast hwEmax
  have hBddI : BddBelow {q : ℝ | ∃ p, IsPathComponent p X ∧
      q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)} := by
    refine ⟨-(Rk k * (k.factorial : ℝ)), ?_⟩
    rintro q ⟨p, -, rfl⟩
    have hnv : (p.numVerts : ℝ) ≤ (k.factorial : ℝ) := by
      have := p.nodup.length_le_card
      rw [ProofsRecursion.card_Vtx] at this
      exact_mod_cast this
    have hwt : (0 : ℝ) ≤ (p.wtP : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hnv (ProofsGB2.Rk_nonneg k)]
  have hsInf : sInf {q : ℝ | ∃ p, IsPathComponent p X ∧
      q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)}
      ≤ (pm.wtP : ℝ) - Rk k * (pm.numVerts : ℝ) :=
    csInf_le hBddI ⟨pm, hpmc, rfl⟩
  -- assemble.  `g Cmax = 1 + compMinto Cmax + w(inducedEdges Cmax)`.
  have hgCmax : g Cmax = (1 : ℝ) + (compMinto X Cmax : ℝ)
      + (wEdges (inducedEdges X Cmax) : ℝ) := by rw [hg]
  linarith [hgsum, hsplit, hMTcast, hA_ge, hCmaxcardR, hR23, hwEmaxR, hsInf, hgCmax]

/-- **Xk-nonempty** — `𝒳_k` is nonempty (a Hamiltonian path always exists, via `exists_ham`;
`F` of it lands in `𝒳_k`).  Discharges the `hne_Xk` hypothesis of `b2_of_gives_b2`. -/
theorem Xk_nonempty (k : ℕ) : (Xk k).Nonempty := by
  obtain ⟨P, hP⟩ := ProofsSpine.exists_ham k
  exact ⟨F P, P, hP, rfl⟩

/-- **b2 (final)** — Bound 2, verbatim type, **fully discharged** for `2 ≤ k`.  `prp_gives_b2`
is discharged by `prp_gives_b2_amended`, the `𝒳_k`-nonemptiness by `Xk_nonempty`, and the
`BddBelow` junk-guard by `ProofsGB2.b2Set_bddBelow`.  **Only remaining hypothesis: `2 ≤ k`.** -/
theorem b2_final (hk : 2 ≤ k) :
    (L k : ℝ) ≥ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} :=
  b2_of_gives_b2 hk (fun _X hX => prp_gives_b2_amended hk hX) (Xk_nonempty k)
    (ProofsGB2.b2Set_bddBelow k)

/-- **g-monotonicity (final)** — the `hg_mono` leaf of `proof_thm1v2`, proved outright for the
concrete inner min `ProofsGB2.gInner`.  Only remaining hypothesis: `2 ≤ k`. -/
theorem gInner_mono (hk : 2 ≤ k) (r s : ℝ) (hrs : r ≤ s) :
    r * (k.factorial : ℝ) + ProofsGB2.gInner k r
      ≤ s * (k.factorial : ℝ) + ProofsGB2.gInner k s :=
  ProofsGB2.gInner_mono hk (Xk_nonempty k) r s hrs

/-- **b2 in `gInner` form (final)** — the `hb2red` leaf of `proof_thm1v2`:
`L(k) ≥ R_k·k! + gInner k (R_k)`.  Assembled from `b2_final` and the constant-shift identity
`ProofsGB2.b2Set_sInf_eq`.  Only remaining hypothesis: `2 ≤ k`. -/
theorem b2_gInner (hk : 2 ≤ k) :
    (L k : ℝ) ≥ Rk k * (k.factorial : ℝ) + ProofsGB2.gInner k (Rk k) := by
  have hb2 := b2_final hk
  rwa [ProofsGB2.b2Set_sInf_eq k (ProofsB2.Xk'_nonempty_of_Xk_nonempty hk (Xk_nonempty k))] at hb2

/-- **red-R (tightened)** — take23 l.744 `≥` form, with the `BddBelow` junk-guard `hBddR`
**discharged** (the `i_k`-ratio set is bounded below by `2−k` for `2 ≤ k`; each valid ℓ has
`ℓ > k` so the ratio's denominator is positive and `i_k(ℓ) ≥ 0` bounds the numerator).
Remaining hypotheses: `2 ≤ k`; `hkey` (the `p_u`-extension per-path ratio bound — the genuine
graph-theoretic input, not touched by the `lem_pathrule` unlock); `hne` (the `R_k` value set is
nonempty, i.e. a non-spanning strongly-exitless component exists). -/
theorem red_R_tightened (hk : 2 ≤ k)
    (hkey : ∀ p, p ∈ Xk' k → p.numVerts ≤ k.factorial - k →
        k < p.numVerts + k ∧ HasExitlessPath k (p.numVerts + k) ∧
          ((iExitless k (p.numVerts + k) : ℝ) - (k : ℝ) + 2) /
              (((p.numVerts + k : ℕ) : ℝ) - (k : ℝ))
            ≤ (pValue p : ℝ) / (p.numVerts : ℝ))
    (hne : ∃ p, p ∈ Xk' k ∧ p.numVerts ≤ k.factorial - k) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} := by
  apply Hunter.Proved.red_R hkey hne
  -- discharge `hBddR`: each ratio `≥ 2 − k`.
  refine ⟨(2 : ℝ) - (k : ℝ), ?_⟩
  rintro q ⟨ℓ, hℓ, -, rfl⟩
  have hd1 : (1 : ℝ) ≤ (ℓ : ℝ) - (k : ℝ) := by
    have : ((k : ℕ) + 1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    linarith
  have hd : (0 : ℝ) < (ℓ : ℝ) - (k : ℝ) := by linarith
  have hi : (0 : ℝ) ≤ (iExitless k ℓ : ℝ) := by positivity
  have hk2 : (2 : ℝ) - (k : ℝ) ≤ 0 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [le_div_iff₀ hd]
  nlinarith [hi, hk2, hd1, mul_nonneg (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - (k : ℝ) - 1)
    (by linarith : (0 : ℝ) ≤ (k : ℝ) - 2)]

/-! ## Dashboard tightening — `proof_thm1v2` with the concrete `gInner` -/

/-- **proof-thm1v2 (tightened)** — the §6.4 per-`k` reduction output, with three of
`proof_thm1v2`'s five hypotheses **discharged** here: the abstract `gInner` is pinned to the
concrete `ProofsGB2.gInner k`; `hb2red` is supplied by `b2_gInner`; `hg_mono` by `gInner_mono`.
The **only remaining hypotheses** are the two pivot-evaluation inputs that route through the
open combinatorial leaves (thm2 / greedy_g / `red_R`):
* `hgInner_eval` — the inner min is attained at `ℓ = P` (⟸ `red_pstar` + `prop4`, i.e. thm2 +
  greedy_g + unwinding);
* `hRk_ge` — the pivot ratio `r_P ≤ R_k` (⟸ `red_R` + `prop4`, i.e. the `p_u`-extension). -/
theorem proof_thm1v2_tightened (hk : 3 ≤ k)
    (hpivot : HasExitlessPath k (k * (k - 1) * (k - 2)))
    (hgInner_eval : ProofsGB2.gInner k
          (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
            / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        = (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          - (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
              / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k * (k - 1) * (k - 2) : ℕ) : ℝ))
    (hRk_ge : ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2)
          / (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)) ≤ Rk k) :
    (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
      + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) :=
  Hunter.Proved.proof_thm1v2 hk hpivot (ProofsGB2.gInner k)
    (b2_gInner (by omega)) (gInner_mono (by omega)) hgInner_eval hRk_ge

end Proved

end Hunter


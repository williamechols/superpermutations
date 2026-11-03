/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Bounds

/-!
# Statements-stage auxiliary definitions (Hunter)

This file adds the machinery that the *definitions* pass (`Hunter/`) deliberately deferred
but that the theorem **statements** (`Hunter/Statements.lean`) need in order to be phrased
faithfully.  Every declaration here is a `def`/`abbrev` — **no proof placeholders, no
theorems** (the statements file owns all the placeholder theorem items).  Each choice is
logged in
`AMBIGUITIES.md` under "## Statements-stage additions".

Contents:
* `sigmaInv` — the inverse rotation `σ⁻¹` (needed for `clm-rule2.5`, `red-R`).
* `HasExitlessPath` — "an exitless path on `ℓ` vertices exists" (the existence guard forced
  by the `iExitless … = 0`-on-empty convention, `AMBIGUITIES.md` §E2).
* `IsWalk` — a directed walk in a subgraph `X` (needed for `lem-walking`).
* `IsUnionOfStronglyExitlessPaths` — "`Comps(X)` is a set of strongly exitless paths"
  (the RHS of `prp-Xk-se`, and the conclusion of `cor-exitlessrule`).
* `IsPhiForm` — "`p = φ(c⃗,v⃗)` for some pointed sequence of 1-cycles" (`clm-phi`).
* `edgeCountGe` — the number of `q+`-edges of a path (the appendix edge-count facts
  `prp-1edgebound`/`prp-2edgebound`/`prp-3edgebound`).
* `coeff` — the leading coefficient `1 + 1/k + 1/(k(k−1)) + 1/((k−1)(k(k−1)(k−2)−k))` of
  `thm1v1`/`thm1v2`.
-/

namespace Hunter

open List
open scoped Classical

variable {k : ℕ}

/-- `σ⁻¹` — the inverse of the 1-rotation `σ`, i.e. `rotate (k−1)` (so `σ(σ⁻¹ v) = v` for a
permutation word of length `k`).  Used by `clm-rule2.5` (`into(X,v) = {(σ⁻¹v→v)}`) and by
the `red-R` extension `p_u`. -/
def sigmaInv (v : Vtx k) : Vtx k := ⟨(v : List ℕ).rotate (k - 1), isPermWord_rotate v.2 (k - 1)⟩

/-- "An exitless path on `ℓ` vertices exists."  The `iExitless k ℓ = 0`-on-empty convention
(`AMBIGUITIES.md` §E2) makes every claim `i_k(ℓ) ≥ …` vacuous/false where no such path
exists, so every statement quantifying over `ℓ` in the support of `i_k` carries this guard. -/
def HasExitlessPath (k ℓ : ℕ) : Prop := ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ

/-- A **directed walk** in the subgraph with edge set `X`: a list of vertices whose
consecutive pairs are `X`-edges (`lem-walking`).  Not required to be simple. -/
def IsWalk (X : Finset (Vtx k × Vtx k)) (D : List (Vtx k)) : Prop :=
  D.IsChain (fun a b => (a, b) ∈ X)

/-- "`Comps(X)` is a set of **strongly exitless paths**": every weak component of `X` is the
vertex set of a strongly exitless path-component.  This is the structural RHS of
`prp-Xk-se` and the conclusion of `cor-exitlessrule`. -/
def IsUnionOfStronglyExitlessPaths (X : Finset (Vtx k × Vtx k)) : Prop :=
  ∀ C ∈ Comps X, ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p X ∧ p.StronglyExitless

/-- `p = φ(c⃗,v⃗)` for some **pointed sequence of 1-cycles** (Hunter §6, `def-pointedseq`):
`p`'s vertex list is the concatenation, over a sequence `vs` of vertices lying in
*distinct* 1-cycles, of the full `σ`-orbits `v, σv, …, σ^{k−1}v`.  (Faithful reading of
`φ(c⃗,v⃗)[(i−1)k+(r+1)] = σ^r(v_i)`; the distinct-cycle condition encodes `c⃗` distinct.) -/
def IsPhiForm (p : HPath k) : Prop :=
  ∃ vs : List (Vtx k), (vs.map (fun v => rotClass v.1)).Nodup ∧
    p.verts = (vs.map (fun v => (List.range k).map (fun r => sigma^[r] v))).flatten

/-- The number of `q+`-edges of a path `p` — edges `(p[i]→p[i+1])` of weight `≥ q`
(Hunter appendix; `q = 1,2,3` give `prp-1edgebound`/`prp-2edgebound`/`prp-3edgebound`).
Indices `0 ≤ i < |p|−1` range over the `|p|−1` edges (vertex-count convention). -/
noncomputable def edgeCountGe (p : HPath k) (q : ℕ) : ℕ :=
  ((Finset.range (p.numVerts - 1)).filter (fun i => q ≤ ew k (p.vert i) (p.vert (i + 1)))).card

/-- The leading coefficient of `thm1v1`/`thm1v2`:
`1 + 1/k + 1/(k(k−1)) + 1/((k−1)(k(k−1)(k−2)−k))`.  All arithmetic in `ℝ`. -/
noncomputable def coeff (k : ℕ) : ℝ :=
  1 + 1 / (k : ℝ) + 1 / ((k : ℝ) * ((k : ℝ) - 1)) +
    1 / (((k : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ)))

end Hunter

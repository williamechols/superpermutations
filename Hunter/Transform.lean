/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Paths

/-!
# The path transformation `f(P,S)`, `F`, and the image classes (Hunter §4–§6)

* `SPrecond P S` — the S-precondition `∀ v ∈ S, (v→σv) ∉ E(P)`.
* `firstInCycle`, `C₀`, `C₋₁`, `Sset P` (`= S(P)`).
* `E1removed`,`E2removed` (`= E₁`,`E₂`), `indicatorI` (`= I`), `fPS` (`= f(P,S)`), `F`.
* `Xk` (`= 𝒳_k`), the image of `F` over Hamiltonian paths.
* weak components: `weakConn`, `vertsOf`, `Comps` (each block a vertex-`Finset`),
  `numComps`, `inducedEdges`; `MinThrough`.
* `IsPathComponent`, `Xk'` (`= 𝒳'_k`), the path-components appearing in some `F(P)`.

Modelling choices (subgraphs as edge `Finset`s, components as vertex-`Finset`s, the
`compMinto` reading of `minto` on a component, and the path-component predicate) are all
documented in `AMBIGUITIES.md`.
-/

namespace Hunter

open List
open scoped Classical

variable {k : ℕ}

/-! ## The S-precondition and the construction `S(P)` (§2.7–§2.8) -/

/-- Hunter §2.7: the *S-precondition* — for every `v ∈ S`, the 1-edge `(v→σv)` is not
already an edge of `P`.  Guarantees Step 1 of `f` removes a genuine `≥2`-edge (or nothing)
and never a 1-edge. -/
def SPrecond (P : HPath k) (S : Finset (Vtx k)) : Prop :=
  ∀ v ∈ S, (v, sigma v) ∉ P.edges

/-- Hunter §2.8: `v` is *first in its cycle* under `P` — reached by `P` no later than any
other vertex of its 1-cycle `c(v)` (same rotation class). -/
def firstInCycle (P : HPath k) (v : Vtx k) : Prop :=
  ∀ u : Vtx k, rotClass u.1 = rotClass v.1 → P.pos v ≤ P.pos u

/-- Hunter §2.8: `C₀`, the vertices first in their cycles (one per 1-cycle). -/
noncomputable def C0 (P : HPath k) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => firstInCycle P v)

/-- Hunter §2.8: `C₋₁ = {v : σ(v) ∈ C₀}`, the "last-before-first" vertices. -/
noncomputable def Cm1 (P : HPath k) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => sigma v ∈ C0 P)

/-- Hunter §2.8: `S(P) = { v : v ∉ C₋₁ and (v→σv) ∉ E(P) }`.  Satisfies `SPrecond`. -/
noncomputable def Sset (P : HPath k) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => v ∉ Cm1 P ∧ (v, sigma v) ∉ P.edges)

/-! ## The transformation `f(P,S)` (§2.7) -/

/-- Hunter §2.7, `E₁`: the edges removed in Step 1, `= out(P, v)` over `v ∈ S`, i.e. the
`P`-edges whose source lies in `S`. -/
noncomputable def E1removed (P : HPath k) (S : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  P.edges.filter (fun e => e.1 ∈ S)

/-- The 1-edges `(v→σv)` added in Step 1 of `f`. -/
noncomputable def addedEdges (S : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  S.image (fun v => (v, sigma v))

/-- The intermediate graph after Step 1 of `f`: remove `E₁`, add the 1-edges. -/
noncomputable def Xstep1 (P : HPath k) (S : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  (P.edges \ E1removed P S) ∪ addedEdges S

/-- The Step-2 vertices: those `u` with `|into(X₁, u)| = 2` (the added 1-edge and the
original `P`-in-edge both point at `u`). -/
noncomputable def doubles (P : HPath k) (S : Finset (Vtx k)) : Finset (Vtx k) :=
  Finset.univ.filter (fun u => (intoV (Xstep1 P S) u).card = 2)

/-- Hunter §2.7, `E₂`: the edges removed in Step 2, `= into(P, u)` over the Step-2 vertices
`u` (the original `P`-in-edge overridden by the added 1-edge). -/
noncomputable def E2removed (P : HPath k) (S : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  P.edges.filter (fun e => e.2 ∈ doubles P S)

/-- Hunter §2.7: `X = f(P,S)` — Step 0 `E(X):=E(P)`; Step 1 swap `out(P,v)` for `(v→σv)`
over `v ∈ S`; Step 2 delete the overridden `P`-in-edges. -/
noncomputable def fPS (P : HPath k) (S : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  Xstep1 P S \ E2removed P S

/-- Hunter §2.7: `I = 𝟙[P[|P|] ∈ S]`, the indicator that the head of `P` lies in `S`. -/
noncomputable def indicatorI (P : HPath k) (S : Finset (Vtx k)) : ℕ :=
  if P.last ∈ S then 1 else 0

/-- Hunter §2.8: `F(P) = f(P, S(P))`. -/
noncomputable def F (P : HPath k) : Finset (Vtx k × Vtx k) := fPS P (Sset P)

/-- Hunter §2.8: `𝒳_k` = image of `F` over all Hamiltonian paths of `𝒮_k`. -/
def Xk (k : ℕ) : Set (Finset (Vtx k × Vtx k)) :=
  {X | ∃ P : HPath k, P.IsHamiltonian ∧ F P = X}

/-! ## Weak components `Comps(G)` (§2.1) -/

/-- One undirected step in a subgraph `X` (either orientation of an `X`-edge). -/
def weakStep (X : Finset (Vtx k × Vtx k)) (u v : Vtx k) : Prop :=
  (u, v) ∈ X ∨ (v, u) ∈ X

/-- Weak connectivity in `X`: the reflexive-transitive closure of `weakStep` (which is
symmetric, so this is the "connected if edges were undirected" equivalence of §2.1). -/
def weakConn (X : Finset (Vtx k × Vtx k)) : Vtx k → Vtx k → Prop :=
  Relation.ReflTransGen (weakStep X)

/-- The vertices incident to some edge of `X` (`= V(G)` for the subgraph `G` with edge set
`X`). -/
noncomputable def vertsOf (X : Finset (Vtx k × Vtx k)) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => ∃ e ∈ X, v = e.1 ∨ v = e.2)

/-- Hunter §2.1: `Comps(X)`, the weakly connected components of the subgraph with edge set
`X`, each as the vertex-`Finset` of its block (labelled vertices, so isomorphic disjoint
blocks are distinct — the `\edit` intent of §2.1).  Isolated vertices (in no edge) are
excluded via `vertsOf`.  See `AMBIGUITIES.md`. -/
noncomputable def Comps (X : Finset (Vtx k × Vtx k)) : Finset (Finset (Vtx k)) :=
  (vertsOf X).image (fun v => (vertsOf X).filter (fun u => weakConn X v u))

/-- Hunter §2.3/§"Bounds": `|Comps(X)|`, the number of weak components. -/
noncomputable def numComps (X : Finset (Vtx k × Vtx k)) : ℕ := (Comps X).card

/-- The edges of `X` induced on a component `C` (each block "carries its induced edges",
§2.1).  On a weak component `C` is closed, so `e.1 ∈ C ↔ e.2 ∈ C`. -/
noncomputable def inducedEdges (X : Finset (Vtx k × Vtx k)) (C : Finset (Vtx k)) :
    Finset (Vtx k × Vtx k) := X.filter (fun e => e.1 ∈ C)

/-! ## `MinThrough` (§2.5) -/

/-- The in-degree-0 vertices of a component `C` under `X` (its *tails*; for a path
component, the singleton `{p[1]}`). -/
noncomputable def compTails (X : Finset (Vtx k × Vtx k)) (C : Finset (Vtx k)) :
    Finset (Vtx k) := C.filter (fun v => intoV X v = ∅)

/-- `minto` of a component `C` of `X`: the cheapest edge into a tail of `C` from outside
`C`.  For a path component (unique tail `= p[1]`) this equals `minto p`; for a cyclic
component (no tail) the value is `0` via `Nat.sInf ∅ = 0`.  See `AMBIGUITIES.md`. -/
noncomputable def compMinto (X : Finset (Vtx k × Vtx k)) (C : Finset (Vtx k)) : ℕ :=
  sInf {d | ∃ v : Vtx k, v ∉ C ∧ ∃ s ∈ compTails X C, ew k v s = d}

/-- Hunter §2.5: `MinThrough(X) = (Σ_{C∈Comps} minto(C)) − max_{C} minto(C)`, with value
`0` when `X` has `≤ 1` component (the "single Hamiltonian path" special case, and the empty
case).  The ℕ subtraction is exact since `max ≤ Σ`.  See `AMBIGUITIES.md`. -/
noncomputable def MinThrough (X : Finset (Vtx k × Vtx k)) : ℕ :=
  if (Comps X).card ≤ 1 then 0
  else (∑ C ∈ Comps X, compMinto X C) - (Comps X).sup (fun C => compMinto X C)

/-! ## Path-components and `𝒳'_k` (§2.8) -/

/-- `p` is a *path-component* of `X`: its edges lie in `X`, and `V(p)` is a full weak
component (no `X`-edge crosses its boundary, and every internal `X`-edge is a path edge).
Combined with `p` being a simple path, `V(p)` is exactly one weak component realized as a
directed path. -/
def IsPathComponent (p : HPath k) (X : Finset (Vtx k × Vtx k)) : Prop :=
  p.edges ⊆ X ∧
    (∀ e ∈ X, (e.1 ∈ p.vertsFinset ↔ e.2 ∈ p.vertsFinset)) ∧
    (∀ e ∈ X, e.1 ∈ p.vertsFinset → e ∈ p.edges)

/-- Hunter §2.8: `𝒳'_k = ⋃_{X∈𝒳_k} Comps(X)` — the path-components appearing in some
`F(P)`.  Elements are paths (`HPath`), the objects over which `R_k` and the reductions
range.  See `AMBIGUITIES.md` for why this is `Set (HPath k)` rather than a set of
vertex-`Finset`s. -/
def Xk' (k : ℕ) : Set (HPath k) :=
  {p | ∃ X ∈ Xk k, IsPathComponent p X}

/-! ## Small free lemmas -/

theorem sset_sPrecond (P : HPath k) : SPrecond P (Sset P) := by
  intro v hv
  rw [Sset, Finset.mem_filter] at hv
  exact hv.2.2

theorem fPS_subset_step1 (P : HPath k) (S : Finset (Vtx k)) :
    fPS P S ⊆ Xstep1 P S := Finset.sdiff_subset

theorem E1removed_subset (P : HPath k) (S : Finset (Vtx k)) :
    E1removed P S ⊆ P.edges := Finset.filter_subset _ _

theorem E2removed_subset (P : HPath k) (S : Finset (Vtx k)) :
    E2removed P S ⊆ P.edges := Finset.filter_subset _ _

end Hunter

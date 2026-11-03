/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Words

/-!
# The graph `𝒮_k` and the weight `w` (Hunter §2.2–§2.3)

`𝒮_k` is the **complete loopless weighted digraph** whose vertices are the permutations of
`[k]`.  We model:

* `Vtx k` — the vertex set `V(𝒮_k)`, the subtype of permutation words.  It is a `Fintype`
  with `DecidableEq`, so subgraphs can be modelled as `Finset (Vtx k × Vtx k)`.
* `ew k u v` — Hunter's edge weight `w(u→v)` (`= wt`).  Every ordered pair of distinct
  vertices is an edge (`Sgraph k`), so `𝒮_k` is complete.
* `sigma`,`tau`,`alpha` — the successors `σ`,`τ`,`α` as vertex maps.
* `cyc v` — the 1-cycle `c(v)` (the `σ`-orbit = the rotation class of `v`).
* subgraph API: `out`,`into`, heads `H` / tails `T`, and the edge-set weight `wEdges`.

`open Classical` is used so that quotient-valued predicates (rotation-class equality) are
decidable; consequently several definitions are `noncomputable` (harmless — the whole
development is).
-/

namespace Hunter

open List
open scoped Classical

variable {k : ℕ}

/-- Hunter §2.2: the vertex set `V(𝒮_k)` — the permutations of `[k]`, as a subtype of
words.  It is finite (`permWords_finite`), so we equip it with a `Fintype`. -/
abbrev Vtx (k : ℕ) : Type := {w : List ℕ // IsPermWord k w}

noncomputable instance instFintypeVtx (k : ℕ) : Fintype (Vtx k) :=
  (permWords_finite k).fintype

/-- Hunter §2.2, the edge weight `w(u→v)` (the digest: "equals Hunter's `w` verbatim"). -/
noncomputable def ew (k : ℕ) (u v : Vtx k) : ℕ := wt k u.1 v.1

/-- Hunter §2.2: `𝒮_k` is the complete loopless digraph — its edge set is every ordered
pair of *distinct* vertices. -/
noncomputable def Sgraph (k : ℕ) : Finset (Vtx k × Vtx k) :=
  Finset.univ.filter (fun e => e.1 ≠ e.2)

/-- Hunter §2.2 `σ` (the unique weight-1 out-edge target): the cyclic rotation `rho`. -/
def sigma (v : Vtx k) : Vtx k := ⟨(v : List ℕ).rotate 1, isPermWord_rotate v.2 1⟩

/-- Hunter §2.2 `τ` (a weight-2 out-edge target, not `σ²`): the `door`.  For `k < 2` the
door of a permutation word need not be a permutation word, so we fall back to the identity
(see `AMBIGUITIES.md`); for `k ≥ 2` this is exactly `door`. -/
noncomputable def tau (v : Vtx k) : Vtx k :=
  if h : IsPermWord k (door v.1) then ⟨door v.1, h⟩ else v

/-- Hunter §2.2 `α` (a specific weight-3 out-edge target): reverse the first three symbols
to the back.  Always a permutation word, so this is total with no side condition. -/
noncomputable def alpha (v : Vtx k) : Vtx k := ⟨alphaWord v.1, alphaWord_isPermWord v.2⟩

/-- Hunter §2.2/§5: the 1-cycle `c(v) = {v, σv, …, σ^{k−1}v}` — the `σ`-orbit, equivalently
the rotation class of `v` (Coeff2 `rotClass`).  The 1-cycles partition `V(𝒮_k)`. -/
noncomputable def cyc (v : Vtx k) : Finset (Vtx k) :=
  Finset.univ.filter (fun u => rotClass u.1 = rotClass v.1)

/-! ## Subgraphs: `into`, `out`, heads, tails, and the edge-set weight (§2.3, §2.7)

A subgraph of `𝒮_k` is modelled by its edge set `X : Finset (Vtx k × Vtx k)`.  Hunter's
`into`/`out` are always relative to such an `X`. -/

/-- Hunter §2.3: `out(X, U) = Ē_X(U, V) = {(u→v) ∈ X : u ∈ U}`, the edges of `X` leaving
`U`. -/
def out (X : Finset (Vtx k × Vtx k)) (U : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  X.filter (fun e => e.1 ∈ U)

/-- Hunter §2.3: `into(X, U) = Ē_X(V, U) = {(u→v) ∈ X : v ∈ U}`, the edges of `X` entering
`U`. -/
def into (X : Finset (Vtx k × Vtx k)) (U : Finset (Vtx k)) : Finset (Vtx k × Vtx k) :=
  X.filter (fun e => e.2 ∈ U)

/-- Hunter §2.3 shorthand `out(X, v) := out(X, {v})`. -/
def outV (X : Finset (Vtx k × Vtx k)) (v : Vtx k) : Finset (Vtx k × Vtx k) := out X {v}

/-- Hunter §2.3 shorthand `into(X, v) := into(X, {v})`. -/
def intoV (X : Finset (Vtx k × Vtx k)) (v : Vtx k) : Finset (Vtx k × Vtx k) := into X {v}

/-- Hunter §2.7: `H(X) = {v : out(X, v) = ∅}`, the *heads* (out-degree 0). -/
noncomputable def heads (X : Finset (Vtx k × Vtx k)) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => outV X v = ∅)

/-- Hunter §2.7: `T(X) = {v : into(X, v) = ∅}`, the *tails* (in-degree 0). -/
noncomputable def tails (X : Finset (Vtx k × Vtx k)) : Finset (Vtx k) :=
  Finset.univ.filter (fun v => intoV X v = ∅)

/-- Hunter §2.3: `w(S) = Σ_{e∈S} w(e)`, the total weight of an edge set. -/
noncomputable def wEdges (S : Finset (Vtx k × Vtx k)) : ℕ :=
  ∑ e ∈ S, ew k e.1 e.2

/-! ## Small unfolding / free lemmas -/

@[simp] theorem mem_out {X : Finset (Vtx k × Vtx k)} {U : Finset (Vtx k)} {e} :
    e ∈ out X U ↔ e ∈ X ∧ e.1 ∈ U := Finset.mem_filter

@[simp] theorem mem_into {X : Finset (Vtx k × Vtx k)} {U : Finset (Vtx k)} {e} :
    e ∈ into X U ↔ e ∈ X ∧ e.2 ∈ U := Finset.mem_filter

theorem out_subset {X : Finset (Vtx k × Vtx k)} {U} : out X U ⊆ X := Finset.filter_subset _ _

theorem into_subset {X : Finset (Vtx k × Vtx k)} {U} : into X U ⊆ X := Finset.filter_subset _ _

/-- Hunter §2.2: `σ` is the weight-1 successor, `w(v → σv) = 1` (for `k ≥ 1`). -/
theorem ew_sigma (hk : 1 ≤ k) (v : Vtx k) : ew k v (sigma v) = 1 :=
  wt_rho hk v.2

/-- The `tau` map is the door on its underlying word once the door is a permutation word
(in particular for `k ≥ 2`). -/
theorem tau_val_of_door {v : Vtx k} (h : IsPermWord k (door v.1)) :
    (tau v).1 = door v.1 := by
  rw [tau, dif_pos h]

end Hunter

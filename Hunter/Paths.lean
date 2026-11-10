/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Graph

/-!
# Vertex-simple paths and (strongly) exitless paths (Hunter §2.4–§2.5)

Hunter's paths are **vertex-simple directed paths** in the complete digraph `𝒮_k`: a
sequence of distinct vertices, with *no* per-edge constraint (every ordered pair is an edge
of `𝒮_k`).  This is why we do **not** reuse Coeff2's `Walk` (whose `chain : IsChain
ProperStep` field is wrong for the complete graph); see `AMBIGUITIES.md`.

* `HPath k` — a nonempty, duplicate-free vertex list.
* `numVerts` (`= |p|`, vertex count), `vert`, `first`/`last`, `pos` (`= p⁻¹`, with the
  sentinel `numVerts` for `v ∉ p`, encoding `∞`), `verts`/`edges` as sets, `wtP` (`= w(p)`).
* `IsHamiltonian`.
* `EarlyExit`, `Exitless`, `StronglyExitless`, and the alternative "union of full 1-cycles"
  characterization `IsUnionOfCycles`.
* `minto`.
-/

namespace Hunter

open List
open scoped Classical

variable {k : ℕ}

/-- Hunter §2.4: a *path* `p = v₁,…,v_x` is a nonempty sequence of **distinct** vertices
(a simple directed path in `𝒮_k`). -/
structure HPath (k : ℕ) where
  /-- The vertices `v₁,…,v_x`, in order (0-based indexing below). -/
  verts : List (Vtx k)
  ne : verts ≠ []
  nodup : verts.Nodup

namespace HPath

/-- Hunter §2.4: `|p| = x`, the number of **vertices**. -/
def numVerts (p : HPath k) : ℕ := p.verts.length

theorem numVerts_pos (p : HPath k) : 0 < p.numVerts :=
  List.length_pos_of_ne_nil p.ne

/-- The vertex `p[t+1]` at 0-based time `t`; junk value is `p`'s first vertex for
`t ≥ |p|`. -/
def vert (p : HPath k) (t : ℕ) : Vtx k := p.verts.getD t (p.verts.head p.ne)

/-- Hunter §2.4: `p[1]`, the first (start) vertex. -/
def first (p : HPath k) : Vtx k := p.verts.head p.ne

/-- Hunter §2.4/§2.7: `p[|p|]`, the last vertex = the unique *head* of `p` (out-degree 0). -/
def last (p : HPath k) : Vtx k := p.verts.getLast p.ne

/-- Hunter §2.4: `V(p)`, the vertex set of the path. -/
def vertsFinset (p : HPath k) : Finset (Vtx k) := p.verts.toFinset

/-- Hunter §2.4: `E(p) = {(p[i]→p[i+1])}`, the edge set of the path. -/
def edges (p : HPath k) : Finset (Vtx k × Vtx k) := (p.verts.zip p.verts.tail).toFinset

/-- Hunter §2.4: `p⁻¹[v]` — the (0-based) position of `v` in `p`, with sentinel value `|p|`
for `v ∉ p` (a finite stand-in for the paper's `p⁻¹[v] = ∞`; any real position is `< |p|`,
so the sentinel compares as `+∞`; see `AMBIGUITIES.md`). -/
def pos (p : HPath k) (v : Vtx k) : ℕ := p.verts.idxOf v

/-- Hunter §2.3: `w(p) = Σ_{i} w(p[i]→p[i+1])`, the total path weight (`= w(E(p))`). -/
noncomputable def wtP (p : HPath k) : ℕ := (p.verts.zipWith (ew k) p.verts.tail).sum

/-- Hunter §2.6: `p` is *Hamiltonian* if it visits every vertex of `𝒮_k`. -/
def IsHamiltonian (p : HPath k) : Prop := ∀ v : Vtx k, v ∈ p.verts

/-! ## Early exits and exitless paths (§2.4) -/

/-- Hunter §2.4: `p` contains an *early exit* if at some vertex `v = p[i]` it leaves via an
edge of weight `≥ 2` (`w(out(p,v)) > 1`) while the weight-1 successor `σ(v)` has not yet
been reached (`p⁻¹[v] < p⁻¹[σ(v)]`) — i.e. it left a 1-cycle prematurely.  (A path head
`v = p[|p|]` has `out(p,v) = ∅`, weight `0`, and is excluded by `i+1 < |p|`.) -/
def EarlyExit (p : HPath k) : Prop :=
  ∃ i, i + 1 < p.numVerts ∧ 2 ≤ ew k (p.vert i) (p.vert (i + 1)) ∧
    i < p.pos (sigma (p.vert i))

/-- Hunter §2.4: `p` is *exitless* if it has no early exit. -/
def Exitless (p : HPath k) : Prop := ¬ EarlyExit p

/-- Hunter §2.4: `p` is *strongly exitless* if it is exitless **and** cannot be extended by
a 1-edge at its last vertex, i.e. `σ(p[|p|]) ∈ p` (Daniel Carter: "complete exitless"). -/
def StronglyExitless (p : HPath k) : Prop :=
  Exitless p ∧ sigma p.last ∈ p.verts

/-- Hunter §6 (clm-1cyclesubset): the alternative characterization of strongly exitless
paths — a path is a **disjoint union of full 1-cycles**, i.e. `∀ v ∈ p, c(v) ⊆ V(p)`.
The paper proves `StronglyExitless p → IsUnionOfCycles p` (and, via `φ`, a converse); the
equivalence is a theorem proved later in the development, so both characterizations are recorded here as
definitions.  See `AMBIGUITIES.md`. -/
def IsUnionOfCycles (p : HPath k) : Prop :=
  ∀ v ∈ p.verts, cyc v ⊆ p.vertsFinset

/-! ## `minto` (§2.5) -/

/-- Hunter §2.5: `minto(p) = min{ w(v→p[1]) : v ∈ V(𝒮_k) ∖ V(p) }`, the cheapest edge into
the start of `p` from outside `p`.  Defined for all `p` via `sInf`; when `V(p) = V(𝒮_k)`
(a Hamiltonian path) the index set is empty and `minto p = 0` by the `Nat.sInf ∅ = 0`
convention (the paper only uses `minto` when `V(p) ≠ V(𝒮_k)`).  See `AMBIGUITIES.md`. -/
noncomputable def minto (p : HPath k) : ℕ :=
  sInf {d | ∃ v : Vtx k, v ∉ p.verts ∧ ew k v p.first = d}

/-! ## Small free lemmas -/

theorem vert_zero (p : HPath k) : p.vert 0 = p.first := by
  obtain ⟨a, t, h⟩ := List.exists_cons_of_ne_nil p.ne
  simp only [vert, first, h, List.getD_cons_zero, List.head_cons]

theorem first_mem (p : HPath k) : p.first ∈ p.verts := by
  rw [first]; exact List.head_mem p.ne

theorem last_mem (p : HPath k) : p.last ∈ p.verts := by
  rw [last]; exact List.getLast_mem p.ne

@[simp] theorem mem_vertsFinset {p : HPath k} {v : Vtx k} :
    v ∈ p.vertsFinset ↔ v ∈ p.verts := List.mem_toFinset

theorem numVerts_eq_card_of_hamiltonian {p : HPath k} (h : p.IsHamiltonian) :
    p.numVerts = Fintype.card (Vtx k) := by
  rw [numVerts, ← List.toFinset_card_of_nodup p.nodup]
  congr 1
  apply Finset.eq_univ_of_forall
  intro v; exact List.mem_toFinset.mpr (h v)

end HPath

end Hunter

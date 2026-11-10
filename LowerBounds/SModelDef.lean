import Hunter.Graph
import LowerBounds.ChainCapacityC

/-!
# Model chains: the object that the window search enumerates

A *model chain* is what remains of an exact weight-three chain of a strongly exitless path when
everything is forgotten except the entries of its blocks:

* a chain is a list of pieces, a piece is the non-empty list of the entries of its blocks
  (permutation words, `Vtx k`), at most `k - 1` of them;
* inside a piece, the exit of a block (its entry rotated by `k - 1`) overlaps the entry of the next
  block in `k - 2` symbols (`SLink k 2`: what an edge of weight 2 gives);
* the exit of the last block of a piece overlaps the entry of the first block of the next piece in
  `k - 3` symbols (`SLink k 3`: what an edge of weight 3 gives);
* the entries of all blocks of the chain lie in different rotation classes.

Nothing else is asked: pieces need not be maximal, the first entry is arbitrary, and no geometric
fact (run bounds, the unit rule) is part of the model.  `ModelStatement k cn bn q` is the window
bound for every model chain whose list of deficits is a window; `SModel.lean` derives it from a
finite search on numbers.

This file contains the definitions only, so that the bridge to Liu's chains can be written against
them.  The field names are those of `EntriesChain` (`SBridgeChain.lean`), which is the same
structure with the door given as an equation and the seam as a weight.
-/

namespace SuperpermLowerBounds

open Hunter

/-- The exit of the block entered at `u` (the word of `u` rotated by `k - 1`) and the word of `v`
overlap in `k - d` symbols: the word of the exit without its first `d` symbols is the beginning of
the word of `v`.  An edge of weight `d` from the exit to `v` gives this (`sLink_of_ew`). -/
def SLink (k d : ℕ) (u v : Vtx k) : Prop :=
  ((u : List ℕ).rotate (k - 1)).drop d = (v : List ℕ).take (k - d)

/-- A model chain, as the list of its pieces; a piece is the list of the entries of its blocks. -/
structure IsModelChain (k : ℕ) (L : List (List (Vtx k))) : Prop where
  /-- every piece has a block -/
  pieces_ne : ∀ P ∈ L, P ≠ []
  /-- a piece has at most `k - 1` blocks -/
  size_le : ∀ P ∈ L, P.length ≤ k - 1
  /-- consecutive blocks of a piece: the boundary has an overlap of `k - 2` symbols -/
  doors : ∀ P ∈ L, List.IsChain (SLink k 2) P
  /-- consecutive pieces: the boundary from the last block of the first to the first block of the
  second has an overlap of `k - 3` symbols -/
  seams : List.IsChain
    (fun P Q => ∀ (hP : P ≠ []) (hQ : Q ≠ []), SLink k 3 (P.getLast hP) (Q.head hQ)) L
  /-- the entries of all blocks of the chain lie in different rotation classes -/
  classes : List.Pairwise (fun u v : Vtx k => ¬ ((u : List ℕ) ~r (v : List ℕ))) L.flatten

/-- The deficits of the pieces, in order: `k - 1` minus the number of blocks. -/
def modelDeficits (k : ℕ) (L : List (List (Vtx k))) : List ℕ :=
  L.map fun P => k - 1 - P.length

/-- Every model chain whose list of deficits is a window satisfies the window bound with
`c = cn / q`, `b = bn / q`. -/
def ModelStatement (k cn bn q : ℕ) : Prop :=
  ∀ L : List (List (Vtx k)), IsModelChain k L →
    ChainC.IsWindow (modelDeficits k L) → ChainC.WindowBound k cn bn q (modelDeficits k L)

/-- An edge of weight `d ≥ 1` from `x` to `v`: the word of `x` without its first `d` symbols is
the beginning of the word of `v`. -/
theorem overlap_of_ew {k d : ℕ} {x v : Vtx k} (hd : 1 ≤ d) (h : ew k x v = d) :
    (x : List ℕ).drop d = (v : List ℕ).take (k - d) := by
  unfold ew wt at h
  have hne : {d | 1 ≤ d ∧ d ≤ k ∧ (x : List ℕ).drop d = (v : List ℕ).take (k - d)}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Nat.sInf_empty] at h
    omega
  have hmem := Nat.sInf_mem hne
  rw [h] at hmem
  exact hmem.2.2

/-- The link between two block entries, from the weight of the edge from the exit `x` of the
first to the second. -/
theorem sLink_of_ew {k d : ℕ} {u v x : Vtx k} (hx : (x : List ℕ) = (u : List ℕ).rotate (k - 1))
    (hd : 1 ≤ d) (h : ew k x v = d) : SLink k d u v := by
  unfold SLink
  rw [← hx]
  exact overlap_of_ew hd h

end SuperpermLowerBounds

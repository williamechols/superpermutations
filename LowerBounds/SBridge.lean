import LowerBounds.SBridgeChain
import LowerBounds.SModelDef
import LowerBounds.ComponentCapacityC

/-!
# From the model to Liu's chains

Every exact weight-three chain of a strongly exitless path is a model chain
(`SModelDef.lean`) with the same list of deficits: the pieces of the model chain are the lists
of the entries of the blocks of the pieces of the chain (`pieceEntries`).

* `EntriesChain.isModelChain`: an `EntriesChain` is a model chain (the door `tau2V` begins with
  the exit without its first two symbols; an edge of weight 3 gives an overlap of `k - 3`
  symbols).
* `chain_isModelChain`, `chain_modelDeficits`: the model chain of a chain and its deficits.
* `hStatement_of_model`: `ModelStatement k cn bn q → HStatement k cn bn q`, for `4 ≤ k`
  (stated also with `5 ≤ k`, the bound of Theorem C).

The bound `4 ≤ k` is used in one place: a piece has at most `k - 1` blocks
(`actualIntervalPieceSpan_size_le` of the preimage-chain library).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- The door of the exit of the block entered at `a` begins with the exit without its first two
symbols. -/
theorem sLink_two_tau2V (hk : 2 ≤ k) (a : Vtx k) : SLink k 2 a (tau2V a) := by
  unfold SLink
  rw [tau2V_val hk]
  change ((a : List ℕ).rotate (k - 1)).drop 2 =
    (door ((a : List ℕ).rotate (k - 1))).take (k - 2)
  unfold door
  rw [List.take_left' (by rw [List.length_drop, List.length_rotate, a.2.length])]

/-- An edge of weight 3 from the exit of the block entered at `u` to `v` gives an overlap of
`k - 3` symbols. -/
theorem sLink_three_of_ew {u v : Vtx k} (h : ew k (sigmaInv u) v = 3) : SLink k 3 u v :=
  sLink_of_ew (x := sigmaInv u) rfl (by omega) h

/-- An `EntriesChain` is a model chain. -/
theorem EntriesChain.isModelChain (hk : 2 ≤ k) {L : List (List (Vtx k))}
    (h : EntriesChain k L) : IsModelChain k L where
  pieces_ne := h.pieces_ne
  size_le := h.size_le
  doors := fun P hP => List.IsChain.imp
    (fun a b hab => by rw [hab]; exact sLink_two_tau2V hk a) (h.doors P hP)
  seams := List.IsChain.imp
    (fun _ _ hPQ hP hQ => sLink_three_of_ew (hPQ hP hQ)) h.seams
  classes := h.classes

variable {p : HPath k}

/-- The lists of block entries of the pieces of an exact weight-three chain of a strongly
exitless path form a model chain. -/
theorem chain_isModelChain (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    IsModelChain k (chain.pieces.map pieceEntries) :=
  (chain_entriesChain hk hp chain).isModelChain (by omega)

/-- The deficits of that model chain are the deficits of the pieces of the chain. -/
theorem chain_modelDeficits (chain : ExactWeightThreePieceChain p) :
    modelDeficits k (chain.pieces.map pieceEntries) =
      chain.pieces.map ComponentIntervalPiece.deficit :=
  (chain_deficits chain).symm

/-- Every exact weight-three chain of a strongly exitless path is a model chain with the same
list of deficits. -/
theorem exists_modelChain_of_chain (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ∃ L : List (List (Vtx k)), IsModelChain k L ∧
      modelDeficits k L = chain.pieces.map ComponentIntervalPiece.deficit :=
  ⟨chain.pieces.map pieceEntries, chain_isModelChain hk hp chain, chain_modelDeficits chain⟩

/-- The window bound for all model chains gives the hypothesis of Theorem C (`4 ≤ k`). -/
theorem hStatement_of_model_four {cn bn q : ℕ} (hk : 4 ≤ k)
    (h : ModelStatement k cn bn q) : HStatement k cn bn q := by
  intro p hp chain hw
  rw [← chain_modelDeficits chain] at hw ⊢
  exact h _ (chain_isModelChain hk hp chain) hw

/-- The window bound for all model chains gives the hypothesis of Theorem C. -/
theorem hStatement_of_model {k cn bn q : ℕ} (hk : 5 ≤ k) :
    ModelStatement k cn bn q → HStatement k cn bn q :=
  hStatement_of_model_four (by omega)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.sLink_two_tau2V
#print axioms SuperpermLowerBounds.EntriesChain.isModelChain
#print axioms SuperpermLowerBounds.chain_isModelChain
#print axioms SuperpermLowerBounds.chain_modelDeficits
#print axioms SuperpermLowerBounds.exists_modelChain_of_chain
#print axioms SuperpermLowerBounds.hStatement_of_model_four
#print axioms SuperpermLowerBounds.hStatement_of_model

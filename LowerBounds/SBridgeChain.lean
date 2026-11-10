import LowerBounds.SBridgePath

/-!
# The block entries of a chain of pieces

For a list of pieces of a strongly exitless path, joined by seams of weight exactly 3 (as in an
`ExactWeightThreePieceChain`), this file writes down the vertices that describe it:
`pieceEntries piece` is the list of the entries of the blocks of a piece, in order.

* `pieceEntries_eq_iterate`: the entries of a piece are `v, tau2V v, tau2V² v, …`.
* `pieces_join_ew`: between consecutive pieces, the edge from the exit of the last entry of one
  piece to the first entry of the next has weight 3.
* `pieces_flatten`: the entries of all pieces, concatenated, are the entries of consecutive
  blocks of the path.
* `pieces_pairwise_not_isRotated`: they are pairwise in different rotation classes.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ} {p : HPath k}

/-- The entries of the blocks of a piece, in order. -/
def pieceEntries (piece : ComponentIntervalPiece p) : List (Vtx k) :=
  (List.range' piece.start piece.size).map (blockEntry p)

@[simp] theorem pieceEntries_length (piece : ComponentIntervalPiece p) :
    (pieceEntries piece).length = piece.size := by
  simp [pieceEntries]

theorem pieceEntries_ne_nil (piece : ComponentIntervalPiece p) : pieceEntries piece ≠ [] := by
  intro h
  have hlen := pieceEntries_length piece
  rw [h] at hlen
  have := piece_size_pos piece
  simp at hlen
  omega

theorem pieceEntries_getElem (piece : ComponentIntervalPiece p) (l : ℕ)
    (hl : l < (pieceEntries piece).length) :
    (pieceEntries piece)[l] = blockEntry p (piece.start + l) := by
  simp [pieceEntries]

theorem pieceEntries_head (piece : ComponentIntervalPiece p) :
    (pieceEntries piece).head (pieceEntries_ne_nil piece) = blockEntry p piece.start := by
  rw [List.head_eq_getElem]
  rw [pieceEntries_getElem]
  rfl

theorem pieceEntries_getLast (piece : ComponentIntervalPiece p) :
    (pieceEntries piece).getLast (pieceEntries_ne_nil piece) =
      blockEntry p (piece.start + (piece.size - 1)) := by
  rw [List.getLast_eq_getElem]
  rw [pieceEntries_getElem]
  rw [pieceEntries_length]

/-- The deficit of a piece from its list of entries. -/
theorem piece_deficit_eq_entries (piece : ComponentIntervalPiece p) :
    piece.deficit = k - 1 - (pieceEntries piece).length := by
  rw [pieceEntries_length]
  rfl

/-- The entries of a piece are `v, tau2V v, tau2V² v, …` for its first entry `v`. -/
theorem pieceEntries_eq_iterate (hk : 2 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) :
    pieceEntries piece = List.iterate tau2V (blockEntry p piece.start) piece.size := by
  apply List.ext_getElem
  · simp
  · intro l h1 h2
    rw [pieceEntries_getElem, List.getElem_iterate]
    exact piece_blockEntry hk hp piece (by simpa using h1)

/-- Inside a piece each entry is `tau2V` of the one before. -/
theorem pieceEntries_isChain (hk : 2 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) :
    List.IsChain (fun a b => b = tau2V a) (pieceEntries piece) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  rw [pieceEntries_getElem, pieceEntries_getElem]
  exact piece_blockEntry_succ hk hp piece (by simpa using hi)

/-- Between two pieces joined by a seam of weight 3: the edge from the exit of the last entry
of the first piece to the first entry of the second has weight 3. -/
theorem pieceEntries_join_ew (hk : 1 ≤ k) (hp : p.StronglyExitless)
    {left right : ComponentIntervalPiece p} (hjoin : ExactPieceAdjacent left right) :
    ew k (sigmaInv ((pieceEntries left).getLast (pieceEntries_ne_nil left)))
      ((pieceEntries right).head (pieceEntries_ne_nil right)) = 3 := by
  rw [pieceEntries_getLast, pieceEntries_head]
  exact piece_join_ew hk hp hjoin

/-- The entries of a list of consecutive pieces, concatenated, are the entries of consecutive
blocks of the path. -/
theorem pieces_flatten (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    ∀ (ps : List (ComponentIntervalPiece p)) (hne : ps ≠ []),
      Adjacent ExactPieceAdjacent ps →
      ∃ n, (ps.map pieceEntries).flatten =
          (List.range' (ps.head hne).start n).map (blockEntry p) ∧
        ∀ i, i < n → k * ((ps.head hne).start + i) < p.numVerts := by
  intro ps
  induction ps with
  | nil => intro hne; exact absurd rfl hne
  | cons x rest ih =>
      intro _ hadj
      cases rest with
      | nil =>
          refine ⟨x.size, ?_, ?_⟩
          · simp [pieceEntries]
          · intro i hi
            exact piece_block_inRange hk hp x hi
      | cons y rest =>
          obtain ⟨hxy, hrest⟩ := hadj
          obtain ⟨n, hflat, hrange⟩ := ih (List.cons_ne_nil y rest) hrest
          have hystart : y.start = x.start + x.size := by
            rw [← hxy.1]
            have := x.valid.nonempty
            simp only [ComponentIntervalPiece.size, actualPieceSize]
            omega
          simp only [List.head_cons] at hflat hrange ⊢
          refine ⟨x.size + n, ?_, ?_⟩
          · rw [List.map_cons, List.flatten_cons, hflat, hystart, pieceEntries,
              ← List.map_append, List.range'_append_1]
          · intro i hi
            by_cases hix : i < x.size
            · exact piece_block_inRange hk hp x hix
            · have h := hrange (i - x.size) (by omega)
              rw [hystart] at h
              rw [show x.start + i = x.start + x.size + (i - x.size) by omega]
              exact h

/-- The block entries of a list of consecutive pieces are pairwise in different rotation
classes. -/
theorem pieces_pairwise_not_isRotated (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (ps : List (ComponentIntervalPiece p)) (hadj : Adjacent ExactPieceAdjacent ps) :
    List.Pairwise (fun u v : Vtx k => ¬ ((u : List ℕ) ~r (v : List ℕ)))
      (ps.map pieceEntries).flatten := by
  by_cases hne : ps = []
  · subst hne
    simp
  · obtain ⟨n, hflat, hrange⟩ := pieces_flatten hk hp ps hne hadj
    rw [hflat, List.pairwise_map]
    have hlt : List.Pairwise (· < ·) (List.range' (ps.head hne).start n) :=
      List.pairwise_lt_range'
    refine List.Pairwise.imp_of_mem ?_ hlt
    intro a b ha hb hab
    rw [List.mem_range'_1] at ha hb
    have hra : k * a < p.numVerts := by
      have := hrange (a - (ps.head hne).start) (by omega)
      rwa [show (ps.head hne).start + (a - (ps.head hne).start) = a by omega] at this
    have hrb : k * b < p.numVerts := by
      have := hrange (b - (ps.head hne).start) (by omega)
      rwa [show (ps.head hne).start + (b - (ps.head hne).start) = b by omega] at this
    exact blockEntry_not_isRotated hk hp.1 hra hrb (by omega)

/-- The list of deficits of a list of pieces, from the lists of entries. -/
theorem pieces_deficits (ps : List (ComponentIntervalPiece p)) :
    ps.map ComponentIntervalPiece.deficit =
      (ps.map pieceEntries).map fun L => k - 1 - L.length := by
  rw [List.map_map]
  apply List.map_congr_left
  intro piece _
  exact piece_deficit_eq_entries piece

/-! ### The whole chain -/

/-- Liu's `Adjacent` as `List.IsChain`. -/
theorem isChain_of_adjacent {α : Type} {R : α → α → Prop} :
    ∀ {xs : List α}, Adjacent R xs → List.IsChain R xs
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | _ :: _ :: _, h => List.isChain_cons_cons.mpr ⟨h.1, isChain_of_adjacent h.2⟩

/-- A list of lists of vertices that looks like a chain of pieces: every list is a non-empty
run `v, tau2V v, …` of at most `k - 1` vertices, the exit of the last vertex of a list is
joined to the first vertex of the next list by an edge of weight 3, and all vertices lie in
pairwise different rotation classes. -/
structure EntriesChain (k : ℕ) (L : List (List (Vtx k))) : Prop where
  ne : L ≠ []
  pieces_ne : ∀ P ∈ L, P ≠ []
  size_le : ∀ P ∈ L, P.length ≤ k - 1
  doors : ∀ P ∈ L, List.IsChain (fun a b => b = tau2V a) P
  seams : List.IsChain
    (fun P Q => ∀ (hP : P ≠ []) (hQ : Q ≠ []), ew k (sigmaInv (P.getLast hP)) (Q.head hQ) = 3) L
  classes : List.Pairwise (fun u v : Vtx k => ¬ ((u : List ℕ) ~r (v : List ℕ))) L.flatten

/-- The lists of block entries of the pieces of an exact weight-three chain form an
`EntriesChain`. -/
theorem chain_entriesChain (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    EntriesChain k (chain.pieces.map pieceEntries) := by
  have hadj : Adjacent ExactPieceAdjacent chain.pieces := exactChain_pieces_adjacent chain
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact chain.nonempty (List.map_eq_nil_iff.mp h)
  · intro P hP
    obtain ⟨piece, _, rfl⟩ := List.mem_map.mp hP
    exact pieceEntries_ne_nil piece
  · intro P hP
    obtain ⟨piece, _, rfl⟩ := List.mem_map.mp hP
    rw [pieceEntries_length]
    exact piece_size_le hk hp piece
  · intro P hP
    obtain ⟨piece, _, rfl⟩ := List.mem_map.mp hP
    exact pieceEntries_isChain (by omega) hp piece
  · rw [List.isChain_map]
    refine List.IsChain.imp ?_ (isChain_of_adjacent hadj)
    intro left right hjoin _ _
    exact pieceEntries_join_ew (by omega) hp hjoin
  · exact pieces_pairwise_not_isRotated (by omega) hp chain.pieces hadj

/-- The deficits of the pieces of a chain, from the lists of entries. -/
theorem chain_deficits (chain : ExactWeightThreePieceChain p) :
    chain.pieces.map ComponentIntervalPiece.deficit =
      (chain.pieces.map pieceEntries).map fun L => k - 1 - L.length :=
  pieces_deficits chain.pieces

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.pieceEntries_eq_iterate
#print axioms SuperpermLowerBounds.pieceEntries_isChain
#print axioms SuperpermLowerBounds.pieceEntries_join_ew
#print axioms SuperpermLowerBounds.pieces_flatten
#print axioms SuperpermLowerBounds.pieces_pairwise_not_isRotated
#print axioms SuperpermLowerBounds.pieces_deficits
#print axioms SuperpermLowerBounds.chain_entriesChain
#print axioms SuperpermLowerBounds.chain_deficits

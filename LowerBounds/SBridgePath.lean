import PreimageChain.ComponentPortalChains
import PreimageChain.FullGapRunStable

/-!
# Blocks, doors and seams of a strongly exitless path, on vertices

A strongly exitless path is a sequence of complete rotation classes (blocks) of `k` vertices
each.  This file states the facts about the blocks as equations between vertices (`Vtx k`), so
that the pieces and chains of the preimage-chain library can be compared with a model that is
defined on vertices only.

Notation: `blockEntry p j = p.vert (k j)` is the first vertex of block `j` (its *entry*),
`sigmaInv (blockEntry p j)` its last vertex (its *exit*), and

  `tau2V v = tau (sigmaInv v)`,   on words `x₁ x₂ … x_{k-1} x_k ↦ x₂ … x_{k-1} x₁ x_k`,

is the door of the exit: the entry of the next block inside a piece.

* `block_vert`: block `j` is `blockEntry p j, σ (blockEntry p j), …, σ^{k-1} (blockEntry p j)`.
* `blockExit_eq`: the vertex before the entry of block `j + 1` is `sigmaInv (blockEntry p j)`.
* `blockEntry_door`: across a door, `blockEntry p (j + 1) = tau2V (blockEntry p j)`.
* `blockEntry_seam`: across a boundary of weight 3,
  `ew k (sigmaInv (blockEntry p j)) (blockEntry p (j + 1)) = 3`.
* `ew_three_cases`: an edge of weight 3 from `y₁ y₂ y₃ Y` ends at `Y` followed by one of the
  six arrangements of `y₁, y₂, y₃`.
* `blockEntry_not_isRotated`: different blocks are different rotation classes.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### Vertices -/

/-- The entry of block `j` of a path: its vertex number `k j`. -/
def blockEntry (p : HPath k) (j : ℕ) : Vtx k := p.vert (k * j)

/-- The door of the exit of the block entered at `v`: the entry of the next block inside a
piece. -/
noncomputable def tau2V (v : Vtx k) : Vtx k := tau (sigmaInv v)

theorem blockEntry_val (p : HPath k) (j : ℕ) :
    (blockEntry p j : List ℕ) = Hunter.ProofsChartEq.blockWord p j := rfl

theorem sigmaInv_val (v : Vtx k) : (sigmaInv v : List ℕ) = (v : List ℕ).rotate (k - 1) := rfl

theorem sigmaInv_val_bexit (v : Vtx k) :
    (sigmaInv v : List ℕ) = Hunter.ProofsRigidity2.bexit k (v : List ℕ) := rfl

/-- On words, `tau2V` is `τ₂` of the Hunter library. -/
theorem tau2V_val (hk : 2 ≤ k) (v : Vtx k) :
    (tau2V v : List ℕ) = Hunter.ProofsRigidity2.tau2 k (v : List ℕ) := by
  unfold tau2V
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord hk (sigmaInv v).2)]
  rfl

/-- `τ₂` moves the first letter in front of the last one. -/
theorem tau2_cons_append (hk : 2 ≤ k) (x : ℕ) (M : List ℕ) (m : ℕ)
    (hlen : (x :: (M ++ [m])).length = k) :
    Hunter.ProofsRigidity2.tau2 k (x :: (M ++ [m])) = M ++ [x, m] := by
  have hP : (x :: M).length = k - 1 := by
    simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
    omega
  have h := Hunter.ProofsRigidity2.tau2_step hk hP m 0
  simpa [List.rotate_cons_succ] using h

/-- `tau2V` on words: `x M m ↦ M x m`. -/
theorem tau2V_cons_append (hk : 2 ≤ k) (v : Vtx k) (x : ℕ) (M : List ℕ) (m : ℕ)
    (hv : (v : List ℕ) = x :: (M ++ [m])) :
    (tau2V v : List ℕ) = M ++ [x, m] := by
  rw [tau2V_val hk, hv]
  exact tau2_cons_append hk x M m (by rw [← hv]; exact v.2.length)

/-- Every vertex is `x M m` with `|M| = k - 2`. -/
theorem vtx_cons_append (hk : 2 ≤ k) (v : Vtx k) :
    ∃ x M m, (v : List ℕ) = x :: (M ++ [m]) ∧ M.length = k - 2 := by
  have hlen : (v : List ℕ).length = k := v.2.length
  rcases hv : (v : List ℕ) with _ | ⟨x, rest⟩
  · rw [hv] at hlen
    simp at hlen
    omega
  · rw [hv] at hlen
    have hrest : rest ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    refine ⟨x, rest.dropLast, rest.getLast hrest, ?_, ?_⟩
    · rw [List.dropLast_append_getLast hrest]
    · simp only [List.length_cons] at hlen
      rw [List.length_dropLast]
      omega

/-! ### Blocks of an exitless path -/

/-- A block is traversed by weight-1 steps: its vertices are the rotations of its entry. -/
theorem block_vert (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {j r : ℕ}
    (hr : r < k) (hN : k * j + r < p.numVerts) :
    p.vert (k * j + r) = sigma^[r] (blockEntry p j) :=
  Hunter.ProofsExitless.block_is_full_cycle hk hp ⟨j, rfl⟩ hr hN

/-- The vertex before the entry of block `j + 1` is the exit of block `j`. -/
theorem blockExit_eq (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {j : ℕ}
    (hN : k * (j + 1) < p.numVerts) :
    p.vert (k * (j + 1) - 1) = sigmaInv (blockEntry p j) := by
  apply Subtype.ext
  have h := blockBoundarySource_eq_bexit hk hp (t := j + 1) (by omega) hN
  rw [h]
  rfl

/-- The weight of the boundary into block `j + 1`, as the weight of an edge between the exit of
block `j` and the entry of block `j + 1`. -/
theorem bw_eq_ew (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {j : ℕ}
    (hN : k * (j + 1) < p.numVerts) :
    Hunter.ProofsLedger.bw p (j + 1) =
      ew k (sigmaInv (blockEntry p j)) (blockEntry p (j + 1)) := by
  unfold Hunter.ProofsLedger.bw
  rw [blockExit_eq hk hp hN]
  rfl

/-- Across a door the entry of the next block is `tau2V` of the entry of the block. -/
theorem blockEntry_door (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {j : ℕ}
    (hN : k * (j + 1) < p.numVerts) (hdoor : Hunter.ProofsLedger.IsDoor p (j + 1)) :
    blockEntry p (j + 1) = tau2V (blockEntry p j) := by
  apply Subtype.ext
  obtain ⟨x, M, m, hv, hM⟩ := vtx_cons_append hk (blockEntry p j)
  rw [tau2V_cons_append hk _ x M m hv]
  have h := doorSegment_block_word hk hp (start := j) (r := 1) (l := 1)
    (base := x :: M) (marker := m) le_rfl hN
    (by
      intro i hi1 hi2
      obtain rfl : i = 1 := by omega
      exact hdoor)
    (by rw [← blockEntry_val, hv]; rfl)
  rw [blockEntry_val, h]
  simp [List.rotate_cons_succ]

/-- Across a boundary of weight 3 the edge from the exit of the block to the entry of the next
block has weight 3. -/
theorem blockEntry_seam (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {j : ℕ}
    (hN : k * (j + 1) < p.numVerts) (hseam : Hunter.ProofsLedger.bw p (j + 1) = 3) :
    ew k (sigmaInv (blockEntry p j)) (blockEntry p (j + 1)) = 3 := by
  rw [← bw_eq_ew hk hp hN]
  exact hseam

/-- Different blocks of an exitless path are different rotation classes. -/
theorem blockEntry_not_isRotated (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {s t : ℕ}
    (hs : k * s < p.numVerts) (ht : k * t < p.numVerts) (hst : s ≠ t) :
    ¬ ((blockEntry p s : List ℕ) ~r (blockEntry p t : List ℕ)) := by
  intro h
  exact Hunter.ProofsChartEq.blockWord_distinct hk hp hs ht hst (rotClass_eq_iff.mpr h)

/-- The entries of different blocks are different vertices. -/
theorem blockEntry_injective (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {s t : ℕ}
    (hs : k * s < p.numVerts) (ht : k * t < p.numVerts) (h : blockEntry p s = blockEntry p t) :
    s = t := by
  by_contra hst
  apply blockEntry_not_isRotated hk hp hs ht hst
  rw [h]

/-! ### Edges of weight 3 -/

/-- An edge of weight 3 from `y₁ y₂ y₃ Y` ends at `Y` followed by an arrangement of
`y₁, y₂, y₃`. -/
theorem ew_three_cases (hk : 3 ≤ k) {u v : Vtx k} (h : ew k u v = 3) :
    ∃ y₁ y₂ y₃ Y, (u : List ℕ) = y₁ :: y₂ :: y₃ :: Y ∧
      ((v : List ℕ) = Y ++ [y₁, y₂, y₃] ∨ (v : List ℕ) = Y ++ [y₁, y₃, y₂] ∨
        (v : List ℕ) = Y ++ [y₂, y₁, y₃] ∨ (v : List ℕ) = Y ++ [y₂, y₃, y₁] ∨
        (v : List ℕ) = Y ++ [y₃, y₁, y₂] ∨ (v : List ℕ) = Y ++ [y₃, y₂, y₁]) := by
  have hulen : (u : List ℕ).length = k := u.2.length
  obtain ⟨y₁, y₂, y₃, Y, hu⟩ : ∃ y₁ y₂ y₃ Y, (u : List ℕ) = y₁ :: y₂ :: y₃ :: Y := by
    rcases hu : (u : List ℕ) with _ | ⟨a, _ | ⟨b, _ | ⟨c, Y⟩⟩⟩
    · rw [hu] at hulen; simp at hulen; omega
    · rw [hu] at hulen; simp at hulen; omega
    · rw [hu] at hulen; simp at hulen; omega
    · exact ⟨a, b, c, Y, rfl⟩
  have hY : Y.length + 3 = k := by
    rw [hu] at hulen
    simpa using hulen
  refine ⟨y₁, y₂, y₃, Y, hu, ?_⟩
  have hspec := (wt_spec (u := (u : List ℕ)) (v := (v : List ℕ)) (by omega : 1 ≤ k)
    (le_of_eq hulen)).2.2
  have hw : wt k (u : List ℕ) (v : List ℕ) = 3 := h
  rw [hw] at hspec
  have hx : IsPermWord (Y.length + 3) (Hunter.ProofsClosure3.finalExit Y y₃ y₂ y₁) := by
    rw [hY]
    have := u.2
    rw [hu] at this
    exact this
  have hv : IsPermWord (Y.length + 3) (v : List ℕ) := by
    rw [hY]
    exact v.2
  have hover : (Hunter.ProofsClosure3.finalExit Y y₃ y₂ y₁).drop 3 =
      (v : List ℕ).take (Y.length + 3 - 3) := by
    rw [hY]
    rw [hu] at hspec
    exact hspec
  rcases Hunter.ProofsClosure3.w3_six_cases Y y₃ y₂ y₁ hx hv hover with
    h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h1

/-! ### Pieces -/

variable {p : HPath k}

/-- Every block of a piece lies in the path. -/
theorem piece_block_inRange (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) {l : ℕ} (hl : l < piece.size) :
    k * (piece.start + l) < p.numVerts := by
  have hlast := actualIntervalPieceSpan_last_inRange hk hp piece.valid
  have hne := piece.valid.nonempty
  simp only [ComponentIntervalPiece.size, actualPieceSize] at hl
  exact lt_of_le_of_lt (Nat.mul_le_mul_left k (by omega)) hlast

/-- Inside a piece the entry of block number `l + 1` is `tau2V` of the entry of block number
`l`. -/
theorem piece_blockEntry_succ (hk : 2 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) {l : ℕ} (hl : l + 1 < piece.size) :
    blockEntry p (piece.start + (l + 1)) = tau2V (blockEntry p (piece.start + l)) := by
  have hN := piece_block_inRange (by omega) hp piece hl
  have hdoor : Hunter.ProofsLedger.IsDoor p (piece.start + (l + 1)) :=
    piece.valid.doors (l + 1) (by omega)
      (by simpa only [ComponentIntervalPiece.size, actualPieceSize] using hl)
  exact blockEntry_door hk hp.1 (j := piece.start + l) hN hdoor

/-- Inside a piece the entry of block number `l` is `tau2V^l` of the entry of the first
block. -/
theorem piece_blockEntry (hk : 2 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) {l : ℕ} (hl : l < piece.size) :
    blockEntry p (piece.start + l) = tau2V^[l] (blockEntry p piece.start) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      rw [piece_blockEntry_succ hk hp piece hl, ih (by omega), Function.iterate_succ_apply']

/-- A piece has at least one block. -/
theorem piece_size_pos (piece : ComponentIntervalPiece p) : 0 < piece.size := by
  have := piece.valid.nonempty
  simp only [ComponentIntervalPiece.size, actualPieceSize]
  omega

/-- A piece has at most `k - 1` blocks. -/
theorem piece_size_le (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p) : piece.size ≤ k - 1 :=
  actualIntervalPieceSpan_size_le hk hp piece.valid

/-- The deficit of a piece is `k - 1` minus its number of blocks. -/
theorem piece_deficit_eq (piece : ComponentIntervalPiece p) :
    piece.deficit = k - 1 - piece.size := rfl

/-- The last block of a piece. -/
theorem piece_stop_eq (piece : ComponentIntervalPiece p) :
    piece.stop = piece.start + (piece.size - 1) + 1 := by
  have := piece.valid.nonempty
  simp only [ComponentIntervalPiece.size, actualPieceSize]
  omega

/-- Between two pieces joined by a seam of weight 3, the edge from the exit of the last block
of the first piece to the entry of the first block of the second has weight 3. -/
theorem piece_join_ew (hk : 1 ≤ k) (hp : p.StronglyExitless)
    {left right : ComponentIntervalPiece p} (hjoin : ExactPieceAdjacent left right) :
    ew k (sigmaInv (blockEntry p (left.start + (left.size - 1))))
      (blockEntry p right.start) = 3 := by
  have hstop := piece_stop_eq left
  have hstart : right.start = left.start + (left.size - 1) + 1 := by
    rw [← hjoin.1]
    exact hstop
  have hN : k * (left.start + (left.size - 1) + 1) < p.numVerts := by
    rw [← hstart]
    simpa using piece_block_inRange hk hp right (l := 0) (piece_size_pos right)
  have hseam : Hunter.ProofsLedger.bw p (left.start + (left.size - 1) + 1) = 3 := by
    rw [← hstart]
    exact hjoin.2
  have h := blockEntry_seam hk hp.1 hN hseam
  rw [← hstart] at h
  exact h

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.block_vert
#print axioms SuperpermLowerBounds.blockEntry_door
#print axioms SuperpermLowerBounds.blockEntry_seam
#print axioms SuperpermLowerBounds.ew_three_cases
#print axioms SuperpermLowerBounds.blockEntry_not_isRotated
#print axioms SuperpermLowerBounds.piece_blockEntry
#print axioms SuperpermLowerBounds.piece_join_ew

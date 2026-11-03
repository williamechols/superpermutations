import PreimageChain.ComponentEndpointRigidity

/-!
# Lemma Z: junctions of cost zero

Let `p`, `q` be strongly exitless paths with `q.first = ψ(p.last)`, and `q = p` or `q` disjoint
from `p`.  Write the last piece of `p` as a door run with block entries
`E_i = base.rotate i ++ [m]`, `0 ≤ i < L`.  Then `ψ(p.last) = E_{L+1}` (`psi_of_run_head`), so
the first piece of `q`, with `f` blocks, has block entries `E_{L+1}, …, E_{L+f}`.  The words
`E_i` have period `k - 1` in `i`.  If `L + f ≥ k - 1`, one of the first `f` blocks of `q` has
the same entry as one of the last `L` blocks of `p`; then `q = p`, the two block numbers agree,
and this forces `p` to be a single piece with `k - 2` blocks (`Z_core`).

`Z_pieces` is the same in the vocabulary of Liu's `componentIntervalPieces`, and `lemma_Z` is
the statement for a chain of cost zero whose target has minimum entry weight 2, through Liu's
`actual_reduced_zero_cost_dichotomy`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

/-! ### Words -/

/-- Rotation by the length is the identity, also after another rotation. -/
theorem rotate_add_length (l : List ℕ) (n : ℕ) :
    l.rotate (n + l.length) = l.rotate n := by
  rw [← List.rotate_mod l (n + l.length), Nat.add_mod_right, List.rotate_mod]

/--
`ψ` of the exit of block `i` of a door run is the entry of block `i + 2` of the same run
(indices taken with period `k - 1`).  Liu's `psi_of_complete_run_head` is the case `i = k - 2`.
-/
theorem psi_of_run_head
    (hk : 2 ≤ k) {base : List ℕ} (hbase : base.length = k - 1)
    {m : ℕ} (i : ℕ) {h : Vtx k}
    (hhead : h.1 = Hunter.ProofsRigidity2.bexit k (base.rotate i ++ [m])) :
    (psi h).1 = base.rotate (i + 2) ++ [m] := by
  have hfirstDoor :
      door (Hunter.ProofsRigidity2.bexit k (base.rotate i ++ [m])) =
        base.rotate (i + 1) ++ [m] :=
    Hunter.ProofsRigidity2.tau2_step hk hbase m i
  have hsecondDoor :
      door (Hunter.ProofsRigidity2.bexit k (base.rotate (i + 1) ++ [m])) =
        base.rotate (i + 2) ++ [m] :=
    Hunter.ProofsRigidity2.tau2_step hk hbase m (i + 1)
  change (tau (sigmaInv (tau h))).1 = _
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord hk (sigmaInv (tau h)).2)]
  change door ((tau h).1.rotate (k - 1)) = _
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord hk h.2)]
  rw [hhead, hfirstDoor]
  exact hsecondDoor

/-! ### Paths -/

/-- The last vertex of a strongly exitless path is the exit of its last block. -/
theorem last_eq_bexit_lastBlock
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    (p.last : List ℕ) = Hunter.ProofsRigidity2.bexit k
      (Hunter.ProofsChartEq.blockWord p (componentClassCount p - 1)) := by
  obtain ⟨t, ht⟩ : ∃ t, t = componentClassCount p := ⟨_, rfl⟩
  rw [← ht]
  have hN : p.numVerts = k * t := by
    rw [ht]
    exact component_numVerts_eq hk hp
  have htpos : 0 < t := by
    rw [ht]
    exact componentClassCount_pos hk hp
  have hmul : k * t = k * (t - 1) + k := by
    have htEq : t = (t - 1) + 1 := by omega
    calc
      k * t = k * ((t - 1) + 1) := congrArg (fun n => k * n) htEq
      _ = k * (t - 1) + k := Nat.mul_succ _ _
  have hlastIndex : p.numVerts - 1 = k * (t - 1) + (k - 1) := by
    rw [hN, hmul]
    omega
  have hBlt : k * (t - 1) + (k - 1) < p.numVerts := by
    rw [hN, hmul]
    omega
  have hcycle :
      p.vert (k * (t - 1) + (k - 1)) = sigma^[k - 1] (p.vert (k * (t - 1))) :=
    Hunter.ProofsExitless.block_is_full_cycle hk hp.1 ⟨t - 1, rfl⟩ (by omega) hBlt
  rw [Hunter.Proved.last_eq_vert, hlastIndex, hcycle,
    Hunter.ProofsExitless.sigma_iter_val]
  rfl

/--
**Lemma Z-core.**  `p` ends with a door run of `L` blocks, `q` starts with a door run of `f`
blocks, `q.first = ψ(p.last)`, and `q` is `p` or disjoint from `p`.  Then `L + f ≤ k - 2`, or
`q = p` and `p` is one door run of `k - 2` blocks.
-/
theorem Z_core
    (hk : 4 ≤ k) {p q : HPath k} (hp : p.StronglyExitless) (hq : q.StronglyExitless)
    {L f : ℕ} (hL : 1 ≤ L) (hLt : L ≤ componentClassCount p)
    (hpDoors : ∀ r, 1 ≤ r → r < L →
      Hunter.ProofsLedger.IsDoor p (componentClassCount p - L + r))
    (hf : 1 ≤ f) (hft : f ≤ componentClassCount q)
    (hqDoors : ∀ r, 1 ≤ r → r < f → Hunter.ProofsLedger.IsDoor q r)
    (hpsi : q.first = psi p.last)
    (hpq : q = p ∨ ∀ v, v ∈ p.verts → v ∉ q.verts) :
    L + f ≤ k - 2 ∨
      (q = p ∧ componentClassCount p = k - 2 ∧
        ∀ j, 1 ≤ j → j < componentClassCount p → Hunter.ProofsLedger.IsDoor p j) := by
  by_cases hsum : L + f ≤ k - 2
  · exact Or.inl hsum
  right
  have hlastBlock := last_eq_bexit_lastBlock (by omega : 1 ≤ k) hp
  have hNp := component_numVerts_eq (by omega : 1 ≤ k) hp
  have hNq := component_numVerts_eq (by omega : 1 ≤ k) hq
  obtain ⟨t, ht⟩ : ∃ t, t = componentClassCount p := ⟨_, rfl⟩
  obtain ⟨tq, htq⟩ : ∃ t, t = componentClassCount q := ⟨_, rfl⟩
  rw [← ht] at hLt hpDoors hlastBlock hNp ⊢
  rw [← htq] at hft hNq
  have hprange : ∀ {j : ℕ}, j < t → k * j < p.numVerts := by
    intro j hj
    rw [hNp]
    exact Nat.mul_lt_mul_of_pos_left hj (by omega)
  have hqrange : ∀ {j : ℕ}, j < tq → k * j < q.numVerts := by
    intro j hj
    rw [hNq]
    exact Nat.mul_lt_mul_of_pos_left hj (by omega)
  obtain ⟨g0, hg0⟩ : ∃ g, g = t - L := ⟨_, rfl⟩
  rw [← hg0] at hpDoors
  -- the last `L` blocks of `p` are `base.rotate l ++ [m]`
  have hrootLen : (Hunter.ProofsChartEq.blockWord p g0).length = k :=
    (Hunter.ProofsChartEq.blockWord_isPermWord p g0).length
  have hrootNe : Hunter.ProofsChartEq.blockWord p g0 ≠ [] := by
    intro hnil
    rw [hnil] at hrootLen
    simp only [List.length_nil] at hrootLen
    omega
  obtain ⟨base, m, hbase, hroot⟩ : ∃ base m, base.length = k - 1 ∧
      Hunter.ProofsChartEq.blockWord p g0 = base ++ [m] :=
    ⟨(Hunter.ProofsChartEq.blockWord p g0).dropLast,
      (Hunter.ProofsChartEq.blockWord p g0).getLastD 0,
      by rw [List.length_dropLast, hrootLen],
      Hunter.ProofsSynthesis.list_dropLast_getLastD _ hrootNe⟩
  have hpBlocks : ∀ l, l ≤ L - 1 →
      Hunter.ProofsChartEq.blockWord p (g0 + l) = base.rotate l ++ [m] := fun l hl =>
    doorSegment_block_word (by omega : 2 ≤ k) hp.1 (r := L - 1) hl
      (hprange (by omega)) (fun i hi1 hi2 => hpDoors i hi1 (by omega)) hroot
  -- `ψ(p.last)` is the entry of block `L + 1` of that run
  have hlast : (p.last : List ℕ) =
      Hunter.ProofsRigidity2.bexit k (base.rotate (L - 1) ++ [m]) := by
    rw [hlastBlock, show t - 1 = g0 + (L - 1) by omega, hpBlocks (L - 1) le_rfl]
  have hpsiVal : (psi p.last).1 = base.rotate (L + 1) ++ [m] := by
    have h := psi_of_run_head (by omega : 2 ≤ k) hbase (L - 1) hlast
    rwa [show L - 1 + 2 = L + 1 by omega] at h
  -- the first `f` blocks of `q` are `base.rotate (L + 1 + l) ++ [m]`
  have hqroot : Hunter.ProofsChartEq.blockWord q 0 = base.rotate (L + 1) ++ [m] := by
    change (q.vert (k * 0) : List ℕ) = _
    rw [Nat.mul_zero, q.vert_zero, hpsi]
    exact hpsiVal
  have hqBlocks : ∀ l, l ≤ f - 1 →
      Hunter.ProofsChartEq.blockWord q l = base.rotate (L + 1 + l) ++ [m] := by
    intro l hl
    have h := doorSegment_block_word (by omega : 2 ≤ k) hq.1 (start := 0) (r := f - 1) hl
      (by rw [Nat.zero_add]; exact hqrange (by omega))
      (fun i hi1 hi2 => by rw [Nat.zero_add]; exact hqDoors i hi1 (by omega)) hqroot
    rw [Nat.zero_add, List.rotate_rotate] at h
    exact h
  -- a block of `q` with the entry of a block of `p`: the paths and the block numbers agree
  have hshare : ∀ {i j : ℕ}, i < tq → j < t →
      Hunter.ProofsChartEq.blockWord q i = Hunter.ProofsChartEq.blockWord p j →
      q = p ∧ i = j := by
    intro i j hi hj hw
    rcases hpq with hqp | hdisj
    · refine ⟨hqp, ?_⟩
      by_contra hne
      have htqt : tq = t := by rw [htq, ht, hqp]
      rw [hqp] at hw
      exact Hunter.ProofsChartEq.blockWord_distinct (by omega : 1 ≤ k) hp.1
        (hprange (by omega : i < t)) (hprange hj) hne (congrArg rotClass hw)
    · exfalso
      have hv : q.vert (k * i) = p.vert (k * j) := Subtype.ext hw
      have hmemq : q.vert (k * i) ∈ q.verts :=
        Hunter.ProofsExitless.vert_mem q (hqrange hi)
      rw [hv] at hmemq
      exact hdisj _ (Hunter.ProofsExitless.vert_mem p (hprange hj)) hmemq
  by_cases hLk : k - 1 ≤ L
  · -- block 0 of `q` is block `L + 1 - (k - 1) ≥ 1` of the run: impossible
    exfalso
    have hw : Hunter.ProofsChartEq.blockWord q 0 =
        Hunter.ProofsChartEq.blockWord p (g0 + (L + 1 - (k - 1))) := by
      rw [hqroot, hpBlocks (L + 1 - (k - 1)) (by omega),
        ← rotate_add_length base (L + 1 - (k - 1)), hbase,
        show L + 1 - (k - 1) + (k - 1) = L + 1 by omega]
    have hidx := (hshare (by omega : 0 < tq)
      (by omega : g0 + (L + 1 - (k - 1)) < t) hw).2
    omega
  · -- block `k - 2 - L` of `q` is block 0 of the run
    have hw : Hunter.ProofsChartEq.blockWord q (k - 2 - L) =
        Hunter.ProofsChartEq.blockWord p g0 := by
      rw [hqBlocks (k - 2 - L) (by omega), hroot,
        show L + 1 + (k - 2 - L) = 0 + base.length by rw [hbase]; omega,
        rotate_add_length, List.rotate_zero]
    obtain ⟨hqp, hidx⟩ := hshare (by omega : k - 2 - L < tq) (by omega : g0 < t) hw
    refine ⟨hqp, by omega, ?_⟩
    intro j hj1 hjt
    by_cases hjf : j < f
    · have hdoor := hqDoors j hj1 hjf
      rwa [hqp] at hdoor
    · have hdoor := hpDoors (j - g0) (by omega) (by omega)
      rwa [show g0 + (j - g0) = j by omega] at hdoor

/-! ### Pieces -/

/-- The first piece of a strongly exitless path starts at block 0. -/
theorem exists_first_piece
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    ∃ first rest, componentIntervalPieces p hk hp = first :: rest ∧ first.start = 0 := by
  obtain ⟨first, rest, hpieces⟩ :=
    List.exists_cons_of_ne_nil (componentIntervalPieces_ne_nil hk hp)
  refine ⟨first, rest, hpieces, ?_⟩
  have hstarts := componentIntervalPieces_starts p hk hp
  rw [hpieces] at hstarts
  have hhead := congrArg List.head? hstarts
  simpa [componentPieceStarts] using hhead

/-- The last piece of a strongly exitless path stops at its last block. -/
theorem exists_last_piece
    (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    ∃ last rest, (componentIntervalPieces p hk hp).reverse = last :: rest ∧
      last.stop = componentClassCount p := by
  have hreverseNe : (componentIntervalPieces p hk hp).reverse ≠ [] := by
    simp [componentIntervalPieces_ne_nil hk hp]
  obtain ⟨last, rest, hreverse⟩ := List.exists_cons_of_ne_nil hreverseNe
  refine ⟨last, rest, hreverse, ?_⟩
  have hstops := componentIntervalPieces_stops p hk hp
  have hrevStops := congrArg List.reverse hstops
  rw [← List.map_reverse, hreverse] at hrevStops
  have hhead := congrArg List.head? hrevStops
  simpa [componentPieceStops] using hhead

/--
Lemma Z-core for pieces: either `q = p` is a single piece with `k - 2` blocks, or the last piece
of `p` and the first piece of `q` both have deficit at least 2.
-/
theorem Z_pieces
    (hk : 4 ≤ k) {p q : HPath k} (hp : p.StronglyExitless) (hq : q.StronglyExitless)
    (hpsi : q.first = psi p.last)
    (hpq : q = p ∨ ∀ v, v ∈ p.verts → v ∉ q.verts) :
    (q = p ∧ componentPieceCount p = 1 ∧ componentClassCount p = k - 2) ∨
      (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces p (by omega) hp) ∧
        2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces q (by omega) hq)) := by
  obtain ⟨last, restL, hrev, hlastStop⟩ := exists_last_piece (by omega : 1 ≤ k) hp
  obtain ⟨first, restF, hpieces, hfirstStart⟩ := exists_first_piece (by omega : 1 ≤ k) hq
  have hlastVal : lastNatValue ComponentIntervalPiece.deficit
      (componentIntervalPieces p (by omega) hp) = last.deficit := by
    unfold lastNatValue
    rw [hrev]
    rfl
  have hfirstVal : firstNatValue ComponentIntervalPiece.deficit
      (componentIntervalPieces q (by omega) hq) = first.deficit := by
    rw [hpieces]
    rfl
  have hL := last.valid.nonempty
  have hF := first.valid.nonempty
  have hFle := first.valid.stopLe
  have htpos := componentClassCount_pos (by omega : 1 ≤ k) hp
  rcases Z_core hk hp hq (L := last.stop - last.start) (f := first.stop - first.start)
      (by omega) (by omega)
      (fun r hr1 hr2 => by
        rw [show componentClassCount p - (last.stop - last.start) + r = last.start + r by
          omega]
        exact last.valid.doors r hr1 hr2)
      (by omega) (by omega)
      (fun r hr1 hr2 => by
        have hdoor := first.valid.doors r hr1 hr2
        rwa [hfirstStart, Nat.zero_add] at hdoor)
      hpsi hpq with hsum | ⟨hqp, ht, hdoors⟩
  · right
    rw [hlastVal, hfirstVal]
    constructor
    · change 2 ≤ k - 1 - (last.stop - last.start)
      omega
    · change 2 ≤ k - 1 - (first.stop - first.start)
      omega
  · left
    refine ⟨hqp, ?_, ht⟩
    have hempty : componentSeams p = ∅ := by
      unfold componentSeams
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj hne
      rw [componentBoundaries, Finset.mem_Icc] at hj
      exact hne (hdoors j hj.1 (by omega))
    unfold componentPieceCount
    rw [hempty, Finset.card_empty]

/-! ### Components and chains -/

/--
Lemma Z for two components `A`, `B` of `F P` with `tail A = ψ (head B)`: either `A = B` is a
single piece, or the last piece of `B` and the first piece of `A` both have deficit at least 2.
-/
theorem lemma_Z_components (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (A B : ActualComponent P)
    (hpsi : actualComponentTail hP A = psi (actualComponentHead hP B)) :
    (A = B ∧ componentPieceCount (actualComponentPath hP B) = 1) ∨
      (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces (actualComponentPath hP B) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega) B)) ∧
        2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces (actualComponentPath hP A) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega) A))) := by
  have hpB := actualComponentPath_stronglyExitless hP (by omega : 2 ≤ k) B
  have hpA := actualComponentPath_stronglyExitless hP (by omega : 2 ≤ k) A
  have hpsi' : (actualComponentPath hP A).first = psi (actualComponentPath hP B).last := by
    rw [actualComponentPath_first hP A, actualComponentPath_last hP B]
    exact hpsi
  have hpq : actualComponentPath hP A = actualComponentPath hP B ∨
      ∀ v, v ∈ (actualComponentPath hP B).verts →
        v ∉ (actualComponentPath hP A).verts := by
    by_cases hAB : A = B
    · left
      rw [hAB]
    · right
      intro v hvB hvA
      have hdisj := Hunter.ProofsWP.comps_disjoint A.2 B.2
        (fun h => hAB (Subtype.ext h))
      have hvB' : v ∈ B.1 := by
        rw [← actualComponentPath_vertsFinset hP B]
        exact HPath.mem_vertsFinset.mpr hvB
      have hvA' : v ∈ A.1 := by
        rw [← actualComponentPath_vertsFinset hP A]
        exact HPath.mem_vertsFinset.mpr hvA
      exact Finset.disjoint_left.mp hdisj hvA' hvB'
  rcases Z_pieces (by omega : 4 ≤ k) hpB hpA hpsi' hpq with ⟨hqp, hcount, _⟩ | hlarge
  · left
    refine ⟨?_, hcount⟩
    apply Subtype.ext
    calc
      A.1 = (actualComponentPath hP A).vertsFinset :=
        (actualComponentPath_vertsFinset hP A).symm
      _ = (actualComponentPath hP B).vertsFinset := by rw [hqp]
      _ = B.1 := actualComponentPath_vertsFinset hP B
  · right
    exact hlarge

/--
**Lemma Z.**  Let `P` be a `σ²`-reduced Hamiltonian path and `s` a chain start whose route does
not end at `P.last`, has cost 0, and enters a component of minimum entry weight 2.  Then either
the target is the source and that component is a single piece, or the last piece of the source
and the first piece of the target both have deficit at least 2.
-/
theorem lemma_Z {k : ℕ} (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P})
    (hsEnd : actualChainRouteEnd s ≠ P.last)
    (hzero : actualChainRouteNatCost hP (by omega) s = 0)
    (hmu : compMinto (F P)
      (actualNonterminalTargetComponent hP (by omega)
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2) :
    (actualNonterminalTargetComponent hP (by omega)
          ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩ =
        actualChainSourceComponent hP (by omega) s ∧
      componentPieceCount
          (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) = 1) ∨
    (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces
            (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega)
              (actualChainSourceComponent hP (by omega) s))) ∧
      2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces
            (actualComponentPath hP (actualNonterminalTargetComponent hP (by omega)
              ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩)) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega)
              (actualNonterminalTargetComponent hP (by omega)
                ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩)))) := by
  have hdich := actual_reduced_zero_cost_dichotomy hP (by omega : 2 ≤ k) hred s hsEnd
    hzero hmu
  apply lemma_Z_components hk hP
  rw [actualNonterminalTargetComponent_tail hP (by omega),
    actualChainSourceComponent_head hP (by omega) s]
  exact hdich.2

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.psi_of_run_head
#print axioms SuperpermLowerBounds.Z_core
#print axioms SuperpermLowerBounds.Z_pieces
#print axioms SuperpermLowerBounds.lemma_Z

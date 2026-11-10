import LowerBounds.LemmaZ

/-!
# Lemma Z with the sum of the two deficits

`LemmaZ.lean` proves `Z_core`: if `q.first = ψ (p.last)`, the last piece of `p` has `L` blocks
and the first piece of `q` has `f` blocks, then `L + f ≤ k - 2`, unless `q = p` is a single
piece of `k - 2` blocks.  Its corollaries there keep only "both deficits are at least 2".
Theorem C needs the full strength: the two deficits add up to at least `k`.  The three
statements below are `Z_pieces`, `lemma_Z_components` and `lemma_Z` of `LemmaZ.lean` with this
extra conclusion; the proofs are the same.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

/-- `Z_pieces` with the sum of the two deficits. -/
theorem Z_pieces_sum
    (hk : 4 ≤ k) {p q : HPath k} (hp : p.StronglyExitless) (hq : q.StronglyExitless)
    (hpsi : q.first = psi p.last)
    (hpq : q = p ∨ ∀ v, v ∈ p.verts → v ∉ q.verts) :
    (q = p ∧ componentPieceCount p = 1 ∧ componentClassCount p = k - 2) ∨
      (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces p (by omega) hp) ∧
        2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces q (by omega) hq) ∧
        k ≤ lastNatValue ComponentIntervalPiece.deficit
              (componentIntervalPieces p (by omega) hp) +
            firstNatValue ComponentIntervalPiece.deficit
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
    refine ⟨?_, ?_, ?_⟩
    · change 2 ≤ k - 1 - (last.stop - last.start)
      omega
    · change 2 ≤ k - 1 - (first.stop - first.start)
      omega
    · change k ≤ k - 1 - (last.stop - last.start) + (k - 1 - (first.stop - first.start))
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

/-- `lemma_Z_components` with the sum of the two deficits. -/
theorem lemma_Z_components_sum (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (A B : ActualComponent P)
    (hpsi : actualComponentTail hP A = psi (actualComponentHead hP B)) :
    (A = B ∧ componentPieceCount (actualComponentPath hP B) = 1) ∨
      (2 ≤ lastNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces (actualComponentPath hP B) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega) B)) ∧
        2 ≤ firstNatValue ComponentIntervalPiece.deficit
          (componentIntervalPieces (actualComponentPath hP A) (by omega)
            (actualComponentPath_stronglyExitless hP (by omega) A)) ∧
        k ≤ lastNatValue ComponentIntervalPiece.deficit
              (componentIntervalPieces (actualComponentPath hP B) (by omega)
                (actualComponentPath_stronglyExitless hP (by omega) B)) +
            firstNatValue ComponentIntervalPiece.deficit
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
  rcases Z_pieces_sum (by omega : 4 ≤ k) hpB hpA hpsi' hpq with ⟨hqp, hcount, _⟩ | hlarge
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
**Lemma Z with the sum.**  Let `P` be a `σ²`-reduced Hamiltonian path and `s` a chain start
whose route does not end at `P.last`, has cost 0, and enters a component of minimum entry
weight 2.  Then either the target is the source and that component is a single piece, or the
last piece of the source has deficit `d ≥ 2`, the first piece of the target has deficit
`d' ≥ 2`, and `d + d' ≥ k`.
-/
theorem lemma_ZC {k : ℕ} (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
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
                ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩))) ∧
      k ≤ lastNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualChainSourceComponent hP (by omega) s)) (by omega)
              (actualComponentPath_stronglyExitless hP (by omega)
                (actualChainSourceComponent hP (by omega) s))) +
          firstNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualNonterminalTargetComponent hP (by omega)
                ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩))
              (by omega)
              (actualComponentPath_stronglyExitless hP (by omega)
                (actualNonterminalTargetComponent hP (by omega)
                  ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩)))) := by
  have hdich := actual_reduced_zero_cost_dichotomy hP (by omega : 2 ≤ k) hred s hsEnd
    hzero hmu
  apply lemma_Z_components_sum hk hP
  rw [actualNonterminalTargetComponent_tail hP (by omega),
    actualChainSourceComponent_head hP (by omega) s]
  exact hdich.2

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Z_pieces_sum
#print axioms SuperpermLowerBounds.lemma_ZC

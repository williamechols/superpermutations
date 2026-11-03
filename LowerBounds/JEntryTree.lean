import LowerBounds.JLinks
import LowerBounds.SBridgePath
import PreimageChain.ComponentEndpointRigidity

/-!
# Theorem T: the entry tree

the written proofs of the joint conditions, section 3.  `P` is any Hamiltonian path and `k ≥ 2`; no
reducedness is used anywhere in this file.

* `tail_first` (Theorem T (1)): the tail of a component of `F P` is the first vertex of that
  component in `P`.  This is `cor_pathfirst` of the Hunter–Raudvere library (their Corollary
  "path first") restated for Liu's `ActualComponent`; it is not new.
* `first_entry` (Lemma T0): the first vertex of `P` in a union of components is the tail of its
  component, and its `P`-predecessor is outside the union.
* `parentComp C`: the component of the `P`-predecessor `pPred P (tail C)` of the tail of `C`.
* `parent_tail_lt` (Theorem T (2)): for `C` other than the root, the tail of `parentComp C`
  comes strictly before the tail of `C` in `P`.  Hence `parentComp C ≠ C`
  (`parent_ne_self`), no non-empty set of non-root components is closed under `parentComp`
  (`exists_parent_not_mem`), and every component reaches the root (`exists_iterate_parent_eq_root`).
* `parent_target`: for a chain that does not end at `P.last`, the parent of its target is the
  component of the end of the chain (the last borrowed class).
* `entry_weight_two` (Corollary T′, without reducedness): if the `P`-edge into the tail of a
  non-root component has weight 2, it is the door; it cannot be `σ²`, because a rotation class
  lies inside one component.
* `class_before_tail`: then the rotation class of `e`, where `τ₂ e = tail C`, lies in
  `parentComp C`; `door_entries_not_closed`: in every non-empty set of non-root components that
  are all entered by an edge of weight 2 there is one whose class `e` lies in none of them.
* `free_junction_entry`: a junction of cost 0 enters its target by an edge of weight 2.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

section Path

variable {P : HPath k}

/-- The position in `P` determines the vertex. -/
theorem eq_of_pos_eq (hP : P.IsHamiltonian) {u v : Vtx k} (h : P.pos u = P.pos v) : u = v := by
  rw [← Hunter.ProofsExitless.vert_pos P (hP u), ← Hunter.ProofsExitless.vert_pos P (hP v), h]

/-- **Theorem T (1).**  The tail of a component is the first vertex of the component in `P`. -/
theorem tail_first (hP : P.IsHamiltonian) (C : ActualComponent P) {u : Vtx k} (hu : u ∈ C.1) :
    P.pos (actualComponentTail hP C) ≤ P.pos u := by
  rw [← actualComponentPath_first hP C]
  apply Hunter.Proved.cor_pathfirst hP (actualComponentPath_isPathComponent hP C)
  rw [← HPath.mem_vertsFinset, actualComponentPath_vertsFinset hP C]
  exact hu

/-- **Lemma T0 (first entry).**  If `u` is the first vertex of `P` in the union of a set `𝒞` of
components, then `u` is the tail of its component and no `P`-predecessor of `u` lies in the
union. -/
theorem first_entry (hP : P.IsHamiltonian) (𝒞 : Set (ActualComponent P))
    {C : ActualComponent P} (hC : C ∈ 𝒞) {u : Vtx k} (hu : u ∈ C.1)
    (hmin : ∀ D ∈ 𝒞, ∀ v ∈ D.1, P.pos u ≤ P.pos v) :
    u = actualComponentTail hP C ∧ ∀ p : Vtx k, (p, u) ∈ P.edges → ∀ D ∈ 𝒞, p ∉ D.1 := by
  constructor
  · apply eq_of_pos_eq hP
    exact le_antisymm (hmin C hC _ (actualComponentTail_mem_component hP C))
      (tail_first hP C hu)
  · intro p hp D hD hpD
    have h1 := Hunter.ProofsStructure.edge_pos_succ hp
    have h2 := hmin D hD p hpD
    omega

/-! ### Predecessors, components of vertices, parents -/

/-- The vertex of `P` one step before `v` (for `v = P.first` it is `P.first` itself). -/
def pPred (P : HPath k) (v : Vtx k) : Vtx k := P.vert (P.pos v - 1)

theorem pPred_eq (hP : P.IsHamiltonian) {p v : Vtx k} (h : (p, v) ∈ P.edges) :
    pPred P v = p := by
  unfold pPred
  rw [Hunter.ProofsStructure.edge_pos_succ h, Nat.add_sub_cancel]
  exact Hunter.ProofsExitless.vert_pos P (hP p)

theorem pPred_edge (hP : P.IsHamiltonian) {v : Vtx k} (hv : v ≠ P.first) :
    (pPred P v, v) ∈ P.edges := by
  obtain ⟨p, hp⟩ := Hunter.ProofsSpine.exists_pred (hP v) hv
  rw [pPred_eq hP hp]
  exact hp

/-- The component of `F P` that contains the vertex `v`. -/
noncomputable def compOf (hP : P.IsHamiltonian) (hk : 2 ≤ k) (v : Vtx k) : ActualComponent P :=
  ⟨Hunter.ProofsWP.block (F P) v, Hunter.ProofsWP.block_mem_comps
    ((Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk) ▸ Finset.mem_univ v)⟩

theorem mem_compOf (hP : P.IsHamiltonian) (hk : 2 ≤ k) (v : Vtx k) : v ∈ (compOf hP hk v).1 :=
  Hunter.ProofsWP.self_mem_block
    ((Hunter.ProofsStructure.vertsOf_F_eq_univ hP hk) ▸ Finset.mem_univ v)

theorem compOf_eq_of_mem (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    {v : Vtx k} (h : v ∈ C.1) : compOf hP hk v = C :=
  Subtype.ext (Hunter.ProofsWP.comp_eq_block_of_mem C.2 h).symm

theorem compOf_first (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    compOf hP hk P.first = actualRootComponent hP hk :=
  Subtype.ext rfl

/-- The parent of a component: the component of the `P`-predecessor of its tail. -/
noncomputable def parentComp (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) :
    ActualComponent P :=
  compOf hP hk (pPred P (actualComponentTail hP C))

theorem tail_ne_first (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk) : actualComponentTail hP C ≠ P.first := by
  intro h
  apply hC
  apply actualComponentTail_injective hP
  rw [h, actualComponentTail_root hP hk]

/-- The `P`-predecessor of the tail of a non-root component is outside the component. -/
theorem pPred_not_mem (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk) : pPred P (actualComponentTail hP C) ∉ C.1 := by
  intro hmem
  have h1 := Hunter.ProofsStructure.edge_pos_succ (pPred_edge hP (tail_ne_first hP hk hC))
  have h2 := tail_first hP C hmem
  omega

/-- **Theorem T (2).**  The tail of the parent comes strictly before the tail of the component
in `P`. -/
theorem parent_tail_lt (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk) :
    P.pos (actualComponentTail hP (parentComp hP hk C)) < P.pos (actualComponentTail hP C) := by
  have h1 := Hunter.ProofsStructure.edge_pos_succ (pPred_edge hP (tail_ne_first hP hk hC))
  have h2 : P.pos (actualComponentTail hP (parentComp hP hk C)) ≤
      P.pos (pPred P (actualComponentTail hP C)) :=
    tail_first hP (parentComp hP hk C) (mem_compOf hP hk _)
  omega

theorem parent_ne_self (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk) : parentComp hP hk C ≠ C := by
  intro h
  have hlt := parent_tail_lt hP hk hC
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- No non-empty set of non-root components is closed under `parentComp`. -/
theorem exists_parent_not_mem (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (𝒞 : Finset (ActualComponent P)) (hne : 𝒞.Nonempty)
    (hroot : actualRootComponent hP hk ∉ 𝒞) : ∃ C ∈ 𝒞, parentComp hP hk C ∉ 𝒞 := by
  obtain ⟨C, hC, hmin⟩ :=
    Finset.exists_min_image 𝒞 (fun C => P.pos (actualComponentTail hP C)) hne
  refine ⟨C, hC, fun hpar => ?_⟩
  have h1 := parent_tail_lt hP hk (C := C) (fun h => hroot (h ▸ hC))
  have h2 := hmin _ hpar
  omega

/-- Every component reaches the root by iterating `parentComp`: the components form a tree
rooted at the root component. -/
theorem exists_iterate_parent_eq_root (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    ∀ (m : ℕ) (C : ActualComponent P), P.pos (actualComponentTail hP C) = m →
      ∃ n, (parentComp hP hk)^[n] C = actualRootComponent hP hk := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hm
    by_cases hC : C = actualRootComponent hP hk
    · exact ⟨0, hC⟩
    · have hlt := parent_tail_lt hP hk hC
      obtain ⟨n, hn⟩ := ih _ (hm ▸ hlt) (parentComp hP hk C) rfl
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- For a chain that does not end at `P.last`, the parent of the target is the component of
the end of the chain. -/
theorem parent_target (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    parentComp hP hk (actualNonterminalTargetComponent hP hk (ntEnd s hs)) =
      compOf hP hk (actualChainRouteEnd s) := by
  have hedge : (actualChainRouteEnd s, (chainTargetTail hP (ntEnd s hs)).1) ∈ P.edges :=
    E1removed_subset P (Sset P) (chainTargetTail_spec hP (ntEnd s hs))
  unfold parentComp
  rw [actualNonterminalTargetComponent_tail hP hk, pPred_eq hP hedge]

/-! ### Entries of weight 2 -/

/-- A rotation class lies inside one component. -/
theorem cyc_subset_component (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P)
    {v : Vtx k} (hv : v ∈ C.1) : cyc v ⊆ C.1 := by
  have h := Hunter.ProofsPathrule.cyc_subset_pc hP hk
    (actualComponentPath_isPathComponent hP C) (v := v)
    (by rw [actualComponentPath_vertsFinset hP C]; exact hv)
  rwa [actualComponentPath_vertsFinset hP C] at h

/-- **Corollary T′, first part, for every Hamiltonian path.**  If the `P`-edge into the tail of
a non-root component has weight 2, it is the door. -/
theorem entry_weight_two (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk)
    (h2 : ew k (pPred P (actualComponentTail hP C)) (actualComponentTail hP C) = 2) :
    actualComponentTail hP C = tau (pPred P (actualComponentTail hP C)) := by
  have key : ∀ p : Vtx k, p = pPred P (actualComponentTail hP C) →
      ew k p (actualComponentTail hP C) = 2 → actualComponentTail hP C = tau p := by
    intro p hp hw
    rcases weight_two_successors hk hw with hs2 | hdoor
    · exfalso
      apply pPred_not_mem hP hk hC
      rw [← hp]
      apply cyc_subset_component hP hk C (actualComponentTail_mem_component hP C)
      rw [Hunter.ProofsExitless.mem_cyc, hs2]
      exact (Hunter.ProofsExitless.rotClass_sigma_iter 2 p).symm
    · exact hdoor
  exact key _ rfl h2

/-- **Corollary T′, second part.**  If the tail of a non-root component `C` is entered by an
edge of weight 2 and `τ₂ e = tail C`, then the rotation class of `e` (the class just before the
first row of `C` in that row's 2-cycle) lies in the parent of `C`. -/
theorem class_before_tail (hP : P.IsHamiltonian) (hk : 2 ≤ k) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP hk)
    (h2 : ew k (pPred P (actualComponentTail hP C)) (actualComponentTail hP C) = 2)
    {e : Vtx k} (he : tau2V e = actualComponentTail hP C) :
    cyc e ⊆ (parentComp hP hk C).1 := by
  have hdoor := entry_weight_two hP hk hC h2
  have hp : sigmaInv e = pPred P (actualComponentTail hP C) :=
    tau_injective hk (he.trans hdoor)
  have hmem : e ∈ (parentComp hP hk C).1 := by
    apply cyc_subset_component hP hk _ (mem_compOf hP hk (pPred P (actualComponentTail hP C)))
    rw [Hunter.ProofsExitless.mem_cyc, ← hp]
    exact rotClass_eq_iff.mpr ⟨k - 1, rfl⟩
  exact cyc_subset_component hP hk _ hmem

/-- In a non-empty set of non-root components that are all entered by an edge of weight 2, one
of them has its class `e` (with `τ₂ e` its tail) in none of them. -/
theorem door_entries_not_closed (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (𝒞 : Finset (ActualComponent P)) (hne : 𝒞.Nonempty)
    (hroot : actualRootComponent hP hk ∉ 𝒞)
    (hdoor : ∀ C ∈ 𝒞,
      ew k (pPred P (actualComponentTail hP C)) (actualComponentTail hP C) = 2) :
    ∃ C ∈ 𝒞, ∀ e : Vtx k, tau2V e = actualComponentTail hP C → ∀ D ∈ 𝒞, e ∉ D.1 := by
  obtain ⟨C, hC, hpar⟩ := exists_parent_not_mem hP hk 𝒞 hne hroot
  refine ⟨C, hC, fun e he D hD heD => hpar ?_⟩
  have hCr : C ≠ actualRootComponent hP hk := fun h => hroot (h ▸ hC)
  have hmem : e ∈ (parentComp hP hk C).1 :=
    class_before_tail hP hk hCr (hdoor C hC) he (Hunter.ProofsExitless.mem_cyc.mpr rfl)
  have h1 : compOf hP hk e = parentComp hP hk C := compOf_eq_of_mem hP hk hmem
  have h2 : compOf hP hk e = D := compOf_eq_of_mem hP hk heD
  rw [← h1, h2]
  exact hD

/-- The last edge of a chain has weight at most `c(s) + 2`. -/
theorem exit_le_cost (hk : 1 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 ≤
      junctionCost hP s hs + 2 := by
  have h := exit_ge_two hk hP s hs
  unfold junctionCost
  omega

/-- A junction of cost 0 enters its target by an edge of weight 2. -/
theorem free_junction_entry (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last)
    (h0 : junctionCost hP s hs = 0) :
    ew k (pPred P (actualComponentTail hP
          (actualNonterminalTargetComponent hP hk (ntEnd s hs))))
        (actualComponentTail hP (actualNonterminalTargetComponent hP hk (ntEnd s hs))) = 2 := by
  have hedge : (actualChainRouteEnd s, (chainTargetTail hP (ntEnd s hs)).1) ∈ P.edges :=
    E1removed_subset P (Sset P) (chainTargetTail_spec hP (ntEnd s hs))
  rw [actualNonterminalTargetComponent_tail hP hk, pPred_eq hP hedge]
  have h1 := exit_ge_two (by omega) hP s hs
  have h2 := exit_le_cost (by omega) hP s hs
  omega

end Path

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.tail_first
#print axioms SuperpermLowerBounds.first_entry
#print axioms SuperpermLowerBounds.parent_tail_lt
#print axioms SuperpermLowerBounds.exists_parent_not_mem
#print axioms SuperpermLowerBounds.exists_iterate_parent_eq_root
#print axioms SuperpermLowerBounds.parent_target
#print axioms SuperpermLowerBounds.entry_weight_two
#print axioms SuperpermLowerBounds.class_before_tail
#print axioms SuperpermLowerBounds.door_entries_not_closed
#print axioms SuperpermLowerBounds.free_junction_entry

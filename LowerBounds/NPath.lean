import LowerBounds.NCore
import LowerBounds.DJunction

/-!
# Theorem W of the written model: the canonical certificate of a Hamiltonian path as `JoinData`

For a Hamiltonian path `P` on `k ≥ 5` symbols, `joinData hk hP : JoinData k (ActualComponent P)`
collects what Theorem N needs from the canonical certificate `cert(P)`:

* the components are those of `F P` (Hunter and Raudvere), each with the list of its block
  entries (`compLine`);
* the permutation `junctionPerm` sends the source of a junction to its target and the one
  component that is the source of no junction to the root (`existsUnique_target`,
  `existsUnique_not_source`);
* for a component `C` other than the root, `sIn C` is the junction into `C`, `jinP C` its cost
  `c(s)`, `slotP C` its last slot, and `parentComp C` the component of that slot;
* `link_into`: Lemma 2 (`theoremL`); `att_into`: Lemma 2 for the attachment at the last slot
  (`offset_route_sigma`); `sigma_ne_blockEntry`: a slot is not the exit of its block.

`sum_charge_le` is the identity for the defect, as the inequality
`HPV(k) + Σ_C (rows + seam excess) + Σ_junctions c(s) ≤ (k-2)! + wt(P) + k`
(from `budget` and `holes_eq`).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-! ### Words -/

/-- The offset of a route up to the rotation of its last slot (Lemma 2 of the written model, first
statement): from `h` an offset `a` leads to `σ v₁`; then the route passes `v₁, …, v_j`. -/
theorem offset_route_sigma (hk : 1 ≤ k) (h : Vtx k) :
    ∀ (L : List (Vtx k)) (hne : L ≠ []) (a : ℕ), 1 ≤ a →
      Offset k a h.1 (sigma (L.head hne)).1 →
      Offset k (a + ((L.zip L.tail).map (fun d => ew k d.1 (sigma d.2) - 1)).sum) h.1
        (sigma (L.getLast hne)).1
  | [], hne, _, _, _ => absurd rfl hne
  | [v], _, a, _, hoff => by
      simpa using hoff
  | v :: w :: rest, _, a, ha, hoff => by
      have hb : 1 ≤ ew k v (sigma w) := (wt_spec hk (le_of_eq v.2.length)).1
      have h2 : Offset k (ew k v (sigma w)) v.1 (sigma w).1 := offset_wt hk v.2.length
      have hstep : Offset k (a + ew k v (sigma w) - 1) h.1 (sigma w).1 :=
        offset_rho_step hk v.2.length ha hb hoff h2
      have ih := offset_route_sigma hk h (w :: rest) (List.cons_ne_nil _ _)
        (a + ew k v (sigma w) - 1) (by omega) hstep
      have hnum : a + (((v :: w :: rest).zip (v :: w :: rest).tail).map
            (fun d => ew k d.1 (sigma d.2) - 1)).sum =
          a + ew k v (sigma w) - 1 + (((w :: rest).zip (w :: rest).tail).map
            (fun d => ew k d.1 (sigma d.2) - 1)).sum := by
        simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
        omega
      rw [hnum]
      exact ih

theorem sigma_iter_pred (hk : 1 ≤ k) (v : Vtx k) : sigma^[k - 1] v = sigmaInv v := by
  have e : sigma^[k - 1 + 1] v = sigma (sigma^[k - 1] v) :=
    Function.iterate_succ_apply' sigma (k - 1) v
  rw [Nat.sub_add_cancel hk, Hunter.ProofsExitless.sigma_iter_period] at e
  rw [← sigmaInv_sigma hk (sigma^[k - 1] v), ← e]

/-- The link sum of a line given by a function on `0, …, m`. -/
theorem linkSum_range_map (f : ℕ → Vtx k) : ∀ m : ℕ,
    linkSum ((List.range (m + 1)).map f) =
      ∑ j ∈ Finset.range m, (ew k (sigmaInv (f j)) (f (j + 1)) - 2)
  | 0 => by simp [linkSum]
  | m + 1 => by
      have ih := linkSum_range_map f m
      have hlast : ((List.range (m + 1)).map f).getLast? = some (f m) := by
        simp [List.getLast?_range]
      have hsplit : (List.range (m + 1 + 1)).map f = (List.range (m + 1)).map f ++ [f (m + 1)] := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [hsplit, linkSum_append _ _ (f m) (f (m + 1)) hlast rfl, ih, Finset.sum_range_succ]
      simp [linkSum]

theorem sum_Icc_one_eq (g : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, g j = ∑ j ∈ Finset.range n, g (j + 1) := by
  have h : Finset.Icc 1 n = (Finset.range n).image (fun j => j + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [h, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.add_right_cancel hab

section Path

variable {P : HPath k}

/-! ### The line of a component -/

/-- The block entries of a component, in order. -/
noncomputable def compLine (hP : P.IsHamiltonian) (C : ActualComponent P) : List (Vtx k) :=
  (List.range (componentClassCount (actualComponentPath hP C))).map
    (blockEntry (actualComponentPath hP C))

/-- The entry of the last block of a component. -/
noncomputable def compLast (hP : P.IsHamiltonian) (C : ActualComponent P) : Vtx k :=
  blockEntry (actualComponentPath hP C) (componentClassCount (actualComponentPath hP C) - 1)

theorem classCount_pos_of (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) :
    0 < componentClassCount (actualComponentPath hP C) :=
  componentClassCount_pos (by omega) (actualComponentPath_stronglyExitless hP hk C)

theorem compLine_head (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) :
    (compLine hP C).head? = some (actualComponentTail hP C) := by
  have hpos := classCount_pos_of hP hk C
  unfold compLine
  rw [List.head?_map, List.head?_range, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
  show some (blockEntry (actualComponentPath hP C) 0) = _
  congr 1
  unfold blockEntry
  rw [Nat.mul_zero, HPath.vert_zero, actualComponentPath_first]

theorem compLine_last (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) :
    (compLine hP C).getLast? = some (compLast hP C) := by
  have hpos := classCount_pos_of hP hk C
  unfold compLine
  rw [List.getLast?_map, List.getLast?_range, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
  rfl

/-- The head of a component is the exit of its last block. -/
theorem head_eq_sigmaInv_last (hP : P.IsHamiltonian) (hk : 2 ≤ k) (C : ActualComponent P) :
    actualComponentHead hP C = sigmaInv (compLast hP C) := by
  have hk1 : 1 ≤ k := by omega
  have hp := actualComponentPath_stronglyExitless hP hk C
  have hN := component_numVerts_eq hk1 hp
  have hpos := classCount_pos_of hP hk C
  unfold compLast
  rw [← actualComponentPath_last hP C, Hunter.Proved.last_eq_vert]
  generalize actualComponentPath hP C = p at hp hN hpos ⊢
  obtain ⟨t', ht'⟩ : ∃ t', componentClassCount p = t' + 1 :=
    ⟨componentClassCount p - 1, by omega⟩
  rw [ht'] at hN ⊢
  rw [Nat.add_sub_cancel]
  have hidx : p.numVerts - 1 = k * t' + (k - 1) := by
    rw [hN, Nat.mul_add, Nat.mul_one]
    omega
  have hlt : k * t' + (k - 1) < p.numVerts := by
    rw [hN, Nat.mul_add, Nat.mul_one]
    omega
  rw [hidx, block_vert hk1 hp.1 (j := t') (r := k - 1) (by omega) hlt, sigma_iter_pred hk1]

/-- **A slot is not the exit of its block**: for `v ∉ C₋₁` (in particular for `v ∈ S(P)`),
`σ v` is not the entry of a block of a component. -/
theorem sigma_ne_blockEntry (hP : P.IsHamiltonian) (hk : 2 ≤ k) {v : Vtx k} (hv : v ∉ Cm1 P)
    (C : ActualComponent P) {j : ℕ} (hj : j < componentClassCount (actualComponentPath hP C)) :
    sigma v ≠ blockEntry (actualComponentPath hP C) j := by
  intro heq
  have hk1 : 1 ≤ k := by omega
  have hp := actualComponentPath_stronglyExitless hP hk C
  have hN := component_numVerts_eq hk1 hp
  have hpc := actualComponentPath_isPathComponent hP C
  have hvC : v ∈ C.1 := by
    apply cyc_subset_component hP hk C (blockEntry_mem hP hk C hj)
    rw [Hunter.ProofsExitless.mem_cyc, ← heq]
    exact (Hunter.ProofsStructure.rotClass_sigma v).symm
  have hvF : v ∈ (actualComponentPath hP C).vertsFinset := by
    rw [actualComponentPath_vertsFinset hP C]
    exact hvC
  have hedge : (v, sigma v) ∈ (actualComponentPath hP C).edges :=
    hpc.2.2 (v, sigma v) (Hunter.ProofsStructure.mem_F_sigma_of_not_Cm1 hv) hvF
  have hpos := Hunter.ProofsStructure.edge_pos_succ hedge
  have hjN : k * j < (actualComponentPath hP C).numVerts := by
    rw [hN]
    exact Nat.mul_lt_mul_of_pos_left hj (by omega)
  have hposj : (actualComponentPath hP C).pos (sigma v) = k * j := by
    rw [heq]
    exact Hunter.ProofsExitless.pos_vert _ hjN
  have hvmem : v ∈ (actualComponentPath hP C).verts := HPath.mem_vertsFinset.mp hvF
  rcases j with _ | j'
  · rw [hposj] at hpos
    omega
  · have hj'N : k * j' < (actualComponentPath hP C).numVerts := by
      rw [hN]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have hpv : (actualComponentPath hP C).pos v = k * (j' + 1) - 1 := by omega
    have hvert : v = sigmaInv (blockEntry (actualComponentPath hP C) j') := by
      rw [← blockExit_eq hk1 hp.1 hjN, ← hpv]
      exact (Hunter.ProofsExitless.vert_pos _ hvmem).symm
    have h2 : sigma v = blockEntry (actualComponentPath hP C) j' := by
      rw [hvert, Hunter.ProofsStructure.sigma_sigmaInv]
    have h3 := blockEntry_injective hk1 hp.1 hjN hj'N (heq.symm.trans h2)
    omega

/-- The cost of the line of a component is its number of rows plus its seam excess. -/
theorem lineCost_compLine (hk : 3 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    lineCost (compLine hP C) = componentPieceCount (actualComponentPath hP C) +
      componentSeamResidual (actualComponentPath hP C) := by
  have hk1 : 1 ≤ k := by omega
  have hp := actualComponentPath_stronglyExitless hP (by omega : 2 ≤ k) C
  have hpos := classCount_pos_of hP (by omega : 2 ≤ k) C
  unfold compLine lineCost
  generalize actualComponentPath hP C = p at hp hpos ⊢
  have hN := component_numVerts_eq hk1 hp
  have e1 := component_excess_eq_boundary_sum hk hp
  have e2 := component_excess_eq_piece_residual hk hp
  have hpc : 1 ≤ componentPieceCount p := by
    unfold componentPieceCount
    omega
  obtain ⟨t', ht'⟩ : ∃ t', componentClassCount p = t' + 1 :=
    ⟨componentClassCount p - 1, by omega⟩
  have h3 : linkSum ((List.range (t' + 1)).map (blockEntry p)) =
      ∑ j ∈ Finset.range t', (Hunter.ProofsLedger.bw p (j + 1) - 2) := by
    rw [linkSum_range_map]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j + 1 < t' + 1 := by
      have := Finset.mem_range.mp hj
      omega
    have hjN : k * (j + 1) < p.numVerts := by
      rw [hN, ht']
      exact Nat.mul_lt_mul_of_pos_left hjt (by omega)
    rw [bw_eq_ew hk1 hp.1 hjN]
  have h4 : ∑ j ∈ componentBoundaries p, (Hunter.ProofsLedger.bw p j - 2) =
      ∑ j ∈ Finset.range t', (Hunter.ProofsLedger.bw p (j + 1) - 2) := by
    unfold componentBoundaries
    rw [ht', Nat.add_sub_cancel]
    exact sum_Icc_one_eq (fun j => Hunter.ProofsLedger.bw p j - 2) t'
  rw [ht', h3, ← h4, ← e1, e2]
  omega

/-! ### The junction into a component -/

/-- The junction into a component other than the root. -/
noncomputable def sIn (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hC : C ≠ actualRootComponent hP (by omega)) : {v : Vtx k // v ∈ chainStarts P} :=
  Classical.choose (existsUnique_target hk hP hC).exists

theorem sIn_spec (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hC : C ≠ actualRootComponent hP (by omega)) :
    sIn hk hP C hC ∈ nonterminal P ∧ tgt hk hP (sIn hk hP C hC) = C :=
  Classical.choose_spec (existsUnique_target hk hP hC).exists

theorem sIn_end (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hC : C ≠ actualRootComponent hP (by omega)) :
    actualChainRouteEnd (sIn hk hP C hC) ≠ P.last :=
  mem_nonterminal.mp (sIn_spec hk hP C hC).1

theorem sIn_tgt (hk : 5 ≤ k) (hP : P.IsHamiltonian) {s : {v : Vtx k // v ∈ chainStarts P}}
    (hs : s ∈ nonterminal P) (hC : tgt hk hP s ≠ actualRootComponent hP (by omega)) :
    sIn hk hP (tgt hk hP s) hC = s :=
  tgt_inj_nonterminal hk hP _ (sIn_spec hk hP _ hC).1 _ hs (sIn_spec hk hP _ hC).2

theorem tgt_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) :
    tgt hk hP s = actualNonterminalTargetComponent hP (by omega) (ntEnd s hs) := by
  unfold tgt
  rw [dif_pos hs]
  rfl

/-- The target of the junction into `C` is `C`. -/
theorem sIn_target (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hC : C ≠ actualRootComponent hP (by omega)) :
    actualNonterminalTargetComponent hP (by omega)
      (ntEnd (sIn hk hP C hC) (sIn_end hk hP C hC)) = C := by
  rw [← tgt_eq hk hP]
  exact (sIn_spec hk hP C hC).2

/-- The component that is the source of no junction. -/
noncomputable def lastComp (hk : 5 ≤ k) (hP : P.IsHamiltonian) : ActualComponent P :=
  Classical.choose (existsUnique_not_source hk hP).exists

theorem lastComp_spec (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∀ s ∈ nonterminal P, actualChainSourceComponent hP (by omega) s ≠ lastComp hk hP :=
  Classical.choose_spec (existsUnique_not_source hk hP).exists

/-- The source of the junction into a component; for the root, the last component. -/
noncomputable def prevComp (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    ActualComponent P :=
  if hC : C = actualRootComponent hP (by omega) then lastComp hk hP
  else actualChainSourceComponent hP (by omega) (sIn hk hP C hC)

theorem prevComp_injective (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    Function.Injective (prevComp hk hP) := by
  intro C D h
  unfold prevComp at h
  by_cases hC : C = actualRootComponent hP (by omega)
  · by_cases hD : D = actualRootComponent hP (by omega)
    · rw [hC, hD]
    · rw [dif_pos hC, dif_neg hD] at h
      exact absurd h.symm (lastComp_spec hk hP _ (sIn_spec hk hP D hD).1)
  · by_cases hD : D = actualRootComponent hP (by omega)
    · rw [dif_neg hC, dif_pos hD] at h
      exact absurd h (lastComp_spec hk hP _ (sIn_spec hk hP C hC).1)
    · rw [dif_neg hC, dif_neg hD] at h
      have hs := actualChainSourceComponent_injective hP (by omega : 2 ≤ k) h
      calc C = tgt hk hP (sIn hk hP C hC) := (sIn_spec hk hP C hC).2.symm
        _ = tgt hk hP (sIn hk hP D hD) := by rw [hs]
        _ = D := (sIn_spec hk hP D hD).2

/-- The junctions as a permutation of the components: source ↦ target, last component ↦ root. -/
noncomputable def junctionPerm (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    Equiv.Perm (ActualComponent P) :=
  (Equiv.ofBijective (prevComp hk hP)
    (Finite.injective_iff_bijective.mp (prevComp_injective hk hP))).symm

theorem junctionPerm_symm_apply (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (junctionPerm hk hP).symm C = prevComp hk hP C := rfl

/-- The cost of the junction into a component (0 for the root). -/
noncomputable def jinP (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  if hC : C = actualRootComponent hP (by omega) then 0
  else junctionCostT hP (sIn hk hP C hC)

/-- The last slot of the junction into a component (for the root a vertex without meaning). -/
noncomputable def slotP (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : Vtx k :=
  if hC : C = actualRootComponent hP (by omega) then P.first
  else actualChainRouteEnd (sIn hk hP C hC)

/-- Lemma 2 for the junction into `A`: from the head of its source to the tail of `A`. -/
theorem link_into (hk : 5 ≤ k) (hP : P.IsHamiltonian) (A : ActualComponent P)
    (hA : A ≠ actualRootComponent hP (by omega)) :
    ew k (sigmaInv (compLast hP (prevComp hk hP A))) (actualComponentTail hP A) ≤
      jinP hk hP A + 3 := by
  have hs := sIn_end hk hP A hA
  have hL := theoremL (by omega : 2 ≤ k) hP (sIn hk hP A hA) hs
  rw [sIn_target hk hP A hA, head_eq_sigmaInv_last hP (by omega)] at hL
  unfold prevComp jinP
  rw [dif_neg hA, dif_neg hA, junctionCostT_of_ne hP _ hs]
  exact hL

/-- Lemma 2 for the attachment at the last slot of the junction into `A`. -/
theorem att_into (hk : 5 ≤ k) (hP : P.IsHamiltonian) (A : ActualComponent P)
    (hA : A ≠ actualRootComponent hP (by omega)) :
    ew k (sigmaInv (compLast hP (prevComp hk hP A))) (sigma (slotP hk hP A)) +
        ew k (slotP hk hP A) (actualComponentTail hP A) ≤ jinP hk hP A + 4 := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hs := sIn_end hk hP A hA
  unfold prevComp jinP slotP
  rw [dif_neg hA, dif_neg hA, dif_neg hA, junctionCostT_of_ne hP _ hs,
    ← head_eq_sigmaInv_last hP hk2, actualChainSourceComponent_head hP hk2]
  have htail : actualComponentTail hP A =
      (chainTargetTail hP (ntEnd (sIn hk hP A hA) hs)).1 := by
    rw [← actualNonterminalTargetComponent_tail hP hk2, sIn_target hk hP A hA]
  rw [htail]
  generalize sIn hk hP A hA = s at hs ⊢
  have h0 := entry_ge_two hk2 hP s
  have hj := exit_ge_two hk1 hP s hs
  have hoff : Offset k (ew k (chainSourceHead hP s).1 (sigma s.1)) (chainSourceHead hP s).1.1
      (sigma ((actualChainRoute s).head (actualChainRoute_ne_nil s))).1 := by
    rw [actualChainRoute_head]
    exact offset_wt hk1 (chainSourceHead hP s).1.2.length
  have h := offset_route_sigma hk1 (chainSourceHead hP s).1 (actualChainRoute s)
    (actualChainRoute_ne_nil s) _ (by omega) hoff
  have hle : ew k (chainSourceHead hP s).1 (sigma (actualChainRouteEnd s)) ≤
      ew k (chainSourceHead hP s).1 (sigma s.1) +
        (((actualChainRoute s).zip (actualChainRoute s).tail).map
          (fun d => ew k d.1 (sigma d.2) - 1)).sum :=
    wt_le_of_offset hk1 (chainSourceHead hP s).1.2.length (by omega) h
  have hint : slotInternalCost (actualChainSlotSequence s) =
      (((actualChainRoute s).zip (actualChainRoute s).tail).map
        (fun d => ew k d.1 (sigma d.2) - 1)).sum := rfl
  unfold junctionCost
  rw [hint]
  omega

/-- The last slot of a junction is not the exit of its block. -/
theorem slotP_not_Cm1 (hk : 5 ≤ k) (hP : P.IsHamiltonian) (A : ActualComponent P)
    (hA : A ≠ actualRootComponent hP (by omega)) : slotP hk hP A ∉ Cm1 P := by
  unfold slotP
  rw [dif_neg hA]
  have hS : actualChainRouteEnd (sIn hk hP A hA) ∈ Sset P :=
    (mem_chainEnds.mp (actualChainRouteEnd_mem_chainEnds _)).1
  rw [Sset, Finset.mem_filter] at hS
  exact hS.2.1

/-- The parent of `A` is the component of the last slot of the junction into `A`. -/
theorem parent_eq_compOf_slot (hk : 5 ≤ k) (hP : P.IsHamiltonian) (A : ActualComponent P)
    (hA : A ≠ actualRootComponent hP (by omega)) :
    parentComp hP (by omega) A = compOf hP (by omega) (slotP hk hP A) := by
  have h := parent_target (by omega : 2 ≤ k) hP (sIn hk hP A hA) (sIn_end hk hP A hA)
  rw [sIn_target hk hP A hA] at h
  unfold slotP
  rw [dif_neg hA]
  exact h

/-! ### The data for Theorem N -/

/-- The canonical certificate of a Hamiltonian path, as the data Theorem N starts from. -/
noncomputable def joinData (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    JoinData k (ActualComponent P) where
  line := compLine hP
  fst := actualComponentTail hP
  lst := compLast hP
  root := actualRootComponent hP (by omega)
  nxt := junctionPerm hk hP
  t := fun C => P.pos (actualComponentTail hP C)
  slot := slotP hk hP
  par := parentComp hP (by omega)
  jin := jinP hk hP
  head_line := compLine_head hP (by omega)
  last_line := compLine_last hP (by omega)
  cover := by
    intro v
    obtain ⟨j, hj, hv⟩ := exists_block hP (by omega : 2 ≤ k) v
    refine ⟨compOf hP (by omega) v, _, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    exact rotClass_eq_iff.mp (Hunter.ProofsExitless.mem_cyc.mp hv)
  distinct := by
    intro C
    unfold compLine
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro i j hi hj hlt hrot
    have h := (block_unique hP (by omega : 2 ≤ k) (List.mem_range.mp hi) (List.mem_range.mp hj)
      hrot).2
    omega
  disjoint := by
    intro C D hne a ha b hb hrot
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    exact hne (block_unique hP (by omega : 2 ≤ k) (List.mem_range.mp hi) (List.mem_range.mp hj)
      hrot).1
  link := by
    intro C hC
    have h := link_into hk hP (junctionPerm hk hP C) hC
    have e : prevComp hk hP (junctionPerm hk hP C) = C :=
      (junctionPerm hk hP).symm_apply_apply C
    rw [e] at h
    exact h
  slot_ne := by
    intro C hC D hmem
    obtain ⟨j, hj, hje⟩ := List.mem_map.mp hmem
    exact sigma_ne_blockEntry hP (by omega) (slotP_not_Cm1 hk hP C hC) D (List.mem_range.mp hj)
      hje.symm
  slot_inj := by
    intro C D hC hD h
    unfold slotP at h
    rw [dif_neg hC, dif_neg hD] at h
    have hs : sIn hk hP C hC = sIn hk hP D hD := chainStartEnd_injective (Subtype.ext h)
    calc C = tgt hk hP (sIn hk hP C hC) := (sIn_spec hk hP C hC).2.symm
      _ = tgt hk hP (sIn hk hP D hD) := by rw [hs]
      _ = D := (sIn_spec hk hP D hD).2
  att := by
    intro C hC
    exact att_into hk hP C hC
  par_mem := by
    intro C hC
    obtain ⟨j, hj, hv⟩ := exists_block hP (by omega : 2 ≤ k) (slotP hk hP C)
    rw [parent_eq_compOf_slot hk hP C hC]
    exact ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩,
      rotClass_eq_iff.mp (Hunter.ProofsExitless.mem_cyc.mp hv)⟩
  par_lt := by
    intro C hC
    exact parent_tail_lt hP (by omega) hC

/-! ### The defect -/

/-- The junction costs, summed over the components other than the root, are at most the sum
over all chains. -/
theorem sum_jinP_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, (if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C) ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s := by
  obtain ⟨f, hf⟩ : ∃ f : ActualComponent P → ℕ,
      f = fun C => if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C := ⟨_, rfl⟩
  have h1 : ∑ C : ActualComponent P, f C = f (actualRootComponent hP (by omega)) +
      ∑ C ∈ Finset.univ.erase (actualRootComponent hP (by omega)), f C :=
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ _)).symm
  have h0 : f (actualRootComponent hP (by omega)) = 0 := by
    rw [hf]
    exact if_pos rfl
  have h2 : ∑ C ∈ Finset.univ.erase (actualRootComponent hP (by omega)), f C =
      ∑ s ∈ nonterminal P, f (tgt hk hP s) := by
    rw [← image_tgt_nonterminal hk hP]
    exact Finset.sum_image (fun x hx y hy h => tgt_inj_nonterminal hk hP x hx y hy h)
  have h3 : ∀ s ∈ nonterminal P, f (tgt hk hP s) = junctionCostT hP s := by
    intro s hs
    have hne : tgt hk hP s ≠ actualRootComponent hP (by omega) := by
      have hmem := Finset.mem_image_of_mem (tgt hk hP) hs
      rw [image_tgt_nonterminal hk hP] at hmem
      exact (Finset.mem_erase.mp hmem).1
    rw [hf]
    show (if tgt hk hP s = actualRootComponent hP (by omega) then 0
      else jinP hk hP (tgt hk hP s)) = _
    rw [if_neg hne]
    unfold jinP
    rw [dif_neg hne, sIn_tgt hk hP hs hne]
  have h4 : ∑ s ∈ nonterminal P, f (tgt hk hP s) ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s := by
    rw [Finset.sum_congr rfl h3]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  show ∑ C : ActualComponent P,
      (fun C => if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C) C ≤ _
  rw [← hf, h1, h0, h2]
  omega

/-- **The identity for the defect, as an inequality.**  Rows plus seam excess of all components
plus the costs of all junctions, plus `HPV(k)`, is at most `(k-2)! + wt(P) + k`. -/
theorem sum_charge_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    hpv k + ∑ C : ActualComponent P, (joinData hk hP).charge C ≤
      (k - 2).factorial + (P.wtP + k) := by
  have hb := budget hk hP
  have hh := holes_eq hk hP
  unfold holesP rowsP at hh
  have hJ := sum_jinP_le hk hP
  have hsplit : ∑ C : ActualComponent P, (joinData hk hP).charge C =
      ∑ C : ActualComponent P, componentPieceCount (actualComponentPath hP C) +
        ∑ C : ActualComponent P, componentSeamResidual (actualComponentPath hP C) +
        ∑ C : ActualComponent P,
          (if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    show lineCost (compLine hP C) +
        (if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C) = _
    rw [lineCost_compLine (by omega) hP C]
  rw [hsplit]
  obtain ⟨Rw, hRw⟩ : ∃ Rw, Rw = ∑ C : ActualComponent P,
      componentPieceCount (actualComponentPath hP C) := ⟨_, rfl⟩
  obtain ⟨Xr, hXr⟩ : ∃ Xr, Xr = ∑ C : ActualComponent P,
      componentSeamResidual (actualComponentPath hP C) := ⟨_, rfl⟩
  obtain ⟨Df, hDf⟩ : ∃ Df, Df = ∑ C : ActualComponent P,
      componentPieceDeficit (actualComponentPath hP C) := ⟨_, rfl⟩
  obtain ⟨Jn, hJn⟩ : ∃ Jn, Jn = ∑ C : ActualComponent P,
      (if C = actualRootComponent hP (by omega) then 0 else jinP hk hP C) := ⟨_, rfl⟩
  obtain ⟨Jt, hJt⟩ : ∃ Jt, Jt = ∑ s : {v : Vtx k // v ∈ chainStarts P}, junctionCostT hP s :=
    ⟨_, rfl⟩
  rw [← hRw, ← hDf] at hh
  rw [← hDf, ← hXr, ← hJt] at hb
  rw [← hJn, ← hJt] at hJ
  rw [← hRw, ← hXr, ← hJn]
  have hpos : 0 < k - 1 := by omega
  apply Nat.le_of_mul_le_mul_left _ hpos
  have hJ' := Nat.mul_le_mul_left (k - 1) hJ
  simp only [Nat.mul_add] at hb ⊢
  omega

end Path

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.offset_route_sigma
#print axioms SuperpermLowerBounds.sigma_ne_blockEntry
#print axioms SuperpermLowerBounds.joinData
#print axioms SuperpermLowerBounds.sum_charge_le

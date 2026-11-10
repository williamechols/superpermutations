import PreimageChain.PathwiseFinalCore

/-!
# Theorem A: the lower bound with denominator k(k-3)

For every `k ≥ 5`

  Ssuper k ≥ k! + (k-1)! + (k-2)! + k - 3 + ⌈2((k-2)! - (k-2)) / (k(k-3))⌉.

The proof uses the preimage-chain library as it is.  For a `σ²`-reduced Hamiltonian path `P`
and the components `C` of its Hunter image, with `r` pieces, deficit `Δ`, seam residual `x`,
minimum entry weight `μ` and first/last full bits `a`, `b`:

* `sum_actual_component_pValue`, `sum_actual_component_t` and the weight equations give the
  Bound-1 baseline as a sum over components;
* `actualBaseline_add_actualPathPaymentCore_le` adds the root gap, the terminal indicator and
  the chain costs;
* `actual_component_capacity`: `2r ≤ (k-2)(Δ + 2x + a + b)` for every component;
* a full first piece of a non-root component forces `μ ≥ 3`
  (`componentFirstFullBit_eq_zero_of_minto_two`);
* a full last piece is paid by the cost of the chain that leaves the component or by
  `μ - 2` of the component it enters (`actual_terminal_full_portal_positive`); only one
  component is left unpaid.

So `Σ(a + b) ≤ 2 + 2 Σ_{C ≠ root}(μ_C - 2) + cost`, and the rest is arithmetic.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- `k! + (k-1)! + (k-2)! + k - 3`. -/
def hpv (k : ℕ) : ℕ := k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3

/-- The bound of Theorem A. -/
def kisicBound (k : ℕ) : ℕ :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + k * (k - 3) - 1) / (k * (k - 3))

section Path

variable {P : HPath k}

/-- Two different components are disjoint, so neither is everything. -/
theorem ne_univ_of_ne (hP : P.IsHamiltonian) {C D : ActualComponent P} (hne : C ≠ D) :
    C.1 ≠ Finset.univ := by
  intro hspan
  apply hne
  apply Subtype.ext
  by_contra hval
  have hdisj := Hunter.ProofsWP.comps_disjoint C.2 D.2 hval
  have hvD : actualComponentHead hP D ∈ D.1 := actualComponentHead_mem_component hP D
  have hvC : actualComponentHead hP D ∈ C.1 := by
    rw [hspan]
    exact Finset.mem_univ _
  exact Finset.disjoint_left.mp hdisj hvC hvD

/-- First piece full. -/
noncomputable def aBit (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  componentFirstFullBit (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- Last piece full. -/
noncomputable def bBit (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  componentLastFullBit (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- `μ - 2` for a component other than the root, and `0` for the root. -/
noncomputable def gap (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  if C = actualRootComponent hP (by omega) then 0 else compMinto (F P) C.1 - 2

theorem aBit_le_one (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    aBit hk hP C ≤ 1 := componentFirstFullBit_le_one _ _ _

theorem bBit_le_one (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    bBit hk hP C ≤ 1 := componentLastFullBit_le_one _ _ _

theorem two_le_minto_of_ne_root (hk : 5 ≤ k) (hP : P.IsHamiltonian) {C : ActualComponent P}
    (hC : C ≠ actualRootComponent hP (by omega)) : 2 ≤ compMinto (F P) C.1 :=
  actual_component_minto_ge_two hP (by omega) C (ne_univ_of_ne hP hC)

/-- A full first piece is paid by the component itself, except at the root. -/
theorem aBit_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    aBit hk hP C ≤ (if C = actualRootComponent hP (by omega) then 1 else 0) + gap hk hP C := by
  have hle := aBit_le_one hk hP C
  by_cases hroot : C = actualRootComponent hP (by omega)
  · rw [if_pos hroot]
    omega
  · have hmu2 := two_le_minto_of_ne_root hk hP hroot
    unfold gap
    rw [if_neg hroot, if_neg hroot]
    by_cases hmu : compMinto (F P) C.1 = 2
    · have hz : aBit hk hP C = 0 :=
        componentFirstFullBit_eq_zero_of_minto_two hk
          (actualComponentPath_stronglyExitless hP (by omega) C)
          (by rw [actualComponentPath_vertsFinset hP C]; exact ne_univ_of_ne hP hroot)
          (by rw [actualComponentPath_minto hP C]; exact hmu)
      omega
    · omega

/-! ### Targets of the chains -/

theorem target_ne_root (hP : P.IsHamiltonian) (hk2 : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    actualNonterminalTargetComponent hP hk2 e ≠ actualRootComponent hP hk2 := by
  intro h
  have h1 := congrArg (actualComponentTail hP) h
  rw [actualNonterminalTargetComponent_tail hP hk2 e, actualComponentTail_root hP hk2] at h1
  have h2 := (Finset.mem_sdiff.mp (chainTargetTail hP e).2).2
  have h3 : P.first ∈ tails P.edges := by
    rw [Hunter.ProofsWP.tails_edges_ham hP]
    exact Finset.mem_singleton_self _
  exact h2 (h1 ▸ h3)

theorem target_injective (hP : P.IsHamiltonian) (hk2 : 2 ≤ k) :
    Function.Injective (actualNonterminalTargetComponent hP hk2) := by
  intro e e' h
  have h1 := congrArg (actualComponentTail hP) h
  rw [actualNonterminalTargetComponent_tail hP hk2 e,
    actualNonterminalTargetComponent_tail hP hk2 e'] at h1
  exact chainTargetTail_injective hP (Subtype.ext h1)

/-- The component a chain enters; the root stands in for the chain that ends at `P.last`. -/
noncomputable def tgt (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) : ActualComponent P :=
  if h : actualChainRouteEnd s ≠ P.last then
    actualNonterminalTargetComponent hP (by omega)
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, h⟩
  else actualRootComponent hP (by omega)

/-- A full last piece is paid by the chain that leaves the component, or by the component
the chain enters; the chain to `P.last` is left unpaid. -/
theorem bBit_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    bBit hk hP (actualChainSourceComponent hP (by omega) s) ≤
      actualChainRouteNatCost hP (by omega) s + gap hk hP (tgt hk hP s) +
        (if actualChainRouteEnd s = P.last then 1 else 0) := by
  have hle := bBit_le_one hk hP (actualChainSourceComponent hP (by omega) s)
  by_cases hend : actualChainRouteEnd s = P.last
  · rw [if_pos hend]
    omega
  · rw [if_neg hend]
    by_cases hbit : bBit hk hP (actualChainSourceComponent hP (by omega) s) = 1
    swap
    · omega
    have hfull := componentLastFullBit_one_implies_lastPieceFull hk
      (actualComponentPath_stronglyExitless hP (by omega)
        (actualChainSourceComponent hP (by omega) s)) hbit
    have hcert := actualComponentLastPieceFull_certificate hP (by omega : 4 ≤ k)
      (actualChainSourceComponent hP (by omega) s) hfull
    have htgt : tgt hk hP s = actualNonterminalTargetComponent hP (by omega)
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hend⟩ := by
      unfold tgt
      rw [dif_pos hend]
    have hnr : tgt hk hP s ≠ actualRootComponent hP (by omega) := by
      rw [htgt]
      exact target_ne_root hP (by omega) _
    have hmu2 := two_le_minto_of_ne_root hk hP hnr
    have hgap : gap hk hP (tgt hk hP s) = compMinto (F P) (tgt hk hP s).1 - 2 := by
      unfold gap
      rw [if_neg hnr]
    by_cases hmu : compMinto (F P) (tgt hk hP s).1 = 2
    · have hpos := actual_terminal_full_portal_positive hP (by omega) hred s hend hcert
        (by rw [← htgt]; exact hmu)
      omega
    · omega

theorem sum_gap_tgt_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ s : {v : Vtx k // v ∈ chainStarts P}, gap hk hP (tgt hk hP s) ≤
      ∑ C : ActualComponent P, gap hk hP C := by
  have h0 : ∀ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteEnd s = P.last →
      gap hk hP (tgt hk hP s) = 0 := by
    intro s hs
    have : tgt hk hP s = actualRootComponent hP (by omega) := by
      unfold tgt
      rw [dif_neg (not_not.mpr hs)]
    rw [this]
    unfold gap
    rw [if_pos rfl]
  have h1 : ∑ s : {v : Vtx k // v ∈ chainStarts P}, gap hk hP (tgt hk hP s) =
      ∑ s ∈ Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s ≠ P.last), gap hk hP (tgt hk hP s) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    apply h0 s
    by_contra hne
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  rw [h1, ← Finset.sum_image (g := tgt hk hP)]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro s hs s' hs' h
    have hs1 : actualChainRouteEnd s ≠ P.last := (Finset.mem_filter.mp hs).2
    have hs2 : actualChainRouteEnd s' ≠ P.last := (Finset.mem_filter.mp hs').2
    unfold tgt at h
    rw [dif_pos hs1, dif_pos hs2] at h
    have he := congrArg Subtype.val (target_injective hP (by omega) h)
    exact chainStartEnd_injective (Subtype.ext he)

theorem card_terminal_le_one :
    (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
      actualChainRouteEnd s = P.last)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs s' hs'
  have h1 := (Finset.mem_filter.mp hs).2
  have h2 := (Finset.mem_filter.mp hs').2
  exact chainStartEnd_injective (Subtype.ext (h1.trans h2.symm))

/-- At most one full last piece is left unpaid: the component that is not the source of a
chain, or the source of the chain that ends at `P.last`. -/
theorem unpaid_le_one (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    (Fintype.card (ActualComponent P) - Fintype.card {v : Vtx k // v ∈ chainStarts P}) +
      (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last)).card ≤ 1 := by
  by_cases hlast : P.last ∈ heads (F P)
  · have hcard : Fintype.card (ActualComponent P) ≤
        Fintype.card {v : Vtx k // v ∈ chainStarts P} + 1 :=
      actualChainSource_card_codimension_one_core hP (by omega : 2 ≤ k)
    have hempty : Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s _ hs
      have hmem := actualChainRouteEnd_mem_chainEnds s
      rw [hs] at hmem
      exact (last_mem_Sset_iff_not_mem_heads hP).mp ((last_mem_chainEnds_iff hP).mp hmem) hlast
    rw [hempty, Finset.card_empty]
    omega
  · have hcard : Fintype.card {v : Vtx k // v ∈ chainStarts P} =
        Fintype.card (ActualComponent P) :=
      Fintype.card_congr (actualChainSourceAllEquiv hP (by omega : 2 ≤ k) hlast)
    have hone := card_terminal_le_one (P := P)
    omega

theorem sum_bBit_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, bBit hk hP C ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
          bBit hk hP (actualChainSourceComponent hP (by omega) s) +
        (Fintype.card (ActualComponent P) -
          Fintype.card {v : Vtx k // v ∈ chainStarts P}) := by
  have hinj := actualChainSourceComponent_injective hP (by omega : 2 ≤ k)
  let I : Finset (ActualComponent P) :=
    Finset.univ.image (actualChainSourceComponent hP (by omega : 2 ≤ k))
  have hsplit : ∑ C : ActualComponent P, bBit hk hP C =
      ∑ C ∈ I, bBit hk hP C + ∑ C ∈ Finset.univ \ I, bBit hk hP C := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have h1 : ∑ C ∈ I, bBit hk hP C =
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        bBit hk hP (actualChainSourceComponent hP (by omega) s) :=
    Finset.sum_image (fun s _ s' _ h => hinj h)
  have h2 : ∑ C ∈ Finset.univ \ I, bBit hk hP C ≤ (Finset.univ \ I).card := by
    calc ∑ C ∈ Finset.univ \ I, bBit hk hP C ≤ ∑ _C ∈ Finset.univ \ I, 1 :=
          Finset.sum_le_sum (fun C _ => bBit_le_one hk hP C)
      _ = (Finset.univ \ I).card := by simp
  have h3 : (Finset.univ \ I).card + I.card = Fintype.card (ActualComponent P) := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
  have h4 : I.card = Fintype.card {v : Vtx k // v ∈ chainStarts P} := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hsplit, h1]
  omega

/-- All full last pieces together. -/
theorem sum_bBit_bound (hk : 5 ≤ k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    ∑ C : ActualComponent P, bBit hk hP C ≤
      actualChainCostSumCore hP (by omega) + ∑ C : ActualComponent P, gap hk hP C + 1 := by
  have h1 := sum_bBit_le hk hP
  have h2 : ∑ s : {v : Vtx k // v ∈ chainStarts P},
      bBit hk hP (actualChainSourceComponent hP (by omega) s) ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        (actualChainRouteNatCost hP (by omega) s + gap hk hP (tgt hk hP s) +
          (if actualChainRouteEnd s = P.last then 1 else 0)) :=
    Finset.sum_le_sum (fun s _ => bBit_le hk hP hred s)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole] at h2
  have h3 := sum_gap_tgt_le hk hP
  have h4 := unpaid_le_one hk hP
  have h5 : actualChainCostSumCore hP (by omega : 2 ≤ k) =
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteNatCost hP (by omega) s := rfl
  simp only [Nat.cast_id] at h2
  omega

/-- All full first pieces together. -/
theorem sum_aBit_bound (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, aBit hk hP C ≤ 1 + ∑ C : ActualComponent P, gap hk hP C := by
  have h := Finset.sum_le_sum (fun (C : ActualComponent P) (_ : C ∈ Finset.univ) =>
    aBit_le hk hP C)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ
    (actualRootComponent hP (by omega : 2 ≤ k)) (fun _ => 1)] at h
  simpa using h

/-! ### The path inequality -/

set_option maxHeartbeats 1600000 in
/-- Theorem A for a `σ²`-reduced Hamiltonian path, without subtraction. -/
theorem reduced_pathwise (hk : 5 ≤ k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    2 * (k - 2).factorial + k * (k - 3) * hpv k ≤
      k * (k - 3) * (P.wtP + k) + 2 * (k - 2) := by
  have hk2 : 2 ≤ k := by omega
  have hw : ∀ C : ActualComponent P, (actualGeom hP C).WeightEquations k :=
    fun C => actualComponentGeometry_weightEquations hP (by omega) C
  have hsumT : ∑ C : ActualComponent P, (actualGeom hP C).t = ((k - 1).factorial : ℤ) :=
    sum_actual_component_t hP hk2
  have hsumP : ∑ C : ActualComponent P, (actualGeom hP C).pValue =
      (actualBaseline P : ℤ) + 1 + (actualMu (distinguishedComponent hP hk2) : ℤ) :=
    sum_actual_component_pValue hP hk2
  obtain ⟨Rz, hRz⟩ : ∃ Rz : ℤ, Rz = ∑ C : ActualComponent P, (actualGeom hP C).r := ⟨_, rfl⟩
  obtain ⟨Xz, hXz⟩ : ∃ Xz : ℤ, Xz = ∑ C : ActualComponent P, (actualGeom hP C).x := ⟨_, rfl⟩
  obtain ⟨Dz, hDz⟩ : ∃ Dz : ℤ, Dz = ∑ C : ActualComponent P, (actualGeom hP C).Delta :=
    ⟨_, rfl⟩
  obtain ⟨Gz, hGz⟩ : ∃ Gz : ℤ, Gz = ∑ C : ActualComponent P, ((actualGeom hP C).mu - 2) :=
    ⟨_, rfl⟩
  obtain ⟨Ea, hEa⟩ : ∃ Ea : ℤ, Ea = ∑ C : ActualComponent P, (aBit hk hP C : ℤ) := ⟨_, rfl⟩
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℤ, Eb = ∑ C : ActualComponent P, (bBit hk hP C : ℤ) := ⟨_, rfl⟩
  obtain ⟨gs, hgs⟩ : ∃ gs : ℤ, gs = ∑ C : ActualComponent P, (gap hk hP C : ℤ) := ⟨_, rfl⟩
  -- the weight equations, summed
  have hF1 : ((k - 1).factorial : ℤ) = ((k : ℤ) - 1) * Rz - Dz := by
    rw [← hsumT, hRz, hDz, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _ => (hw C).1)
  have hF2 : (actualBaseline P : ℤ) + 1 + (actualMu (distinguishedComponent hP hk2) : ℤ) =
      ((k : ℤ) + 1) * ((k - 1).factorial : ℤ) + Rz + Xz + Gz := by
    rw [← hsumP, ← hsumT, hRz, hXz, hGz, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C _
    rw [(hw C).2]
    ring
  -- minimum entry weights
  have hmu : ∀ C : ActualComponent P, (actualGeom hP C).mu = (compMinto (F P) C.1 : ℤ) := by
    intro C
    show ((actualComponentPath hP C).minto : ℤ) = _
    rw [actualComponentPath_minto hP C]
  have hterm : ∀ C : ActualComponent P, (actualGeom hP C).mu - 2 = (gap hk hP C : ℤ) +
      (if C = actualRootComponent hP hk2 then
        (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2 else 0) := by
    intro C
    rw [hmu C]
    by_cases hC : C = actualRootComponent hP hk2
    · have hg : gap hk hP C = 0 := by
        unfold gap
        rw [if_pos hC]
      rw [if_pos hC, hg, hC]
      simp
    · have h2 := two_le_minto_of_ne_root hk hP hC
      have hg : gap hk hP C = compMinto (F P) C.1 - 2 := by
        unfold gap
        rw [if_neg hC]
      rw [if_neg hC, hg, Nat.cast_sub h2]
      simp
  have hGap : Gz = gs + ((compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2) := by
    rw [hGz, hgs, Finset.sum_congr rfl (fun C _ => hterm C), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (actualRootComponent hP hk2)
        (fun _ => (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2)]
    simp
  -- the budget
  have hroot_le := actualMu_le_distinguished hP hk2 (actualRootComponent hP hk2)
  have hmur : (actualMu (actualRootComponent hP hk2) : ℤ) =
      (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) := rfl
  have hbud : (actualBaseline P : ℤ) + ((actualMu (distinguishedComponent hP hk2) : ℤ) -
      (actualMu (actualRootComponent hP hk2) : ℤ)) + (actualTerminalIndicatorCore P : ℤ) +
      (actualChainCostSumCore hP hk2 : ℤ) ≤ (P.wtP : ℤ) := by
    have h := actualBaseline_add_actualPathPaymentCore_le hP hk2
    unfold actualPathPaymentCore actualRootGap at h
    have h' : ((actualBaseline P + (actualMu (distinguishedComponent hP hk2) -
        actualMu (actualRootComponent hP hk2) + actualTerminalIndicatorCore P +
        actualChainCostSumCore hP hk2) : ℕ) : ℤ) ≤ (P.wtP : ℤ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hroot_le] at h'
    linarith
  -- the capacity of every component, summed
  have hcapC : ∀ C : ActualComponent P, 2 * (actualGeom hP C).r ≤
      ((k : ℤ) - 2) * ((actualGeom hP C).Delta + 2 * (actualGeom hP C).x +
        (aBit hk hP C : ℤ) + (bBit hk hP C : ℤ)) := by
    intro C
    have hc := actual_component_capacity hk (actualComponentPath_stronglyExitless hP hk2 C)
    have h' : ((2 * componentPieceCount (actualComponentPath hP C) : ℕ) : ℤ) ≤
        (((k - 2) * (componentPieceDeficit (actualComponentPath hP C) +
          2 * componentSeamResidual (actualComponentPath hP C) + aBit hk hP C +
            bBit hk hP C) : ℕ) : ℤ) := by exact_mod_cast hc
    push_cast [Nat.cast_sub hk2] at h'
    exact h'
  have hcap : 2 * Rz ≤ ((k : ℤ) - 2) * (Dz + 2 * Xz + Ea + Eb) := by
    have h := Finset.sum_le_sum (fun (C : ActualComponent P) (_ : C ∈ Finset.univ) => hcapC C)
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hRz, hDz, hXz, hEa, hEb]
    exact h
  -- the endpoint bits
  have ha : Ea ≤ 1 + gs := by
    rw [hEa, hgs]
    exact_mod_cast sum_aBit_bound hk hP
  have hb : Eb ≤ (actualChainCostSumCore hP hk2 : ℤ) + gs + 1 := by
    rw [hEb, hgs]
    exact_mod_cast sum_bBit_bound hk hP hred
  have hX0 : 0 ≤ Xz := by
    rw [hXz]
    exact Finset.sum_nonneg (fun C _ => Int.natCast_nonneg _)
  have hg0 : 0 ≤ gs := by
    rw [hgs]
    exact Finset.sum_nonneg (fun C _ => Int.natCast_nonneg _)
  have hI0 : (0 : ℤ) ≤ (actualTerminalIndicatorCore P : ℤ) := Int.natCast_nonneg _
  have hc0 : (0 : ℤ) ≤ (actualChainCostSumCore hP hk2 : ℤ) := Int.natCast_nonneg _
  -- factorials
  have hf1 : ((k - 1).factorial : ℤ) = ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by
    have h := Nat.mul_factorial_pred (n := k - 1) (by omega)
    rw [show k - 1 - 1 = k - 2 by omega] at h
    rw [← h]
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  have hf0 : (k.factorial : ℤ) = (k : ℤ) * ((k - 1).factorial : ℤ) := by
    have h := Nat.mul_factorial_pred (n := k) (by omega)
    rw [← h]
    push_cast
    ring
  have hH : (hpv k : ℤ) = (k : ℤ) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) +
      ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) + ((k - 2).factorial : ℤ) + (k : ℤ) - 3 := by
    have h : hpv k + 3 = k.factorial + (k - 1).factorial + (k - 2).factorial + k := by
      unfold hpv
      omega
    have h' : ((hpv k + 3 : ℕ) : ℤ) =
        ((k.factorial + (k - 1).factorial + (k - 2).factorial + k : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    rw [hf0, hf1] at h'
    linarith
  -- arithmetic
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [hf1] at hF1 hF2
  rw [hGap] at hF2
  have hDz' : Dz = ((k : ℤ) - 1) * Rz - ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by linarith
  rw [hDz'] at hcap
  have hA : ((k : ℤ) + 1) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) + Rz + Xz + gs - 3 +
      (actualTerminalIndicatorCore P : ℤ) + (actualChainCostSumCore hP hk2 : ℤ) ≤
      (P.wtP : ℤ) := by
    rw [hmur] at hbud
    linarith
  have hZ : 2 * ((k - 2).factorial : ℤ) + (k : ℤ) * ((k : ℤ) - 3) * (hpv k : ℤ) ≤
      (k : ℤ) * ((k : ℤ) - 3) * ((P.wtP : ℤ) + (k : ℤ)) + 2 * ((k : ℤ) - 2) := by
    rw [hH]
    have hKK3 : (0 : ℤ) ≤ (k : ℤ) * ((k : ℤ) - 3) := by nlinarith
    have hK2 : (0 : ℤ) ≤ (k : ℤ) - 2 := by linarith
    have hK14 : (0 : ℤ) ≤ ((k : ℤ) - 1) * ((k : ℤ) - 4) := by nlinarith
    have hKc : (0 : ℤ) ≤ (k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 2 := by nlinarith
    have hS2 : (0 : ℤ) ≤ 2 + 2 * gs + (actualChainCostSumCore hP hk2 : ℤ) - Ea - Eb := by
      linarith
    have hXg : (0 : ℤ) ≤ Xz + gs := by linarith
    linarith [mul_nonneg hKK3 (sub_nonneg.mpr hA), hcap, mul_nonneg hK2 hS2,
      mul_nonneg hK14 hXg, mul_nonneg hKK3 hI0, mul_nonneg hKc hc0]
  have h3 : 3 ≤ k := by omega
  zify [h3, hk2]
  linarith

end Path

/-! ### From paths to superpermutations -/

/-- A bound for all Hamiltonian paths is a bound for `Ssuper`. -/
theorem ssuper_ge_of_pathwise {N : ℕ} (hk : 1 ≤ k)
    (h : ∀ P : HPath k, P.IsHamiltonian → N ≤ P.wtP + k) : N ≤ Ssuper k := by
  have hham : ∃ P : HPath k, P.IsHamiltonian := Hunter.ProofsSpine.exists_ham k
  have hset : {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty := by
    obtain ⟨P, hP⟩ := hham
    exact ⟨P.wtP, P, hP, rfl⟩
  have hmin : L k ∈ {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m} := by
    unfold L
    exact Nat.sInf_mem hset
  obtain ⟨P, hP, hwt⟩ := hmin
  rw [← Hunter.bridge_Lstar_eq_Ssuper hk]
  change N ≤ L k + k
  rw [← hwt]
  exact h P hP

/-- Theorem A for every Hamiltonian path. -/
theorem pathwise (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    2 * (k - 2).factorial + k * (k - 3) * hpv k ≤
      k * (k - 3) * (P.wtP + k) + 2 * (k - 2) := by
  obtain ⟨Q, hQ, hred, hwt⟩ := sigma2_reduced_normal_form (by omega : 3 ≤ k) hP
  have h := reduced_pathwise hk hQ hred
  have hmono := Nat.mul_le_mul_left (k * (k - 3)) (Nat.add_le_add_right hwt k)
  omega

theorem kisicBound_le_pathwise (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    kisicBound k ≤ P.wtP + k := by
  have h := pathwise hk hP
  have hT : k - 2 ≤ (k - 2).factorial := Nat.self_le_factorial _
  have hd : 0 < k * (k - 3) := Nat.mul_pos (by omega) (by omega)
  unfold kisicBound
  generalize k * (k - 3) = d at h hd ⊢
  generalize (k - 2).factorial = T at h hT ⊢
  have h1 : d * hpv k ≤ d * (P.wtP + k) := by omega
  have hle : hpv k ≤ P.wtP + k := Nat.le_of_mul_le_mul_left h1 hd
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
  rw [hm] at h ⊢
  rw [Nat.mul_add] at h
  have ha : 2 * (T - (k - 2)) ≤ d * m := by omega
  have hdiv : (2 * (T - (k - 2)) + d - 1) / d ≤ m := by
    apply Nat.lt_succ_iff.mp
    rw [Nat.div_lt_iff_lt_mul hd]
    have hs : m.succ * d = d * m + d := by
      rw [Nat.succ_eq_add_one]
      ring
    rw [hs]
    omega
  omega

/-- **Theorem A.** For `k ≥ 5`, every superpermutation on `k` symbols has at least
`k! + (k-1)! + (k-2)! + k - 3 + ⌈2((k-2)! - (k-2)) / (k(k-3))⌉` letters. -/
theorem superperm_kisic_bound (hk : 5 ≤ k) : kisicBound k ≤ Ssuper k :=
  ssuper_ge_of_pathwise (by omega) (fun _ hP => kisicBound_le_pathwise hk hP)

/-- The values of Theorem A for `k = 5, …, 14`. -/
theorem superperm_kisic_numerical_bounds :
    153 ≤ Ssuper 5 ∧
    870 ≤ Ssuper 6 ∧
    5893 ≤ Ssuper 7 ∧
    46121 ≤ Ssuper 8 ∧
    408433 ≤ Ssuper 9 ∧
    4033159 ≤ Ssuper 10 ∧
    43916736 ≤ Ssuper 11 ∧
    522614409 ≤ Ssuper 12 ∧
    6746553315 ≤ Ssuper 13 ∧
    93890534411 ≤ Ssuper 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by decide : kisicBound 5 = 153) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 6 = 870) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 7 = 5893) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 8 = 46121) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 9 = 408433) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 10 = 4033159) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 11 = 43916736) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 12 = 522614409) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 13 = 6746553315) ▸ superperm_kisic_bound (by norm_num)
  · exact (by decide : kisicBound 14 = 93890534411) ▸ superperm_kisic_bound (by norm_num)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.superperm_kisic_bound
#print axioms SuperpermLowerBounds.superperm_kisic_numerical_bounds

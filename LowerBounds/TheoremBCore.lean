import LowerBounds.TheoremA
import LowerBounds.ComponentCapacityB

/-!
# Theorem B from its two geometric lemmas

Theorem B is the lower bound with denominator `k² - 4k + 1`, for `k ≥ 7`:

  Ssuper k ≥ k! + (k-1)! + (k-2)! + k - 3 + ⌈2((k-2)! - (k-2)) / (k² - 4k + 1)⌉.

This file proves it from two statements that are hypotheses here:

* `G5Statement k` (the deficit-one lemma in profile form, see `ComponentCapacityB`);
* `ZStatement k` (Lemma Z: a junction of cost zero into a component of minimum entry weight 2
  has no priced end piece on either side).

The proof follows Theorem A (`TheoremA.lean`), with two changes:

* the capacity of a component is `2r ≤ (k-3)Δ + 2(k-2)x + tailPrice + headPrice`
  (`component_capacity_B`);
* the end prices are paid junction by junction (`junction_le`): for a chain start `s` whose
  route does not end at `P.last`, the price of the first piece of the component it enters plus
  the price of the last piece of the component it leaves is at most `(k² - 4k + 1)` times the
  cost of the chain plus `μ - 2` of the entered component.  Only the first piece of the root
  and one last piece are left unpaid.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- The bound of Theorem B. -/
def boundB (k : ℕ) : ℕ :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + (k * k - 4 * k + 1) - 1) / (k * k - 4 * k + 1)

/-- Lemma Z: for a chain start `s` whose route does not end at `P.last`, of cost 0, entering a
component of minimum entry weight 2, either the entered component is the component the chain
leaves and it has a single piece, or the last piece of the component it leaves and the first
piece of the component it enters both have deficit at least 2. -/
def ZStatement (k : ℕ) : Prop :=
  ∀ (P : HPath k) (hP : P.IsHamiltonian) (hk2 : 2 ≤ k), Sigma2Reduced P →
    ∀ (s : {v : Vtx k // v ∈ chainStarts P}) (hsEnd : actualChainRouteEnd s ≠ P.last),
      actualChainRouteNatCost hP hk2 s = 0 →
      compMinto (F P) (actualNonterminalTargetComponent hP hk2
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2 →
      (actualNonterminalTargetComponent hP hk2
            ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩ =
          actualChainSourceComponent hP hk2 s ∧
        componentPieceCount
            (actualComponentPath hP (actualChainSourceComponent hP hk2 s)) = 1) ∨
      (2 ≤ lastNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualChainSourceComponent hP hk2 s)) (by omega)
              (actualComponentPath_stronglyExitless hP hk2
                (actualChainSourceComponent hP hk2 s))) ∧
        2 ≤ firstNatValue ComponentIntervalPiece.deficit
            (componentIntervalPieces
              (actualComponentPath hP (actualNonterminalTargetComponent hP hk2
                ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩))
              (by omega)
              (actualComponentPath_stronglyExitless hP hk2
                (actualNonterminalTargetComponent hP hk2
                  ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩))))

section Path

variable {P : HPath k}

/-- Price of the first piece of a component. -/
noncomputable def tailP (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  tailPrice (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- Price of the last piece of a component. -/
noncomputable def headP (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) : ℕ :=
  headPrice (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

theorem tailP_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    tailP hk hP C ≤ k - 2 := endPrice_le (by omega) _ _

theorem headP_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    headP hk hP C ≤ k - 2 := endPrice_le (by omega) _ _

/-! ### One junction -/

/-- (P2): the two end prices at a junction are paid by the chain and by the entered
component. -/
theorem junction_le (hk : 7 ≤ k) (hZ : ZStatement k) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P})
    (hend : actualChainRouteEnd s ≠ P.last) :
    tailP (by omega) hP (tgt (by omega) hP s) +
        headP (by omega) hP (actualChainSourceComponent hP (by omega) s) ≤
      (k * k - 4 * k + 1) *
        (actualChainRouteNatCost hP (by omega) s + gap (by omega) hP (tgt (by omega) hP s)) := by
  have hk5 : 5 ≤ k := by omega
  have hkk : 7 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have ht := tailP_le hk5 hP (tgt hk5 hP s)
  have hh := headP_le hk5 hP (actualChainSourceComponent hP (by omega) s)
  have htgt : tgt hk5 hP s = actualNonterminalTargetComponent hP (by omega)
      ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hend⟩ := by
    unfold tgt
    rw [dif_pos hend]
  have hnr : tgt hk5 hP s ≠ actualRootComponent hP (by omega) := by
    rw [htgt]
    exact target_ne_root hP (by omega) _
  have hmu2 := two_le_minto_of_ne_root hk5 hP hnr
  have hgap : gap hk5 hP (tgt hk5 hP s) = compMinto (F P) (tgt hk5 hP s).1 - 2 := by
    unfold gap
    rw [if_neg hnr]
  by_cases hpos : 1 ≤ actualChainRouteNatCost hP (by omega) s + gap hk5 hP (tgt hk5 hP s)
  · have hmul := Nat.mul_le_mul_left (k * k - 4 * k + 1) hpos
    rw [Nat.mul_one] at hmul
    omega
  · have hcost : actualChainRouteNatCost hP (by omega) s = 0 := by omega
    have hmu : compMinto (F P) (tgt hk5 hP s).1 = 2 := by omega
    rcases hZ P hP (by omega) hred s hend hcost (by rw [← htgt]; exact hmu) with
      ⟨hAB, hone⟩ | ⟨hlast, hfirst⟩
    · -- one component with a single piece, which is not full because `μ = 2`
      have hbit : aBit hk5 hP (tgt hk5 hP s) = 0 :=
        componentFirstFullBit_eq_zero_of_minto_two hk5
          (actualComponentPath_stronglyExitless hP (by omega) (tgt hk5 hP s))
          (by rw [actualComponentPath_vertsFinset hP (tgt hk5 hP s)]
              exact ne_univ_of_ne hP hnr)
          (by rw [actualComponentPath_minto hP (tgt hk5 hP s)]; exact hmu)
      have hAB' : actualChainSourceComponent hP (by omega) s = tgt hk5 hP s := by
        rw [htgt]
        exact hAB.symm
      have hone' : componentPieceCount (actualComponentPath hP (tgt hk5 hP s)) = 1 := by
        rw [← hAB']
        exact hone
      have hzero := prices_eq_zero_of_single (by omega)
        (actualComponentPath_stronglyExitless hP (by omega) (tgt hk5 hP s)) hbit hone'
      have h1 : tailP hk5 hP (tgt hk5 hP s) = 0 := hzero.1
      have h2 : headP hk5 hP (actualChainSourceComponent hP (by omega) s) = 0 := by
        rw [hAB']
        exact hzero.2
      rw [h1, h2]
      exact Nat.zero_le _
    · -- both pieces at the junction have deficit at least 2
      have h1 : tailP hk5 hP (tgt hk5 hP s) = 0 := by
        rw [htgt]
        exact tailPrice_eq_zero_of_two_le _ _ hfirst
      have h2 : headP hk5 hP (actualChainSourceComponent hP (by omega) s) = 0 :=
        headPrice_eq_zero_of_two_le _ _ hlast
      rw [h1, h2]
      exact Nat.zero_le _

/-- The same for every chain start; the chain to `P.last` leaves one last piece unpaid. -/
theorem junction_all (hk : 7 ≤ k) (hZ : ZStatement k) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P}) :
    headP (by omega) hP (actualChainSourceComponent hP (by omega) s) +
        (if actualChainRouteEnd s ≠ P.last then
          tailP (by omega) hP (tgt (by omega) hP s) else 0) ≤
      (k * k - 4 * k + 1) *
          (actualChainRouteNatCost hP (by omega) s + gap (by omega) hP (tgt (by omega) hP s)) +
        (k - 2) * (if actualChainRouteEnd s = P.last then 1 else 0) := by
  by_cases hend : actualChainRouteEnd s = P.last
  · rw [if_neg (not_not.mpr hend), if_pos hend]
    have hh := headP_le (by omega : 5 ≤ k) hP (actualChainSourceComponent hP (by omega) s)
    omega
  · rw [if_pos hend, if_neg hend]
    have h := junction_le hk hZ hP hred s hend
    omega

/-! ### The components entered by the chains -/

/-- The chain starts whose route does not end at `P.last`. -/
noncomputable def nonterminal (P : HPath k) : Finset {v : Vtx k // v ∈ chainStarts P} :=
  Finset.univ.filter (fun s => actualChainRouteEnd s ≠ P.last)

theorem mem_nonterminal {s : {v : Vtx k // v ∈ chainStarts P}} :
    s ∈ nonterminal P ↔ actualChainRouteEnd s ≠ P.last := by
  unfold nonterminal
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem tgt_inj_nonterminal (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∀ s ∈ nonterminal P, ∀ s' ∈ nonterminal P, tgt hk hP s = tgt hk hP s' → s = s' := by
  intro s hs s' hs' h
  have hs1 := mem_nonterminal.mp hs
  have hs2 := mem_nonterminal.mp hs'
  unfold tgt at h
  rw [dif_pos hs1, dif_pos hs2] at h
  have he := congrArg Subtype.val (target_injective hP (by omega) h)
  exact chainStartEnd_injective (Subtype.ext he)

/-- All components but one are entered by a chain. -/
theorem card_nonterminal (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    Fintype.card (ActualComponent P) ≤ (nonterminal P).card + 1 := by
  have h := unpaid_le_one hk hP
  have hsplit : (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last)).card + (nonterminal P).card =
      Fintype.card {v : Vtx k // v ∈ chainStarts P} := by
    unfold nonterminal
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  omega

/-- The components entered by the chains are exactly the components other than the root. -/
theorem image_tgt_nonterminal (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    (nonterminal P).image (tgt hk hP) =
      Finset.univ.erase (actualRootComponent hP (by omega)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hC
    have hs1 := mem_nonterminal.mp hs
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    unfold tgt
    rw [dif_pos hs1]
    exact target_ne_root hP (by omega) _
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Finset.card_image_of_injOn
        (fun a ha b hb h => tgt_inj_nonterminal hk hP a ha b hb h)]
    have := card_nonterminal hk hP
    omega

theorem sum_tailP_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, tailP hk hP C =
      tailP hk hP (actualRootComponent hP (by omega)) +
        ∑ s ∈ nonterminal P, tailP hk hP (tgt hk hP s) := by
  have h1 : ∑ C ∈ Finset.univ.erase (actualRootComponent hP (by omega)), tailP hk hP C =
      ∑ s ∈ nonterminal P, tailP hk hP (tgt hk hP s) := by
    rw [← image_tgt_nonterminal hk hP]
    exact Finset.sum_image (fun a ha b hb h => tgt_inj_nonterminal hk hP a ha b hb h)
  rw [← h1]
  exact (Finset.add_sum_erase Finset.univ (tailP hk hP) (Finset.mem_univ _)).symm

/-- Every component but at most one is left by a chain. -/
theorem sum_headP_le (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, headP hk hP C ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
          headP hk hP (actualChainSourceComponent hP (by omega) s) +
        (k - 2) * (Fintype.card (ActualComponent P) -
          Fintype.card {v : Vtx k // v ∈ chainStarts P}) := by
  have hinj := actualChainSourceComponent_injective hP (by omega : 2 ≤ k)
  let I : Finset (ActualComponent P) :=
    Finset.univ.image (actualChainSourceComponent hP (by omega : 2 ≤ k))
  have hsplit : ∑ C : ActualComponent P, headP hk hP C =
      ∑ C ∈ I, headP hk hP C + ∑ C ∈ Finset.univ \ I, headP hk hP C := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have h1 : ∑ C ∈ I, headP hk hP C =
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        headP hk hP (actualChainSourceComponent hP (by omega) s) :=
    Finset.sum_image (fun s _ s' _ h => hinj h)
  have h2 : ∑ C ∈ Finset.univ \ I, headP hk hP C ≤ (k - 2) * (Finset.univ \ I).card := by
    calc ∑ C ∈ Finset.univ \ I, headP hk hP C ≤ ∑ _C ∈ Finset.univ \ I, (k - 2) :=
          Finset.sum_le_sum (fun C _ => headP_le hk hP C)
      _ = (k - 2) * (Finset.univ \ I).card := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have h3 : (Finset.univ \ I).card + I.card = Fintype.card (ActualComponent P) := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
  have h4 : I.card = Fintype.card {v : Vtx k // v ∈ chainStarts P} := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have h5 : (Finset.univ \ I).card = Fintype.card (ActualComponent P) -
      Fintype.card {v : Vtx k // v ∈ chainStarts P} := by omega
  rw [hsplit, h1, ← h5]
  exact Nat.add_le_add_left h2 _

/-- (J′): all end prices together. -/
theorem sum_prices_le (hk : 7 ≤ k) (hZ : ZStatement k) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    ∑ C : ActualComponent P, tailP (by omega) hP C +
        ∑ C : ActualComponent P, headP (by omega) hP C ≤
      2 * (k - 2) + (k * k - 4 * k + 1) *
        (actualChainCostSumCore hP (by omega) +
          ∑ C : ActualComponent P, gap (by omega) hP C) := by
  have hk5 : 5 ≤ k := by omega
  have hsum : ∑ s : {v : Vtx k // v ∈ chainStarts P},
        headP hk5 hP (actualChainSourceComponent hP (by omega) s) +
      ∑ s ∈ nonterminal P, tailP hk5 hP (tgt hk5 hP s) ≤
      (k * k - 4 * k + 1) *
          (∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteNatCost hP (by omega) s +
            ∑ s : {v : Vtx k // v ∈ chainStarts P}, gap hk5 hP (tgt hk5 hP s)) +
        (k - 2) * (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
          actualChainRouteEnd s = P.last)).card := by
    have h := Finset.sum_le_sum (fun (s : {v : Vtx k // v ∈ chainStarts P})
      (_ : s ∈ Finset.univ) => junction_all hk hZ hP hred s)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id] at h
    unfold nonterminal
    rw [Finset.sum_filter]
    exact h
  have ht := sum_tailP_eq hk5 hP
  have hroot := tailP_le hk5 hP (actualRootComponent hP (by omega))
  have hh := sum_headP_le hk5 hP
  have hg := sum_gap_tgt_le hk5 hP
  have hu := unpaid_le_one hk5 hP
  have hm1 : (k - 2) * (Fintype.card (ActualComponent P) -
        Fintype.card {v : Vtx k // v ∈ chainStarts P}) +
      (k - 2) * (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last)).card ≤ k - 2 := by
    rw [← Nat.mul_add]
    calc (k - 2) * (Fintype.card (ActualComponent P) -
            Fintype.card {v : Vtx k // v ∈ chainStarts P} +
          (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
            actualChainRouteEnd s = P.last)).card) ≤ (k - 2) * 1 := Nat.mul_le_mul_left _ hu
      _ = k - 2 := Nat.mul_one _
  have hm2 : (k * k - 4 * k + 1) *
        (∑ s : {v : Vtx k // v ∈ chainStarts P}, actualChainRouteNatCost hP (by omega) s +
          ∑ s : {v : Vtx k // v ∈ chainStarts P}, gap hk5 hP (tgt hk5 hP s)) ≤
      (k * k - 4 * k + 1) * (actualChainCostSumCore hP (by omega) +
        ∑ C : ActualComponent P, gap hk5 hP C) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left hg _)
  omega

/-! ### The path inequality -/

set_option maxHeartbeats 1600000 in
/-- Theorem B for a `σ²`-reduced Hamiltonian path, without subtraction, from (G5) and
Lemma Z. -/
theorem reduced_pathwise_B_of (hk : 7 ≤ k) (hG5 : G5Statement k) (hZ : ZStatement k)
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    2 * (k - 2).factorial + (k * k - 4 * k + 1) * hpv k ≤
      (k * k - 4 * k + 1) * (P.wtP + k) + 2 * (k - 2) := by
  have hk5 : 5 ≤ k := by omega
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
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℤ, Kt = ∑ C : ActualComponent P, (tailP hk5 hP C : ℤ) := ⟨_, rfl⟩
  obtain ⟨Kh, hKh⟩ : ∃ Kh : ℤ, Kh = ∑ C : ActualComponent P, (headP hk5 hP C : ℤ) := ⟨_, rfl⟩
  obtain ⟨gs, hgs⟩ : ∃ gs : ℤ, gs = ∑ C : ActualComponent P, (gap hk5 hP C : ℤ) := ⟨_, rfl⟩
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
  have hterm : ∀ C : ActualComponent P, (actualGeom hP C).mu - 2 = (gap hk5 hP C : ℤ) +
      (if C = actualRootComponent hP hk2 then
        (compMinto (F P) (actualRootComponent hP hk2).1 : ℤ) - 2 else 0) := by
    intro C
    rw [hmu C]
    by_cases hC : C = actualRootComponent hP hk2
    · have hg : gap hk5 hP C = 0 := by
        unfold gap
        rw [if_pos hC]
      rw [if_pos hC, hg, hC]
      simp
    · have h2 := two_le_minto_of_ne_root hk5 hP hC
      have hg : gap hk5 hP C = compMinto (F P) C.1 - 2 := by
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
      ((k : ℤ) - 3) * (actualGeom hP C).Delta + 2 * (((k : ℤ) - 2) * (actualGeom hP C).x) +
        (tailP hk5 hP C : ℤ) + (headP hk5 hP C : ℤ) := by
    intro C
    have hc := component_capacity_B hk hG5 (actualComponentPath_stronglyExitless hP hk2 C)
    have h' : ((2 * componentPieceCount (actualComponentPath hP C) : ℕ) : ℤ) ≤
        (((k - 3) * componentPieceDeficit (actualComponentPath hP C) +
          2 * ((k - 2) * componentSeamResidual (actualComponentPath hP C)) +
            tailP hk5 hP C + headP hk5 hP C : ℕ) : ℤ) := by exact_mod_cast hc
    push_cast [Nat.cast_sub hk2, Nat.cast_sub (by omega : 3 ≤ k)] at h'
    exact h'
  have hcap : 2 * Rz ≤ ((k : ℤ) - 3) * Dz + 2 * (((k : ℤ) - 2) * Xz) + Kt + Kh := by
    have h := Finset.sum_le_sum (fun (C : ActualComponent P) (_ : C ∈ Finset.univ) => hcapC C)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hRz, hDz, hXz, hKt, hKh]
    exact h
  -- the end prices
  have hkk : 4 * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
  have hJ : Kt + Kh ≤ 2 * ((k : ℤ) - 2) + ((k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1) *
      ((actualChainCostSumCore hP hk2 : ℤ) + gs) := by
    have h := sum_prices_le hk hZ hP hred
    have h' : ((∑ C : ActualComponent P, tailP hk5 hP C +
        ∑ C : ActualComponent P, headP hk5 hP C : ℕ) : ℤ) ≤
        ((2 * (k - 2) + (k * k - 4 * k + 1) * (actualChainCostSumCore hP hk2 +
          ∑ C : ActualComponent P, gap hk5 hP C) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hk2, Nat.cast_sub hkk] at h'
    rw [hKt, hKh, hgs]
    exact h'
  have hX0 : 0 ≤ Xz := by
    rw [hXz]
    exact Finset.sum_nonneg (fun C _ => Int.natCast_nonneg _)
  have hI0 : (0 : ℤ) ≤ (actualTerminalIndicatorCore P : ℤ) := Int.natCast_nonneg _
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
  have hK : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rw [hf1] at hF1 hF2
  rw [hGap] at hF2
  have hDz' : Dz = ((k : ℤ) - 1) * Rz - ((k : ℤ) - 1) * ((k - 2).factorial : ℤ) := by linarith
  rw [hDz'] at hcap
  have hA : ((k : ℤ) + 1) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) + Rz + Xz + gs - 3 +
      (actualTerminalIndicatorCore P : ℤ) + (actualChainCostSumCore hP hk2 : ℤ) ≤
      (P.wtP : ℤ) := by
    rw [hmur] at hbud
    linarith
  have hZ' : 2 * ((k - 2).factorial : ℤ) +
      ((k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1) * (hpv k : ℤ) ≤
      ((k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1) * ((P.wtP : ℤ) + (k : ℤ)) +
        2 * ((k : ℤ) - 2) := by
    rw [hH]
    have hPk : (0 : ℤ) ≤ (k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1 := by nlinarith
    have hPk2 : (0 : ℤ) ≤ (k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1 - 2 * ((k : ℤ) - 2) := by
      nlinarith
    linarith [mul_nonneg hPk (sub_nonneg.mpr hA), hcap, hJ, mul_nonneg hPk2 hX0,
      mul_nonneg hPk hI0]
  zify [hkk, hk2]
  linarith

/-- Theorem B for a `σ²`-reduced Hamiltonian path, from (G5) and Lemma Z. -/
theorem theoremB_reduced_of (hk : 7 ≤ k) (hG5 : G5Statement k) (hZ : ZStatement k)
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    (k * k - 4 * k + 1) * hpv k + 2 * ((k - 2).factorial - (k - 2)) ≤
      (k * k - 4 * k + 1) * (P.wtP + k) := by
  have h := reduced_pathwise_B_of hk hG5 hZ hP hred
  have hT : k - 2 ≤ (k - 2).factorial := Nat.self_le_factorial _
  omega

end Path

/-! ### All Hamiltonian paths, and superpermutations -/

/-- Theorem B for every Hamiltonian path, without subtraction, from (G5) and Lemma Z. -/
theorem pathwise_B_of (hk : 7 ≤ k) (hG5 : G5Statement k) (hZ : ZStatement k)
    {P : HPath k} (hP : P.IsHamiltonian) :
    2 * (k - 2).factorial + (k * k - 4 * k + 1) * hpv k ≤
      (k * k - 4 * k + 1) * (P.wtP + k) + 2 * (k - 2) := by
  obtain ⟨Q, hQ, hred, hwt⟩ := sigma2_reduced_normal_form (by omega : 3 ≤ k) hP
  have h := reduced_pathwise_B_of hk hG5 hZ hQ hred
  have hmono := Nat.mul_le_mul_left (k * k - 4 * k + 1) (Nat.add_le_add_right hwt k)
  omega

/-- From the product form to the bound with the ceiling. -/
theorem boundB_le_of_pathwise {w : ℕ}
    (h : 2 * (k - 2).factorial + (k * k - 4 * k + 1) * hpv k ≤
      (k * k - 4 * k + 1) * w + 2 * (k - 2)) : boundB k ≤ w := by
  have hT : k - 2 ≤ (k - 2).factorial := Nat.self_le_factorial _
  have hd : 0 < k * k - 4 * k + 1 := Nat.succ_pos _
  unfold boundB
  generalize k * k - 4 * k + 1 = d at h hd ⊢
  generalize (k - 2).factorial = T at h hT ⊢
  have h1 : d * hpv k ≤ d * w := by omega
  have hle : hpv k ≤ w := Nat.le_of_mul_le_mul_left h1 hd
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

theorem boundB_le_pathwise_of (hk : 7 ≤ k) (hG5 : G5Statement k) (hZ : ZStatement k)
    {P : HPath k} (hP : P.IsHamiltonian) : boundB k ≤ P.wtP + k :=
  boundB_le_of_pathwise (pathwise_B_of hk hG5 hZ hP)

/-- Theorem B for superpermutations, from (G5) and Lemma Z. -/
theorem superperm_boundB_of (hk : 7 ≤ k) (hG5 : G5Statement k) (hZ : ZStatement k) :
    boundB k ≤ Ssuper k :=
  ssuper_ge_of_pathwise (by omega) (fun _ hP => boundB_le_pathwise_of hk hG5 hZ hP)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.reduced_pathwise_B_of
#print axioms SuperpermLowerBounds.theoremB_reduced_of
#print axioms SuperpermLowerBounds.superperm_boundB_of

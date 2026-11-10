import LowerBounds.TheoremBCore
import LowerBounds.ComponentCapacityC
import LowerBounds.LemmaZC

/-!
# Theorem C from the window hypothesis

Let `c = cn / q` and `b = bn / q` be rational numbers, written over one denominator `q > 0`.
`HStatement k cn bn q` says that every window `w` (an exact weight-three chain of a strongly
exitless path that starts and ends with a partial piece and all of whose intervals contain a
piece of deficit at least 2) satisfies `2 r(w) + 2 (k - 4) + c δ(w) ≤ (k - 3) δ(w) + b`.

Under the three conditions `ConditionsC k cn bn q` on the constants, and for `k ≥ 5`, this file
proves for every Hamiltonian path `P`

  `Π (wt(P) + k - hpv k) ≥ 2 (k-2)! - 2 (k-2) - b`,   `Π = k² - 4k + 1 - c (k - 1)`,

in the form `2 q (k-2)! + piC · hpv k ≤ piC · (wt(P) + k) + (2 q (k-2) + bn)` with
`piC = q Π`, and hence `boundC k cn bn q ≤ Ssuper k`.

The proof follows Theorem B (`TheoremBCore.lean`), with three changes:

* the capacity of a component is `component_capacity_C` (slope `k - 3 - c`);
* the prices of the two ends of a component are integers and may be negative;
* at a junction of cost zero into a component of minimum entry weight 2, the two pieces have
  deficits `d, d' ≥ 2` with `d + d' ≥ k` (`lemma_ZC`), and such a pair of ends costs nothing
  (`ChainC.priceC_pair_le_zero`, the place where conditions (i) and (ii) are used).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- `q Π`, where `Π = k² - 4k + 1 - c (k - 1)` is the denominator of Theorem C and
`c = cn / q`. -/
def piC (k cn q : ℕ) : ℕ := q * (k * k - 4 * k + 1) - cn * (k - 1)

/-- The bound of Theorem C: `hpv k + ⌈(2 (k-2)! - 2 (k-2) - b) / Π⌉` with `c = cn / q`,
`b = bn / q`. -/
def boundC (k cn bn q : ℕ) : ℕ :=
  hpv k +
    (2 * q * (k - 2).factorial - (2 * q * (k - 2) + bn) + piC k cn q - 1) / piC k cn q

/-- The conditions on the constants `c = cn / q`, `b = bn / q`, multiplied by `q`:
(i) `b ≤ (k-3)(k-2) - c k - 6`, (ii) `b ≤ 2(k-6) - 4c + (k-5-c)(k-2)`,
(iii) `2(k-2) + b ≤ k² - 4k + 1 - c(k-1)`.  Condition (i) contains `c ≤ k - 5`. -/
structure ConditionsC (k cn bn q : ℕ) : Prop where
  q_pos : 0 < q
  cond_i : bn + cn * k ≤ q * k * (k - 5)
  cond_ii : bn + 4 * cn + 2 * q * k ≤ 4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2)
  cond_iii : 2 * q * (k - 2) + bn + cn * (k - 1) ≤ q * (k * k - 4 * k + 1)

section Constants

variable {cn bn q : ℕ}

/-- `c ≤ k - 5`. -/
theorem ConditionsC.slope (h : ConditionsC k cn bn q) (hk : 1 ≤ k) : cn ≤ q * (k - 5) := by
  have h1 : cn * k ≤ q * (k - 5) * k := by
    have h2 := h.cond_i
    have h3 : q * k * (k - 5) = q * (k - 5) * k := by ring
    omega
  exact Nat.le_of_mul_le_mul_right h1 (by omega)

theorem ConditionsC.full_end_le (h : ConditionsC k cn bn q) :
    2 * q * (k - 2) + bn ≤ piC k cn q :=
  Nat.le_sub_of_add_le h.cond_iii

theorem ConditionsC.piC_pos (h : ConditionsC k cn bn q) (hk : 5 ≤ k) : 0 < piC k cn q := by
  have h1 := h.full_end_le
  have h2 : 0 < 2 * q * (k - 2) := Nat.mul_pos (Nat.mul_pos (by omega) h.q_pos) (by omega)
  omega

theorem ConditionsC.piC_cast (h : ConditionsC k cn bn q) (hk : 5 ≤ k) :
    ((piC k cn q : ℕ) : ℤ) =
      (q : ℤ) * ((k : ℤ) * (k : ℤ) - 4 * (k : ℤ) + 1) - (cn : ℤ) * ((k : ℤ) - 1) := by
  have hkk : 4 * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
  have hle : cn * (k - 1) ≤ q * (k * k - 4 * k + 1) := by
    have h3 := h.cond_iii
    omega
  unfold piC
  push_cast [Nat.cast_sub hle, Nat.cast_sub hkk, Nat.cast_sub (by omega : 1 ≤ k)]
  ring

theorem ConditionsC.full_end_le_cast (h : ConditionsC k cn bn q) (hk : 5 ≤ k) :
    2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := by
  have h4 : ((2 * q * (k - 2) + bn : ℕ) : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := by
    exact_mod_cast h.full_end_le
  push_cast [Nat.cast_sub (by omega : 2 ≤ k)] at h4
  exact h4

theorem full_end_nonneg (hk : 5 ≤ k) :
    (0 : ℤ) ≤ 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) := by
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  have hb : (0 : ℤ) ≤ (bn : ℤ) := Int.natCast_nonneg _
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have h1 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 2)
  linarith

theorem sq_le_two_factorial (hk : 5 ≤ k) : k * k - 4 * k + 1 ≤ 2 * (k - 2).factorial := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
  have h0 : j + 5 - 2 = (j + 2) + 1 := by omega
  have h1 : (j + 5 - 2).factorial = (j + 3) * (j + 2).factorial := by
    rw [h0, Nat.factorial_succ]
  have h2 : j + 2 ≤ (j + 2).factorial := Nat.self_le_factorial _
  have h3 : (j + 3) * (j + 2) ≤ (j + 3) * (j + 2).factorial := Nat.mul_le_mul_left _ h2
  have h4 : (j + 5) * (j + 5) = j * j + 10 * j + 25 := by ring
  have h5 : (j + 3) * (j + 2) = j * j + 5 * j + 6 := by ring
  rw [h1]
  omega

/-- `2 (k-2) + b ≤ 2 (k-2)!`: the numerator of the bound is not negative. -/
theorem ConditionsC.full_end_le_factorial (h : ConditionsC k cn bn q) (hk : 5 ≤ k) :
    2 * q * (k - 2) + bn ≤ 2 * q * (k - 2).factorial := by
  have h1 : 2 * q * (k - 2) + bn ≤ q * (k * k - 4 * k + 1) := by
    have h3 := h.cond_iii
    omega
  have h2 : q * (k * k - 4 * k + 1) ≤ q * (2 * (k - 2).factorial) :=
    Nat.mul_le_mul_left _ (sq_le_two_factorial hk)
  have h3 : q * (2 * (k - 2).factorial) = 2 * q * (k - 2).factorial := by ring
  omega

end Constants

section Path

variable {P : HPath k} {cn bn q : ℕ}

/-- Price of the first piece of a component. -/
noncomputable def tailPC (cn bn q : ℕ) (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  tailPriceC cn bn q (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- Price of the last piece of a component. -/
noncomputable def headPC (cn bn q : ℕ) (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  headPriceC cn bn q (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

theorem tailPC_le (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) (hP : P.IsHamiltonian)
    (C : ActualComponent P) :
    tailPC cn bn q hk hP C ≤ 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) :=
  ChainC.priceC_le hk hc _ _

theorem headPC_le (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) (hP : P.IsHamiltonian)
    (C : ActualComponent P) :
    headPC cn bn q hk hP C ≤ 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) :=
  ChainC.priceC_le hk hc _ _

/-- A path with a single piece that is not full has both end prices at most zero. -/
theorem pricesC_le_zero_of_single {p : HPath k} (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    (hp : p.StronglyExitless) (hbit : componentFirstFullBit p (by omega) hp = 0)
    (hr : componentPieceCount p = 1) :
    tailPriceC cn bn q p (by omega) hp ≤ 0 ∧ headPriceC cn bn q p (by omega) hp ≤ 0 := by
  have hlen : (componentIntervalPieces p (by omega) hp).length = 1 := by
    rw [componentIntervalPieces_length, hr]
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  unfold componentFirstFullBit at hbit
  rw [hx] at hbit
  change actualPieceFullBit x = 0 at hbit
  have hne : x.deficit ≠ 0 := by
    unfold actualPieceFullBit at hbit
    intro h
    rw [if_pos h] at hbit
    omega
  have hE := ChainC.cast_slope_nonneg hk hc
  have hd0 : (0 : ℤ) ≤ ((x.deficit : ℕ) : ℤ) := Int.natCast_nonneg _
  have hprod := mul_nonneg hE hd0
  have h1 : firstNatValue ComponentIntervalPiece.deficit [x] = x.deficit := rfl
  have h2 : lastNatValue ComponentIntervalPiece.deficit [x] = x.deficit := rfl
  unfold tailPriceC headPriceC
  rw [hx, hr, h1, h2, ChainC.priceC_single hne (le_refl 1)]
  constructor <;> linarith

/-! ### One junction -/

/-- The two end prices at a junction are paid by the chain and by the entered component. -/
theorem junction_le_C (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P})
    (hend : actualChainRouteEnd s ≠ P.last) :
    tailPC cn bn q hk hP (tgt hk hP s) +
        headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) ≤
      2 * ((piC k cn q : ℕ) : ℤ) *
        (((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) +
          ((gap hk hP (tgt hk hP s) : ℕ) : ℤ)) := by
  have hc := hcond.slope (by omega)
  have ht := tailPC_le (bn := bn) hk hc hP (tgt hk hP s)
  have hh := headPC_le (bn := bn) hk hc hP (actualChainSourceComponent hP (by omega) s)
  have hMle := hcond.full_end_le_cast hk
  have hPi0 : (0 : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := Int.natCast_nonneg _
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
  by_cases hpos : 1 ≤ actualChainRouteNatCost hP (by omega) s + gap hk hP (tgt hk hP s)
  · have hposZ : (1 : ℤ) ≤ ((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) +
        ((gap hk hP (tgt hk hP s) : ℕ) : ℤ) := by exact_mod_cast hpos
    have hmul := mul_le_mul_of_nonneg_left hposZ hPi0
    linarith
  · have hcost : actualChainRouteNatCost hP (by omega) s = 0 := by omega
    have hgap0 : gap hk hP (tgt hk hP s) = 0 := by omega
    have hmu : compMinto (F P) (tgt hk hP s).1 = 2 := by omega
    have hpair : tailPC cn bn q hk hP (tgt hk hP s) +
        headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) ≤ 0 := by
      rcases lemma_ZC hk hP hred s hend hcost (by rw [← htgt]; exact hmu) with
        ⟨hAB, hone⟩ | ⟨hlast, hfirst, hsum⟩
      · -- one component with a single piece, which is not full because `μ = 2`
        have hbit : aBit hk hP (tgt hk hP s) = 0 :=
          componentFirstFullBit_eq_zero_of_minto_two hk
            (actualComponentPath_stronglyExitless hP (by omega) (tgt hk hP s))
            (by rw [actualComponentPath_vertsFinset hP (tgt hk hP s)]
                exact ne_univ_of_ne hP hnr)
            (by rw [actualComponentPath_minto hP (tgt hk hP s)]; exact hmu)
        have hAB' : actualChainSourceComponent hP (by omega) s = tgt hk hP s := by
          rw [htgt]
          exact hAB.symm
        have hone' : componentPieceCount (actualComponentPath hP (tgt hk hP s)) = 1 := by
          rw [← hAB']
          exact hone
        have hzero := pricesC_le_zero_of_single (cn := cn) (bn := bn) (q := q) hk hc
          (actualComponentPath_stronglyExitless hP (by omega) (tgt hk hP s)) hbit hone'
        have h1 : tailPC cn bn q hk hP (tgt hk hP s) ≤ 0 := hzero.1
        have h2 : headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) ≤ 0 := by
          rw [hAB']
          exact hzero.2
        linarith
      · -- the two pieces at the junction have deficits `≥ 2` with sum `≥ k`
        rw [htgt]
        exact ChainC.priceC_pair_le_zero hk hc hcond.cond_i hcond.cond_ii hfirst hlast
          (by omega) _ _
    rw [hcost, hgap0]
    simpa using hpair

/-- The same for every chain start; the chain to `P.last` leaves one last piece unpaid. -/
theorem junction_all_C (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P}) :
    headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) +
        (if actualChainRouteEnd s ≠ P.last then tailPC cn bn q hk hP (tgt hk hP s) else 0) ≤
      2 * ((piC k cn q : ℕ) : ℤ) *
          (((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) +
            ((gap hk hP (tgt hk hP s) : ℕ) : ℤ)) +
        (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) *
          (if actualChainRouteEnd s = P.last then 1 else 0) := by
  have hPi0 : (0 : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := Int.natCast_nonneg _
  by_cases hend : actualChainRouteEnd s = P.last
  · rw [if_neg (not_not.mpr hend), if_pos hend]
    have hh := headPC_le (bn := bn) hk (hcond.slope (by omega)) hP
      (actualChainSourceComponent hP (by omega) s)
    have h0 : (0 : ℤ) ≤ ((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) +
        ((gap hk hP (tgt hk hP s) : ℕ) : ℤ) :=
      add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hmul := mul_nonneg hPi0 h0
    linarith
  · rw [if_pos hend, if_neg hend]
    have h := junction_le_C hk hcond hP hred s hend
    linarith

/-! ### All junctions -/

theorem sum_tailPC_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, tailPC cn bn q hk hP C =
      tailPC cn bn q hk hP (actualRootComponent hP (by omega)) +
        ∑ s ∈ nonterminal P, tailPC cn bn q hk hP (tgt hk hP s) := by
  have h1 : ∑ C ∈ Finset.univ.erase (actualRootComponent hP (by omega)),
        tailPC cn bn q hk hP C =
      ∑ s ∈ nonterminal P, tailPC cn bn q hk hP (tgt hk hP s) := by
    rw [← image_tgt_nonterminal hk hP]
    exact Finset.sum_image (fun a ha b hb h => tgt_inj_nonterminal hk hP a ha b hb h)
  rw [← h1]
  exact (Finset.add_sum_erase Finset.univ (tailPC cn bn q hk hP) (Finset.mem_univ _)).symm

/-- Every component but at most one is left by a chain. -/
theorem sum_headPC_le (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) (hP : P.IsHamiltonian) :
    ∑ C : ActualComponent P, headPC cn bn q hk hP C ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
          headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) +
        (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) *
          ((Fintype.card (ActualComponent P) -
            Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℕ) : ℤ) := by
  have hinj := actualChainSourceComponent_injective hP (by omega : 2 ≤ k)
  let I : Finset (ActualComponent P) :=
    Finset.univ.image (actualChainSourceComponent hP (by omega : 2 ≤ k))
  have hsplit : ∑ C : ActualComponent P, headPC cn bn q hk hP C =
      ∑ C ∈ I, headPC cn bn q hk hP C + ∑ C ∈ Finset.univ \ I, headPC cn bn q hk hP C := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have h1 : ∑ C ∈ I, headPC cn bn q hk hP C =
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) :=
    Finset.sum_image (fun s _ s' _ h => hinj h)
  have h2 : ∑ C ∈ Finset.univ \ I, headPC cn bn q hk hP C ≤
      (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) * (((Finset.univ \ I).card : ℕ) : ℤ) := by
    calc ∑ C ∈ Finset.univ \ I, headPC cn bn q hk hP C ≤
          ∑ _C ∈ Finset.univ \ I, (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) :=
          Finset.sum_le_sum (fun C _ => headPC_le hk hc hP C)
      _ = (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) * (((Finset.univ \ I).card : ℕ) : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : (Finset.univ \ I).card + I.card = Fintype.card (ActualComponent P) := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
  have h4 : I.card = Fintype.card {v : Vtx k // v ∈ chainStarts P} := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have h5 : (Finset.univ \ I).card = Fintype.card (ActualComponent P) -
      Fintype.card {v : Vtx k // v ∈ chainStarts P} := by omega
  rw [hsplit, h1, ← h5]
  linarith

/-- All end prices together: two full ends are left unpaid. -/
theorem sum_prices_le_C (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q) (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    ∑ C : ActualComponent P, tailPC cn bn q hk hP C +
        ∑ C : ActualComponent P, headPC cn bn q hk hP C ≤
      2 * (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) + 2 * ((piC k cn q : ℕ) : ℤ) *
        (((actualChainCostSumCore hP (by omega) : ℕ) : ℤ) +
          ∑ C : ActualComponent P, ((gap hk hP C : ℕ) : ℤ)) := by
  have hc := hcond.slope (by omega)
  have hMle := hcond.full_end_le_cast hk
  have hM0 := full_end_nonneg (q := q) (bn := bn) hk
  have hPi0 : (0 : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := Int.natCast_nonneg _
  have hsum : ∑ s : {v : Vtx k // v ∈ chainStarts P},
        headPC cn bn q hk hP (actualChainSourceComponent hP (by omega) s) +
      ∑ s ∈ nonterminal P, tailPC cn bn q hk hP (tgt hk hP s) ≤
      2 * ((piC k cn q : ℕ) : ℤ) *
          (∑ s : {v : Vtx k // v ∈ chainStarts P},
              ((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) +
            ∑ s : {v : Vtx k // v ∈ chainStarts P}, ((gap hk hP (tgt hk hP s) : ℕ) : ℤ)) +
        (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) *
          (((Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
            actualChainRouteEnd s = P.last)).card : ℕ) : ℤ) := by
    have h := Finset.sum_le_sum (fun (s : {v : Vtx k // v ∈ chainStarts P})
      (_ : s ∈ Finset.univ) => junction_all_C hk hcond hP hred s)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at h
    unfold nonterminal
    rw [Finset.sum_filter]
    exact h
  have ht := sum_tailPC_eq (cn := cn) (bn := bn) (q := q) hk hP
  have hroot := tailPC_le (bn := bn) hk hc hP (actualRootComponent hP (by omega))
  have hh := sum_headPC_le (bn := bn) hk hc hP
  have hg : ∑ s : {v : Vtx k // v ∈ chainStarts P}, ((gap hk hP (tgt hk hP s) : ℕ) : ℤ) ≤
      ∑ C : ActualComponent P, ((gap hk hP C : ℕ) : ℤ) := by
    exact_mod_cast sum_gap_tgt_le hk hP
  have hu : (((Fintype.card (ActualComponent P) -
        Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℕ) : ℤ)) +
      (((Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last)).card : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast unpaid_le_one hk hP
  have hm1 := mul_le_mul_of_nonneg_left hu hM0
  have hm2 := mul_le_mul_of_nonneg_left hg hPi0
  have hcs : ((actualChainCostSumCore hP (by omega) : ℕ) : ℤ) =
      ∑ s : {v : Vtx k // v ∈ chainStarts P},
        ((actualChainRouteNatCost hP (by omega) s : ℕ) : ℤ) := by
    unfold actualChainCostSumCore
    push_cast
    rfl
  rw [hcs]
  linarith

/-! ### The path inequality -/

set_option maxHeartbeats 1600000 in
/-- Theorem C for a `σ²`-reduced Hamiltonian path, without subtraction, from the window
hypothesis. -/
theorem reduced_pathwise_C_of (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) := by
  have hk2 : 2 ≤ k := by omega
  have hc := hcond.slope (by omega)
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
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℤ, Kt = ∑ C : ActualComponent P, tailPC cn bn q hk hP C :=
    ⟨_, rfl⟩
  obtain ⟨Kh, hKh⟩ : ∃ Kh : ℤ, Kh = ∑ C : ActualComponent P, headPC cn bn q hk hP C :=
    ⟨_, rfl⟩
  obtain ⟨gs, hgs⟩ : ∃ gs : ℤ, gs = ∑ C : ActualComponent P, ((gap hk hP C : ℕ) : ℤ) :=
    ⟨_, rfl⟩
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
  have hterm : ∀ C : ActualComponent P, (actualGeom hP C).mu - 2 = ((gap hk hP C : ℕ) : ℤ) +
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
  have hcapC : ∀ C : ActualComponent P, 4 * (q : ℤ) * (actualGeom hP C).r ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (actualGeom hP C).Delta +
        2 * ((2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) * (actualGeom hP C).x) +
        tailPC cn bn q hk hP C + headPC cn bn q hk hP C := by
    intro C
    exact component_capacity_C (bn := bn) hk hc hH
      (actualComponentPath_stronglyExitless hP hk2 C)
  have hcap : 4 * (q : ℤ) * Rz ≤ 2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * Dz +
      2 * ((2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) * Xz) + Kt + Kh := by
    have h := Finset.sum_le_sum (fun (C : ActualComponent P) (_ : C ∈ Finset.univ) => hcapC C)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [hRz, hDz, hXz, hKt, hKh]
    exact h
  -- the end prices
  have hJ : Kt + Kh ≤ 2 * (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) +
      2 * ((piC k cn q : ℕ) : ℤ) * ((actualChainCostSumCore hP hk2 : ℤ) + gs) := by
    have h := sum_prices_le_C hk hcond hP hred
    rw [hKt, hKh, hgs]
    exact h
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
  have hH' : (hpv k : ℤ) = (k : ℤ) * (((k : ℤ) - 1) * ((k - 2).factorial : ℤ)) +
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
  have hMle := hcond.full_end_le_cast hk
  have hPiEq := hcond.piC_cast hk
  have hPi0 : (0 : ℤ) ≤ ((piC k cn q : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [hf1] at hF1 hF2
  rw [hGap] at hF2
  rw [hmur] at hbud
  -- `m ≥ (r - T) + x + G₁`
  have hm : Rz - ((k - 2).factorial : ℤ) + Xz + gs + (actualChainCostSumCore hP hk2 : ℤ) ≤
      (P.wtP : ℤ) + (k : ℤ) - (hpv k : ℤ) := by
    rw [hH']
    linarith
  -- abbreviations
  obtain ⟨Pi, hPi⟩ : ∃ Pi : ℤ, Pi = ((piC k cn q : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℤ, Kc = (q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ) := ⟨_, rfl⟩
  rw [← hPi] at hJ hMle hPiEq hPi0
  rw [← hM] at hJ hMle hcap
  rw [← hKc] at hcap
  have hDz' : Dz = ((k : ℤ) - 1) * (Rz - ((k - 2).factorial : ℤ)) := by linarith
  have hKD : Kc * Dz = (Pi + 2 * (q : ℤ)) * (Rz - ((k - 2).factorial : ℤ)) := by
    rw [hDz', hPiEq, hKc]
    ring
  have hMX : M * Xz ≤ Pi * Xz := mul_le_mul_of_nonneg_right hMle hX0
  have hPm := mul_le_mul_of_nonneg_left hm hPi0
  have hZ : 2 * (q : ℤ) * ((k - 2).factorial : ℤ) + Pi * (hpv k : ℤ) ≤
      Pi * ((P.wtP : ℤ) + (k : ℤ)) + M := by
    nlinarith
  have hgoal : ((2 * q * (k - 2).factorial + piC k cn q * hpv k : ℕ) : ℤ) ≤
      ((piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hk2]
    rw [← hPi, ← hM]
    linarith
  exact_mod_cast hgoal

end Path

/-! ### All Hamiltonian paths, and superpermutations -/

section All

variable {cn bn q : ℕ}

/-- Theorem C for every Hamiltonian path, without subtraction, from the window hypothesis. -/
theorem pathwise_C_of (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) := by
  obtain ⟨Q, hQ, hred, hwt⟩ := sigma2_reduced_normal_form (by omega : 3 ≤ k) hP
  have h := reduced_pathwise_C_of hk hcond hH hQ hred
  have hmono := Nat.mul_le_mul_left (piC k cn q) (Nat.add_le_add_right hwt k)
  omega

/-- From the product form to the bound with the ceiling. -/
theorem boundC_le_of_pathwise {w : ℕ} (hpi : 0 < piC k cn q)
    (hnum : 2 * q * (k - 2) + bn ≤ 2 * q * (k - 2).factorial)
    (h : 2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * w + (2 * q * (k - 2) + bn)) : boundC k cn bn q ≤ w := by
  unfold boundC
  generalize piC k cn q = d at h hpi ⊢
  generalize 2 * q * (k - 2).factorial = A at h hnum ⊢
  generalize 2 * q * (k - 2) + bn = B at h hnum ⊢
  have h1 : d * hpv k ≤ d * w := by omega
  have hle : hpv k ≤ w := Nat.le_of_mul_le_mul_left h1 hpi
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
  rw [hm] at h ⊢
  rw [Nat.mul_add] at h
  have ha : A - B ≤ d * m := by omega
  have hdiv : (A - B + d - 1) / d ≤ m := by
    apply Nat.lt_succ_iff.mp
    rw [Nat.div_lt_iff_lt_mul hpi]
    have hs : m.succ * d = d * m + d := by
      rw [Nat.succ_eq_add_one]
      ring
    rw [hs]
    omega
  omega

theorem boundC_le_pathwise_of (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    boundC k cn bn q ≤ P.wtP + k :=
  boundC_le_of_pathwise (hcond.piC_pos hk) (hcond.full_end_le_factorial hk)
    (pathwise_C_of hk hcond hH hP)

/-- Theorem C for superpermutations, from the window hypothesis. -/
theorem superperm_boundC_of (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) : boundC k cn bn q ≤ Ssuper k :=
  ssuper_ge_of_pathwise (by omega) (fun _ hP => boundC_le_pathwise_of hk hcond hH hP)

end All

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.junction_le_C
#print axioms SuperpermLowerBounds.reduced_pathwise_C_of
#print axioms SuperpermLowerBounds.pathwise_C_of
#print axioms SuperpermLowerBounds.superperm_boundC_of

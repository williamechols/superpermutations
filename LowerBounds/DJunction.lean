import LowerBounds.JCoverage
import LowerBounds.DCapacity

/-!
# Theorem D: the junctions (Lemma D2) and the line inequality (Proposition D3)

the written proof of Theorem D, section 3.  Let `(a, b, c)` be a chain line with `a ≤ b` that is
*closed*, `c + 2 a ≤ b k`, and `γ = min (b - a) (b k - c - 2 a)` (`gammaD`).

* `junction_le_D` (Lemma D2): at a junction of a `σ²`-reduced Hamiltonian path the price of the
  first piece of the entered component plus the price of the last piece of the component that is
  left is at most `2 c` if the junction is paid and at most `-2 γ` if it is free.  The free case
  is `free_junction_rows` (Lemma Z with the sum of the deficits).
* `lineD_reduced_holes` (Proposition D3): for a `σ²`-reduced Hamiltonian path
  `a R + γ F ≤ b Δ + c (1 + X⁺ + J⁺)`, with `R` the rows, `Δ` the holes, `X⁺` the seams of weight
  at least 4, `J⁺` the paid and `F` the free junctions; `lineD_reduced` is the same with
  `Δ = (k - 1) (R - (k-2)!)` (`holes_eq`).

The summation is that of `sum_prices_le_C` (`TheoremCCore.lean`): every component but the root is
entered by exactly one junction, every component but one is left by a chain, and the two ends that
are left over cost at most `c` each.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- `γ = min (b - a) (b k - c - 2 a)`: what a free junction gives back, halved. -/
def gammaD (k a b c : ℕ) : ℕ := min (b - a) (b * k - c - 2 * a)

section Constants

variable {a b c : ℕ}

theorem gammaD_le_left (hab : a ≤ b) : ((gammaD k a b c : ℕ) : ℤ) ≤ (b : ℤ) - (a : ℤ) := by
  have h : gammaD k a b c ≤ b - a := Nat.min_le_left _ _
  have h' : ((gammaD k a b c + a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) := by
    exact_mod_cast (by omega : gammaD k a b c + a ≤ b)
  push_cast at h'
  linarith

theorem gammaD_le_right (hclosed : c + 2 * a ≤ b * k) :
    ((gammaD k a b c : ℕ) : ℤ) ≤ (b : ℤ) * (k : ℤ) - (c : ℤ) - 2 * (a : ℤ) := by
  have h : gammaD k a b c ≤ b * k - c - 2 * a := Nat.min_le_right _ _
  have h' : ((gammaD k a b c + c + 2 * a : ℕ) : ℤ) ≤ ((b * k : ℕ) : ℤ) := by
    exact_mod_cast (by omega : gammaD k a b c + c + 2 * a ≤ b * k)
  push_cast at h'
  linarith

/-- Two ends of deficits `d, d' ≥ 2` with `d + d' ≥ k`: what the pieces at a free junction
cost, whatever the numbers of pieces of the two components. -/
theorem priceD_pair_le (hk : 5 ≤ k) (hab : a ≤ b) (hclosed : c + 2 * a ≤ b * k) {d d' : ℕ}
    (hd : 2 ≤ d) (hd' : 2 ≤ d') (hsum : k ≤ d + d') (r r' : ℕ) :
    priceD a b c d r + priceD a b c d' r' ≤ -2 * ((gammaD k a b c : ℕ) : ℤ) := by
  have hg1 := gammaD_le_left (k := k) (c := c) hab
  have hg2 := gammaD_le_right hclosed
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  have habz : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  have hdz : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdz' : (2 : ℤ) ≤ (d' : ℤ) := by exact_mod_cast hd'
  have hsz : (k : ℤ) ≤ (d : ℤ) + (d' : ℤ) := by exact_mod_cast hsum
  have hkz : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hm1 := mul_le_mul_of_nonneg_left hsz hb0
  have hm2 := mul_le_mul_of_nonneg_left hdz hb0
  have hm3 := mul_le_mul_of_nonneg_left hdz' hb0
  have hm4 := mul_le_mul_of_nonneg_left hkz hb0
  by_cases hr : r ≤ 1 <;> by_cases hr' : r' ≤ 1
  · rw [priceD_one (by omega) hr, priceD_one (by omega) hr']
    linarith
  · rw [priceD_one (by omega) hr, priceD_two (by omega) (by omega)]
    linarith
  · rw [priceD_two (by omega) (by omega), priceD_one (by omega) hr']
    linarith
  · rw [priceD_two (by omega) (by omega), priceD_two (by omega) (by omega)]
    linarith

end Constants

section Path

variable {P : HPath k} {a b c : ℕ}

/-- Price of the first piece of a component. -/
noncomputable def tailPD (a b c : ℕ) (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  tailPriceD a b c (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

/-- Price of the last piece of a component. -/
noncomputable def headPD (a b c : ℕ) (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  headPriceD a b c (actualComponentPath hP C) (by omega)
    (actualComponentPath_stronglyExitless hP (by omega) C)

theorem tailPD_le (hk : 5 ≤ k) (hab : a ≤ b) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    tailPD a b c hk hP C ≤ (c : ℤ) :=
  priceD_le hab _ _

theorem headPD_le (hk : 5 ≤ k) (hab : a ≤ b) (hP : P.IsHamiltonian) (C : ActualComponent P) :
    headPD a b c hk hP C ≤ (c : ℤ) :=
  priceD_le hab _ _

/-- A path with a single piece that is not full: both end prices are `a - b d`, `d ≥ 1` the
deficit of the piece. -/
theorem pricesD_of_single {p : HPath k} (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (hbit : componentFirstFullBit p (by omega) hp = 0) (hr : componentPieceCount p = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ tailPriceD a b c p (by omega) hp = (a : ℤ) - (b : ℤ) * (d : ℤ) ∧
      headPriceD a b c p (by omega) hp = (a : ℤ) - (b : ℤ) * (d : ℤ) := by
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
  have h1 : firstNatValue ComponentIntervalPiece.deficit [x] = x.deficit := rfl
  have h2 : lastNatValue ComponentIntervalPiece.deficit [x] = x.deficit := rfl
  refine ⟨x.deficit, Nat.one_le_iff_ne_zero.mpr hne, ?_, ?_⟩
  · unfold tailPriceD
    rw [hx, hr, h1, priceD_one hne (le_refl 1)]
  · unfold headPriceD
    rw [hx, hr, h2, priceD_one hne (le_refl 1)]

/-! ### One junction -/

/-- **Lemma D2.**  The two end prices at a junction: at most `2 c` at a paid junction, at most
`-2 γ` at a free junction. -/
theorem junction_le_D (hk : 5 ≤ k) (hab : a ≤ b) (hclosed : c + 2 * a ≤ b * k)
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P})
    (hend : actualChainRouteEnd s ≠ P.last) :
    tailPD a b c hk hP (tgt hk hP s) +
        headPD a b c hk hP (actualChainSourceComponent hP (by omega) s) ≤
      if junctionCostT hP s = 0 then -2 * ((gammaD k a b c : ℕ) : ℤ) else 2 * (c : ℤ) := by
  have ht := tailPD_le (c := c) hk hab hP (tgt hk hP s)
  have hh := headPD_le (c := c) hk hab hP (actualChainSourceComponent hP (by omega) s)
  by_cases h0 : junctionCostT hP s = 0
  · rw [if_pos h0]
    rw [junctionCostT_of_ne hP s hend] at h0
    have htgt : tgt hk hP s = actualNonterminalTargetComponent hP (by omega) (ntEnd s hend) := by
      unfold tgt
      rw [dif_pos hend]
      rfl
    obtain ⟨-, hmu⟩ := (junctionCost_eq_zero_iff (by omega) hP s hend).mp h0
    rcases free_junction_rows hk hP hred s hend h0 with ⟨hAB, hone⟩ | ⟨hlast, hfirst, hsum⟩
    · -- a loop on a single piece, which is not full because `μ = 2`
      have hnr : tgt hk hP s ≠ actualRootComponent hP (by omega) := by
        rw [htgt]
        exact target_ne_root hP (by omega) _
      have hbit : componentFirstFullBit (actualComponentPath hP (tgt hk hP s)) (by omega)
          (actualComponentPath_stronglyExitless hP (by omega) (tgt hk hP s)) = 0 :=
        componentFirstFullBit_eq_zero_of_minto_two hk
          (actualComponentPath_stronglyExitless hP (by omega) (tgt hk hP s))
          (by rw [actualComponentPath_vertsFinset hP (tgt hk hP s)]
              exact ne_univ_of_ne hP hnr)
          (by rw [actualComponentPath_minto hP (tgt hk hP s), htgt]; exact hmu)
      have hAB' : actualChainSourceComponent hP (by omega) s = tgt hk hP s := by
        rw [htgt]
        exact hAB.symm
      have hone' : componentPieceCount (actualComponentPath hP (tgt hk hP s)) = 1 := by
        rw [← hAB']
        exact hone
      obtain ⟨d, hd, h1, h2⟩ := pricesD_of_single (a := a) (b := b) (c := c) hk
        (actualComponentPath_stronglyExitless hP (by omega) (tgt hk hP s)) hbit hone'
      have e1 : tailPD a b c hk hP (tgt hk hP s) = (a : ℤ) - (b : ℤ) * (d : ℤ) := h1
      have e2 : headPD a b c hk hP (actualChainSourceComponent hP (by omega) s) =
          (a : ℤ) - (b : ℤ) * (d : ℤ) := by
        rw [hAB']
        exact h2
      rw [e1, e2]
      have hg1 := gammaD_le_left (k := k) (c := c) hab
      have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
      have hdz : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hm := mul_le_mul_of_nonneg_left hdz hb0
      linarith
    · -- the two pieces at the junction have deficits `≥ 2` with sum `≥ k`
      rw [htgt]
      exact priceD_pair_le hk hab hclosed hfirst hlast (by omega) _ _
  · rw [if_neg h0]
    linarith

/-- The same for every chain start; the chain to `P.last` leaves one last piece unpaid. -/
theorem junction_all_D (hk : 5 ≤ k) (hab : a ≤ b) (hclosed : c + 2 * a ≤ b * k)
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) (s : {v : Vtx k // v ∈ chainStarts P}) :
    headPD a b c hk hP (actualChainSourceComponent hP (by omega) s) +
        (if actualChainRouteEnd s ≠ P.last then tailPD a b c hk hP (tgt hk hP s) else 0) ≤
      (c : ℤ) * (if actualChainRouteEnd s = P.last then 1 else 0) +
        2 * (c : ℤ) * (if junctionCostT hP s ≠ 0 then 1 else 0) -
        2 * ((gammaD k a b c : ℕ) : ℤ) * (if s ∈ freeJunctions hP then 1 else 0) := by
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  by_cases hend : actualChainRouteEnd s = P.last
  · have hcost : junctionCostT hP s = 0 := by
      unfold junctionCostT
      rw [dif_neg (not_not.mpr hend)]
    have hfree : s ∉ freeJunctions hP := by
      intro hmem
      exact (mem_nonterminal.mp (Finset.mem_filter.mp hmem).1) hend
    rw [if_neg (not_not.mpr hend), if_pos hend, if_neg (not_not.mpr hcost), if_neg hfree]
    have hh := headPD_le (c := c) hk hab hP (actualChainSourceComponent hP (by omega) s)
    linarith
  · have h := junction_le_D (c := c) hk hab hclosed hP hred s hend
    rw [if_pos hend, if_neg hend]
    by_cases h0 : junctionCostT hP s = 0
    · have hfree : s ∈ freeJunctions hP :=
        Finset.mem_filter.mpr ⟨mem_nonterminal.mpr hend, h0⟩
      rw [if_pos h0] at h
      rw [if_neg (not_not.mpr h0), if_pos hfree]
      linarith
    · have hfree : s ∉ freeJunctions hP := fun hmem => h0 (Finset.mem_filter.mp hmem).2
      rw [if_neg h0] at h
      rw [if_pos h0, if_neg hfree]
      linarith

/-! ### All junctions -/

/-- A sum over the components: the root, and the components entered by the chains. -/
theorem sum_comp_eq_root_add_targets (hk : 5 ≤ k) (hP : P.IsHamiltonian)
    (f : ActualComponent P → ℤ) :
    ∑ C : ActualComponent P, f C =
      f (actualRootComponent hP (by omega)) + ∑ s ∈ nonterminal P, f (tgt hk hP s) := by
  have h1 : ∑ C ∈ Finset.univ.erase (actualRootComponent hP (by omega)), f C =
      ∑ s ∈ nonterminal P, f (tgt hk hP s) := by
    rw [← image_tgt_nonterminal hk hP]
    exact Finset.sum_image (fun x hx y hy h => tgt_inj_nonterminal hk hP x hx y hy h)
  rw [← h1]
  exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ _)).symm

/-- A sum over the components of a function bounded by `M`: every component but those that no
chain leaves is the source of exactly one chain. -/
theorem sum_comp_le_sources (hk : 5 ≤ k) (hP : P.IsHamiltonian) (f : ActualComponent P → ℤ)
    (M : ℤ) (hf : ∀ C, f C ≤ M) :
    ∑ C : ActualComponent P, f C ≤
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, f (actualChainSourceComponent hP (by omega) s) +
        M * ((Fintype.card (ActualComponent P) -
          Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℕ) : ℤ) := by
  have hinj := actualChainSourceComponent_injective hP (by omega : 2 ≤ k)
  let I : Finset (ActualComponent P) :=
    Finset.univ.image (actualChainSourceComponent hP (by omega : 2 ≤ k))
  have hsplit : ∑ C : ActualComponent P, f C =
      ∑ C ∈ I, f C + ∑ C ∈ Finset.univ \ I, f C := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have h1 : ∑ C ∈ I, f C =
      ∑ s : {v : Vtx k // v ∈ chainStarts P}, f (actualChainSourceComponent hP (by omega) s) :=
    Finset.sum_image (fun s _ s' _ h => hinj h)
  have h2 : ∑ C ∈ Finset.univ \ I, f C ≤ M * (((Finset.univ \ I).card : ℕ) : ℤ) := by
    calc ∑ C ∈ Finset.univ \ I, f C ≤ ∑ _C ∈ Finset.univ \ I, M :=
          Finset.sum_le_sum (fun C _ => hf C)
      _ = M * (((Finset.univ \ I).card : ℕ) : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : (Finset.univ \ I).card + I.card = Fintype.card (ActualComponent P) := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
  have h4 : I.card = Fintype.card {v : Vtx k // v ∈ chainStarts P} := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have h5 : (Finset.univ \ I).card = Fintype.card (ActualComponent P) -
      Fintype.card {v : Vtx k // v ∈ chainStarts P} := by omega
  rw [hsplit, h1, ← h5]
  linarith

/-- The rows of a Hamiltonian path: the pieces of all its components. -/
noncomputable def rowsP (hP : P.IsHamiltonian) : ℕ :=
  ∑ C : ActualComponent P, componentPieceCount (actualComponentPath hP C)

/-- The holes: the deficits of all rows. -/
noncomputable def holesP (hP : P.IsHamiltonian) : ℕ :=
  ∑ C : ActualComponent P, componentPieceDeficit (actualComponentPath hP C)

/-- The seams of weight at least 4 of all components. -/
noncomputable def heavyP (hP : P.IsHamiltonian) : ℕ :=
  ∑ C : ActualComponent P, (componentPositiveSeams (actualComponentPath hP C)).card

/-- **(F1)**: `holes = (k - 1) (rows - (k-2)!)`, for every Hamiltonian path. -/
theorem holes_eq (hk : 5 ≤ k) (hP : P.IsHamiltonian) :
    holesP hP + (k - 1) * (k - 2).factorial = (k - 1) * rowsP hP := by
  have hsum := sum_actual_component_classCount_nat hP (by omega : 2 ≤ k)
  have hC : ∀ C : ActualComponent P,
      componentClassCount (actualComponentPath hP C) +
          componentPieceDeficit (actualComponentPath hP C) =
        (k - 1) * componentPieceCount (actualComponentPath hP C) :=
    fun C => componentClassCount_add_deficit (by omega)
      (actualComponentPath_stronglyExitless hP (by omega) C)
  have hall := Finset.sum_congr (s₁ := (Finset.univ : Finset (ActualComponent P))) rfl
    (fun C _ => hC C)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at hall
  have hf : (k - 1).factorial = (k - 1) * (k - 2).factorial := by
    have h := Nat.mul_factorial_pred (n := k - 1) (by omega)
    rw [show k - 1 - 1 = k - 2 by omega] at h
    exact h.symm
  unfold holesP rowsP
  rw [← hf]
  omega

set_option maxHeartbeats 1600000 in
/-- **Proposition D3**, with the holes: for a closed chain line and a `σ²`-reduced Hamiltonian
path, `a R + γ F ≤ b Δ + c (1 + X⁺ + J⁺)`. -/
theorem lineD_reduced_holes (hk : 5 ≤ k) (hab : a ≤ b) (hline : ChainLine k a b c)
    (hclosed : c + 2 * a ≤ b * k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    a * rowsP hP + gammaD k a b c * (freeJunctions hP).card ≤
      b * holesP hP + c * (1 + heavyP hP + (paidJunctions hP).card) := by
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℤ, Kt = ∑ C : ActualComponent P, tailPD a b c hk hP C := ⟨_, rfl⟩
  obtain ⟨Kh, hKh⟩ : ∃ Kh : ℤ, Kh = ∑ C : ActualComponent P, headPD a b c hk hP C := ⟨_, rfl⟩
  -- the capacity of every component, summed
  have hcapC : ∀ C : ActualComponent P,
      2 * (a : ℤ) * ((componentPieceCount (actualComponentPath hP C) : ℕ) : ℤ) ≤
        2 * (b : ℤ) * ((componentPieceDeficit (actualComponentPath hP C) : ℕ) : ℤ) +
          2 * (c : ℤ) * (((componentPositiveSeams (actualComponentPath hP C)).card : ℕ) : ℤ) +
          tailPD a b c hk hP C + headPD a b c hk hP C :=
    fun C => component_capacity_D hk hline (actualComponentPath_stronglyExitless hP (by omega) C)
  have hcap : 2 * (a : ℤ) * ((rowsP hP : ℕ) : ℤ) ≤
      2 * (b : ℤ) * ((holesP hP : ℕ) : ℤ) + 2 * (c : ℤ) * ((heavyP hP : ℕ) : ℤ) + Kt + Kh := by
    have h := Finset.sum_le_sum (fun (C : ActualComponent P) (_ : C ∈ Finset.univ) => hcapC C)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    unfold rowsP holesP heavyP
    rw [hKt, hKh]
    push_cast
    exact h
  -- the junctions
  have hsum : ∑ s : {v : Vtx k // v ∈ chainStarts P},
        headPD a b c hk hP (actualChainSourceComponent hP (by omega) s) +
      ∑ s ∈ nonterminal P, tailPD a b c hk hP (tgt hk hP s) ≤
      (c : ℤ) * (((Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
          actualChainRouteEnd s = P.last)).card : ℕ) : ℤ) +
        2 * (c : ℤ) * (((paidJunctions hP).card : ℕ) : ℤ) -
        2 * ((gammaD k a b c : ℕ) : ℤ) * (((freeJunctions hP).card : ℕ) : ℤ) := by
    have h := Finset.sum_le_sum (fun (s : {v : Vtx k // v ∈ chainStarts P})
      (_ : s ∈ Finset.univ) => junction_all_D (c := c) hk hab hclosed hP hred s)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole] at h
    have hfree : (Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        s ∈ freeJunctions hP)) = freeJunctions hP := by
      ext s
      simp
    rw [hfree] at h
    unfold nonterminal
    rw [Finset.sum_filter]
    exact h
  have ht := sum_comp_eq_root_add_targets hk hP (tailPD a b c hk hP)
  have hroot := tailPD_le (c := c) hk hab hP (actualRootComponent hP (by omega))
  have hh := sum_comp_le_sources hk hP (headPD a b c hk hP) (c : ℤ)
    (fun C => headPD_le hk hab hP C)
  have hu : (((Fintype.card (ActualComponent P) -
        Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℕ) : ℤ)) +
      (((Finset.univ.filter (fun s : {v : Vtx k // v ∈ chainStarts P} =>
        actualChainRouteEnd s = P.last)).card : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast unpaid_le_one hk hP
  have hm1 := mul_le_mul_of_nonneg_left hu hc0
  rw [← hKt] at ht
  rw [← hKh] at hh
  have hZ : (a : ℤ) * ((rowsP hP : ℕ) : ℤ) +
      ((gammaD k a b c : ℕ) : ℤ) * (((freeJunctions hP).card : ℕ) : ℤ) ≤
      (b : ℤ) * ((holesP hP : ℕ) : ℤ) +
        (c : ℤ) * (1 + ((heavyP hP : ℕ) : ℤ) + (((paidJunctions hP).card : ℕ) : ℤ)) := by
    linarith
  exact_mod_cast hZ

/-- **Proposition D3**, the line inequality (★★) with the holes eliminated. -/
theorem lineD_reduced (hk : 5 ≤ k) (hab : a ≤ b) (hline : ChainLine k a b c)
    (hclosed : c + 2 * a ≤ b * k) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    a * rowsP hP + gammaD k a b c * (freeJunctions hP).card +
        b * ((k - 1) * (k - 2).factorial) ≤
      b * ((k - 1) * rowsP hP) + c * (1 + heavyP hP + (paidJunctions hP).card) := by
  have h := lineD_reduced_holes hk hab hline hclosed hP hred
  have he := holes_eq hk hP
  rw [← he, Nat.mul_add]
  omega

end Path

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.junction_le_D
#print axioms SuperpermLowerBounds.holes_eq
#print axioms SuperpermLowerBounds.lineD_reduced_holes
#print axioms SuperpermLowerBounds.lineD_reduced

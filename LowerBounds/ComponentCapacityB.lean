import PreimageChain.ActualComponentCapacity
import LowerBounds.ChainCapacityB

/-!
# Capacity with slope `k - 3` for chains and components

`ChainCapacityB` proves the chain capacity from five facts about the profile of a chain.
Four of them are fields of `ExactWeightThreeChainLocalProfile` in the preimage-chain library.
The fifth, (G5), is the deficit-one lemma; here it is a hypothesis, `G5Statement k`.

Results, for `k ≥ 7` and a strongly exitless path `p`:

* `chain_capacity_B`: for every exact weight-three chain `Q` of `p`,
  `2 r(Q) ≤ (k-3) δ(Q) + price of the first piece + price of the last piece`;
* `component_capacity_B_cuts`:
  `2 r(p) ≤ (k-3) δ(p) + 2 (k-2) x⁺(p) + tailPrice p + headPrice p`, where `x⁺(p)` is the
  number of seams of weight at least 4 (`componentPositiveSeams p`);
* `component_capacity_B`: the same with the seam residual `x(p) ≥ x⁺(p)`.

The price of an end piece (`endPrice`) is `k - 2` if the piece is full, `1` if it has deficit 1
and is not the only piece, and `0` otherwise.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators

variable {k : ℕ} {p : HPath k}

/-- (G5): in the canonical decomposition of a chain, if a full piece stands directly before
partial piece `j`, partial piece `j` has deficit 1 and there is a partial piece `j + 1`, then
partial piece `j + 1` has deficit at least 2. -/
def G5Statement (k : ℕ) : Prop :=
  ∀ (p : HPath k), p.StronglyExitless → ∀ (chain : ExactWeightThreePieceChain p)
    (gaps : List (List (ComponentIntervalPiece p)))
    (partials : List (ComponentIntervalPiece p)),
    ExactPieceGapPartition chain.pieces gaps partials →
    ∀ j, j + 1 < partials.length →
      0 < natListAt 0 (gapLengths gaps) j →
      natListAt 1 (partialDeficits partials) j = 1 →
      2 ≤ natListAt 1 (partialDeficits partials) (j + 1)

/-! ### The price of an end piece -/

/-- Price of an end piece of deficit `dd` in a list of `r` pieces. -/
def endPrice (k dd r : ℕ) : ℕ :=
  if dd = 0 then k - 2 else if dd = 1 ∧ 2 ≤ r then 1 else 0

theorem endPrice_le (hk : 3 ≤ k) (dd r : ℕ) : endPrice k dd r ≤ k - 2 := by
  unfold endPrice
  split_ifs <;> omega

theorem endPrice_mono (k dd : ℕ) {r r' : ℕ} (h : r ≤ r') :
    endPrice k dd r ≤ endPrice k dd r' := by
  unfold endPrice
  split_ifs <;> omega

theorem endPrice_eq_zero_of_two_le {dd : ℕ} (k r : ℕ) (h : 2 ≤ dd) : endPrice k dd r = 0 := by
  unfold endPrice
  rw [if_neg (by omega), if_neg (by omega)]

theorem endPrice_eq_zero_of_single {dd r : ℕ} (k : ℕ) (h : dd ≠ 0) (hr : r ≤ 1) :
    endPrice k dd r = 0 := by
  unfold endPrice
  rw [if_neg h, if_neg (by omega)]

/-! ### Lists -/

section Lists

variable {α : Type*}

theorem le_sum_of_mem_nat (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · have := ih h'
      simp only [List.sum_cons]
      omega

theorem list_sum_capacity {ι : Type*} (c : ℕ) (items : List ι) (r δ e : ι → ℕ)
    (h : ∀ x ∈ items, 2 * r x ≤ c * δ x + e x) :
    2 * (items.map r).sum ≤ c * (items.map δ).sum + (items.map e).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.mul_add, Nat.mul_add]
    omega

theorem sum_map_le_mul_length (f : α → ℕ) (M : ℕ) (hf : ∀ x, f x ≤ M) (xs : List α) :
    (xs.map f).sum ≤ M * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have := hf x
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem sum_map_le_first (f : α → ℕ) (M : ℕ) (hf : ∀ x, f x ≤ M) (xs : List α) :
    (xs.map f).sum ≤ M * (xs.length - 1) + firstNatValue f xs := by
  cases xs with
  | nil => simp [firstNatValue]
  | cons x xs =>
    have h := sum_map_le_mul_length f M hf xs
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_sub_cancel,
      firstNatValue]
    omega

theorem sum_map_le_last (f : α → ℕ) (M : ℕ) (hf : ∀ x, f x ≤ M) (xs : List α) :
    (xs.map f).sum ≤ M * (xs.length - 1) + lastNatValue f xs := by
  have h := sum_map_le_first f M hf xs.reverse
  simpa [lastNatValue] using h

/-- Every item has two ends of price at most `M`; all ends but the two outer ones are bounded
by `M`. -/
theorem sum_two_ends_le (ff fl : α → ℕ) (M : ℕ) (hff : ∀ x, ff x ≤ M)
    (hfl : ∀ x, fl x ≤ M) (xs : List α) :
    (xs.map fun x => ff x + fl x).sum ≤
      2 * (M * (xs.length - 1)) + firstNatValue ff xs + lastNatValue fl xs := by
  have hsplit : (xs.map fun x => ff x + fl x).sum = (xs.map ff).sum + (xs.map fl).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega
  have h1 := sum_map_le_first ff M hff xs
  have h2 := sum_map_le_last fl M hfl xs
  rw [hsplit]
  omega

theorem firstNatValue_flatten_cons (f : α → ℕ) (G : List α) (rest : List (List α))
    (hG : G ≠ []) : firstNatValue f (G :: rest).flatten = firstNatValue f G := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hG
  simp [firstNatValue]

theorem lastNatValue_flatten_of_reverse_cons (f : α → ℕ) (groups : List (List α))
    (G : List α) (rest : List (List α)) (hG : G ≠ []) (hrev : groups.reverse = G :: rest) :
    lastNatValue f groups.flatten = lastNatValue f G := by
  unfold lastNatValue
  rw [reverse_flatten_piece_groups, hrev, List.map_cons]
  exact firstNatValue_flatten_cons f G.reverse _ (by simpa using hG)

/-- The last entry of a mapped list, read with a default. -/
theorem natListAt_map_last (fb : ℕ) (f : α → ℕ) (l : List α) (hl : l ≠ []) :
    natListAt fb (l.map f) (l.length - 1) = lastNatValue f l := by
  obtain ⟨xs, x, rfl⟩ : ∃ xs x, l = xs ++ [x] :=
    ⟨l.dropLast, l.getLast hl, (List.dropLast_append_getLast hl).symm⟩
  have hlen : (xs ++ [x]).length - 1 = (xs.map f).length := by simp
  unfold natListAt lastNatValue
  rw [hlen, List.map_append, List.getElem?_append_right (le_refl _)]
  simp [firstNatValue]

end Lists

/-! ### The ends of a decomposed chain -/

section Partition

variable {pieces : List (ComponentIntervalPiece p)}
  {gaps : List (List (ComponentIntervalPiece p))}
  {partials : List (ComponentIntervalPiece p)}

theorem partition_first_full (partition : ExactPieceGapPartition pieces gaps partials)
    (h : 0 < natListAt 0 (gapLengths gaps) 0) :
    firstNatValue ComponentIntervalPiece.deficit pieces = 0 := by
  cases partition with
  | nil => simp [gapLengths, natListAt] at h
  | full hzero rest => simpa [firstNatValue] using hzero
  | positive hpos rest => simp [gapLengths, natListAt] at h

theorem partition_first_partial (partition : ExactPieceGapPartition pieces gaps partials)
    (h0 : natListAt 0 (gapLengths gaps) 0 = 0) (hn : 0 < partials.length) :
    firstNatValue ComponentIntervalPiece.deficit pieces =
      natListAt 1 (partialDeficits partials) 0 := by
  cases partition with
  | nil => simp at hn
  | full hzero rest => simp [gapLengths, natListAt] at h0
  | positive hpos rest => simp [firstNatValue, partialDeficits, natListAt]

/-- The partial pieces are the pieces of positive deficit, in order. -/
theorem partition_partials_eq_filter
    (partition : ExactPieceGapPartition pieces gaps partials) :
    partials = pieces.filter (fun x => decide (1 ≤ x.deficit)) := by
  induction partition with
  | nil => rfl
  | full hzero rest ih =>
    rw [List.filter_cons_of_neg (by simp [hzero])]
    exact ih
  | positive hpos rest ih =>
    rw [List.filter_cons_of_pos (by simpa using hpos), ← ih]

theorem partition_lastFullBit (partition : ExactPieceGapPartition pieces gaps partials) :
    lastNatValue actualPieceFullBit pieces =
      positiveIndicator (natListAt 0 (gapLengths gaps) partials.length) := by
  have h := interleave_lastFullBit gaps partials partition.gaps_length
    partition.gaps_all_full partition.partials_positive
  rw [partition.interleave_eq] at h
  exact h

theorem partition_last_full (partition : ExactPieceGapPartition pieces gaps partials)
    (h : 0 < natListAt 0 (gapLengths gaps) partials.length) :
    lastNatValue ComponentIntervalPiece.deficit pieces = 0 := by
  have hbit := partition_lastFullBit partition
  unfold positiveIndicator at hbit
  rw [if_pos h] at hbit
  unfold lastNatValue at hbit ⊢
  cases hrev : pieces.reverse with
  | nil =>
    rw [hrev] at hbit
    simp [firstNatValue] at hbit
  | cons x xs =>
    rw [hrev] at hbit
    change actualPieceFullBit x = 1 at hbit
    change x.deficit = 0
    unfold actualPieceFullBit at hbit
    by_contra hne
    rw [if_neg hne] at hbit
    omega

theorem partition_last_partial (partition : ExactPieceGapPartition pieces gaps partials)
    (h0 : natListAt 0 (gapLengths gaps) partials.length = 0) (hn : 0 < partials.length) :
    lastNatValue ComponentIntervalPiece.deficit pieces =
      natListAt 1 (partialDeficits partials) (partials.length - 1) := by
  have hbit := partition_lastFullBit partition
  unfold positiveIndicator at hbit
  rw [if_neg (by omega)] at hbit
  have hfilter := partition_partials_eq_filter partition
  have hpartials : partials ≠ [] := List.ne_nil_of_length_pos hn
  have hlast : natListAt 1 (partialDeficits partials) (partials.length - 1) =
      lastNatValue ComponentIntervalPiece.deficit partials :=
    natListAt_map_last 1 ComponentIntervalPiece.deficit partials hpartials
  rw [hlast]
  unfold lastNatValue at hbit ⊢
  cases hrev : pieces.reverse with
  | nil =>
    exfalso
    apply hpartials
    have hp0 : pieces = [] := by simpa using hrev
    rw [hfilter, hp0]
    rfl
  | cons x xs =>
    rw [hrev] at hbit
    change actualPieceFullBit x = 0 at hbit
    have hx : 1 ≤ x.deficit := by
      unfold actualPieceFullBit at hbit
      by_contra hne
      rw [if_pos (by omega)] at hbit
      omega
    have hrevp : partials.reverse =
        x :: xs.filter (fun x => decide (1 ≤ x.deficit)) := by
      rw [hfilter, ← List.filter_reverse, hrev, List.filter_cons_of_pos (by simpa using hx)]
    rw [hrevp]
    rfl

end Partition

/-! ### Chain capacity -/

/-- Price of the first piece of a chain. -/
def chainFirstPrice (chain : ExactWeightThreePieceChain p) : ℕ :=
  endPrice k (firstNatValue ComponentIntervalPiece.deficit chain.pieces) chain.pieces.length

/-- Price of the last piece of a chain. -/
def chainLastPrice (chain : ExactWeightThreePieceChain p) : ℕ :=
  endPrice k (lastNatValue ComponentIntervalPiece.deficit chain.pieces) chain.pieces.length

/-- **Lemma C1″ for actual chains.** -/
theorem chain_capacity_B (hk : 7 ≤ k) (hG5 : G5Statement k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    2 * chain.pieces.length ≤ (k - 3) * pieceListTotalDeficit chain.pieces +
      (chainFirstPrice chain + chainLastPrice chain) := by
  classical
  obtain ⟨gaps, partials, partition⟩ := ExactPieceGapPartition.exists_for chain.pieces
  have hk5 : 5 ≤ k := by omega
  let witness : ExactPieceGapRunWitness partition :=
    partition.toRunWitness (by omega : 4 ≤ k) hp (leading_gap_length_le hk5 hp partition)
  let geometry : ExactPieceGapGeometry gaps partials := witness.toGeometry hk5 hp
  let profile : ExactWeightThreeChainLocalProfile chain := partition.toLocalProfile geometry
  have hdpos : ∀ j < partials.length, 1 ≤ natListAt 1 (partialDeficits partials) j :=
    profile.deficitPositive
  have G3 : ∀ j < partials.length, natListAt 1 (partialDeficits partials) j = 1 →
      natListAt 0 (gapLengths gaps) j = 0 ∨ natListAt 0 (gapLengths gaps) (j + 1) = 0 := by
    intro j hj hdj
    have h := geometry.unitOneSided j hj hdj
    unfold positiveIndicator at h
    split_ifs at h <;> omega
  have hr : chain.pieces.length = partials.length +
      ∑ i ∈ Finset.range (partials.length + 1), natListAt 0 (gapLengths gaps) i :=
    profile.pieceCount
  have hδ : pieceListTotalDeficit chain.pieces =
      ∑ j ∈ Finset.range partials.length, natListAt 1 (partialDeficits partials) j :=
    profile.totalDeficit
  have hcap := ChainB.chain_capacity_slope3 (k := k) (n := partials.length)
    (g := natListAt 0 (gapLengths gaps)) (d := natListAt 1 (partialDeficits partials))
    hk hdpos geometry.allFullBound geometry.partialGapBound G3
    geometry.internalLongThreshold (hG5 p hp chain gaps partials partition)
  have hsum1 : partials.length = 0 →
      ∑ i ∈ Finset.range (partials.length + 1), natListAt 0 (gapLengths gaps) i =
        natListAt 0 (gapLengths gaps) partials.length := by
    intro hz
    rw [hz]
    simp
  -- the first end
  have hF : ChainB.endFirst k partials.length (natListAt 0 (gapLengths gaps))
      (natListAt 1 (partialDeficits partials)) ≤ chainFirstPrice chain := by
    unfold ChainB.endFirst chainFirstPrice
    by_cases h0 : 0 < natListAt 0 (gapLengths gaps) 0
    · rw [if_pos h0, partition_first_full partition h0]
      unfold endPrice
      rw [if_pos rfl]
    · rw [if_neg h0]
      split_ifs with h1
      · have hnpos : 0 < partials.length := by
          by_contra hc
          have hz : partials.length = 0 := by omega
          have hs := hsum1 hz
          have hg : natListAt 0 (gapLengths gaps) partials.length =
              natListAt 0 (gapLengths gaps) 0 := by rw [hz]
          omega
        rw [partition_first_partial partition (by omega) hnpos]
        unfold endPrice
        rw [if_neg (by omega), if_pos ⟨h1.1, by omega⟩]
      · exact Nat.zero_le _
  -- the last end
  have hL : ChainB.endLast k partials.length (natListAt 0 (gapLengths gaps))
      (natListAt 1 (partialDeficits partials)) ≤ chainLastPrice chain := by
    unfold ChainB.endLast chainLastPrice
    by_cases h0 : 0 < natListAt 0 (gapLengths gaps) partials.length
    · rw [if_pos h0, partition_last_full partition h0]
      unfold endPrice
      rw [if_pos rfl]
    · rw [if_neg h0]
      split_ifs with h1
      · have hnpos : 0 < partials.length := by
          by_contra hc
          have hz : partials.length = 0 := by omega
          have hs := hsum1 hz
          omega
        rw [partition_last_partial partition (by omega) hnpos]
        unfold endPrice
        rw [if_neg (by omega), if_pos ⟨h1.1, by omega⟩]
      · exact Nat.zero_le _
  rw [hr, hδ]
  omega

/-! ### Component capacity -/

/-- Price of the first piece of a strongly exitless path. -/
noncomputable def tailPrice (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) : ℕ :=
  endPrice k (firstNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

/-- Price of the last piece of a strongly exitless path. -/
noncomputable def headPrice (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) : ℕ :=
  endPrice k (lastNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

theorem tailPrice_le (hk : 3 ≤ k) (hp : p.StronglyExitless) :
    tailPrice p (by omega) hp ≤ k - 2 := endPrice_le hk _ _

theorem headPrice_le (hk : 3 ≤ k) (hp : p.StronglyExitless) :
    headPrice p (by omega) hp ≤ k - 2 := endPrice_le hk _ _

theorem tailPrice_eq_zero_of_two_le (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (h : 2 ≤ firstNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp)) :
    tailPrice p hk hp = 0 := endPrice_eq_zero_of_two_le _ _ h

theorem headPrice_eq_zero_of_two_le (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (h : 2 ≤ lastNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp)) :
    headPrice p hk hp = 0 := endPrice_eq_zero_of_two_le _ _ h

/-- A path with a single piece that is not full has both end prices zero. -/
theorem prices_eq_zero_of_single (hk : 1 ≤ k) (hp : p.StronglyExitless)
    (hbit : componentFirstFullBit p hk hp = 0) (hr : componentPieceCount p = 1) :
    tailPrice p hk hp = 0 ∧ headPrice p hk hp = 0 := by
  have hlen : (componentIntervalPieces p hk hp).length = 1 := by
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
  unfold tailPrice headPrice
  rw [hx, hr]
  exact ⟨endPrice_eq_zero_of_single k hne (le_refl 1),
    endPrice_eq_zero_of_single k hne (le_refl 1)⟩

/-- **(CapB).** Capacity of a strongly exitless path with slope `k - 3`; every seam of weight
at least 4 costs `2 (k - 2)`. -/
theorem component_capacity_B_cuts (hk : 7 ≤ k) (hG5 : G5Statement k)
    (hp : p.StronglyExitless) :
    2 * componentPieceCount p ≤ (k - 3) * componentPieceDeficit p +
      2 * ((k - 2) * (componentPositiveSeams p).card) +
        tailPrice p (by omega) hp + headPrice p (by omega) hp := by
  classical
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by omega) hp
  have hlocal : ∀ chain ∈ chains, 2 * chain.pieces.length ≤
      (k - 3) * pieceListTotalDeficit chain.pieces +
        (chainFirstPrice chain + chainLastPrice chain) :=
    fun chain _ => chain_capacity_B hk hG5 hp chain
  have hsum := list_sum_capacity (k - 3) chains (fun chain => chain.pieces.length)
    (fun chain => pieceListTotalDeficit chain.pieces)
    (fun chain => chainFirstPrice chain + chainLastPrice chain) hlocal
  have hr := exactWeightThreeChainPartition_pieceCount_sum p (by omega) hp chains hflatten
  have hΔ := exactWeightThreeChainPartition_totalDeficit_sum (by omega : 4 ≤ k) hp chains
    hflatten
  rw [hr, hΔ] at hsum
  have hends := sum_two_ends_le (chainFirstPrice (p := p)) (chainLastPrice (p := p)) (k - 2)
    (fun _ => endPrice_le (by omega) _ _) (fun _ => endPrice_le (by omega) _ _) chains
  have hlenle : ∀ chain ∈ chains, chain.pieces.length ≤ componentPieceCount p := by
    intro chain hmem
    rw [← hr]
    exact le_sum_of_mem_nat _ _
      (List.mem_map_of_mem (f := fun chain : ExactWeightThreePieceChain p =>
        chain.pieces.length) hmem)
  -- the first piece of the first chain is the first piece of the path
  have hfirst : firstNatValue chainFirstPrice chains ≤ tailPrice p (by omega) hp := by
    unfold tailPrice
    rw [← hflatten]
    cases hch : chains with
    | nil => exact Nat.zero_le _
    | cons Q rest =>
      rw [List.map_cons, firstNatValue_flatten_cons _ _ _ Q.nonempty]
      exact endPrice_mono k _ (hlenle Q (by rw [hch]; exact List.mem_cons_self))
  -- the last piece of the last chain is the last piece of the path
  have hlast : lastNatValue chainLastPrice chains ≤ headPrice p (by omega) hp := by
    unfold headPrice
    rw [← hflatten]
    unfold lastNatValue
    cases hch : chains.reverse with
    | nil => exact Nat.zero_le _
    | cons Q rest =>
      have hQmem : Q ∈ chains := by
        have : Q ∈ chains.reverse := by rw [hch]; exact List.mem_cons_self
        simpa using this
      have hrev : (chains.map ExactWeightThreePieceChain.pieces).reverse =
          Q.pieces :: rest.map ExactWeightThreePieceChain.pieces := by
        rw [← List.map_reverse, hch, List.map_cons]
      have hflat := lastNatValue_flatten_of_reverse_cons ComponentIntervalPiece.deficit
        (chains.map ExactWeightThreePieceChain.pieces) Q.pieces _ Q.nonempty hrev
      unfold lastNatValue at hflat
      rw [hflat]
      exact endPrice_mono k _ (hlenle Q hQmem)
  have hmul : (k - 2) * (chains.length - 1) = (k - 2) * (componentPositiveSeams p).card := by
    rw [hlength, Nat.add_sub_cancel]
  omega

/-- (CapB) with the seam residual `x(p)` in place of the number of seams of weight at
least 4. -/
theorem component_capacity_B (hk : 7 ≤ k) (hG5 : G5Statement k) (hp : p.StronglyExitless) :
    2 * componentPieceCount p ≤ (k - 3) * componentPieceDeficit p +
      2 * ((k - 2) * componentSeamResidual p) +
        tailPrice p (by omega) hp + headPrice p (by omega) hp := by
  have h := component_capacity_B_cuts hk hG5 hp
  have hmul : (k - 2) * (componentPositiveSeams p).card ≤ (k - 2) * componentSeamResidual p :=
    Nat.mul_le_mul_left _ (componentPositiveSeams_card_le_residual (p := p))
  omega

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.chain_capacity_B
#print axioms SuperpermLowerBounds.component_capacity_B_cuts
#print axioms SuperpermLowerBounds.component_capacity_B

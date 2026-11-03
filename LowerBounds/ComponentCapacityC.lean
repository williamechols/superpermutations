import PreimageChain.ActualComponentCapacity
import LowerBounds.ChainCapacityC
import LowerBounds.ComponentCapacityB
import LowerBounds.DeficitOne

/-!
# Capacity for Theorem C: chains and components

The one unproved input of Theorem C is `HStatement k cn bn q`: every *window* (an exact
weight-three chain of a strongly exitless path that starts and ends with a partial piece and
all of whose intervals contain a piece of deficit at least 2) satisfies

  `2 r + 2 (k - 4) + c δ ≤ (k - 3) δ + b`,   `c = cn / q`, `b = bn / q`,

`r` its number of pieces and `δ` its total deficit.

From it, for `k ≥ 5` and `cn ≤ q (k - 5)`, this file proves

* `chain_capacity_C`: for every exact weight-three chain `Q` of a strongly exitless path,
  `4 q r(Q) ≤ 2 (q (k - 3) - cn) δ(Q) + price of the first piece + price of the last piece`;
* `component_capacity_C_cuts`, `component_capacity_C`: for a strongly exitless path `p`,
  `4 q r(p) ≤ 2 (q (k - 3) - cn) δ(p) + 2 (2 q (k - 2) + bn) x(p) + tailPriceC + headPriceC`.

The geometry used: a run of full pieces of a chain has at most `k - 2` pieces, and at most
`k - 3` if a partial piece of the chain stands next to it (two fields of the chain profile of
the preimage-chain library, applied to a part of the chain), and the deficit-one lemma.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators

variable {k : ℕ} {p : HPath k}

/-! ### The hypothesis -/

/-- `H(k; c, b)` with `c = cn / q`, `b = bn / q`: every window satisfies
`slack_int(w) ≥ c δ(w) - b`. -/
def HStatement (k cn bn q : ℕ) : Prop :=
  ∀ (p : HPath k), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
    ChainC.IsWindow (chain.pieces.map ComponentIntervalPiece.deficit) →
    ChainC.WindowBound k cn bn q (chain.pieces.map ComponentIntervalPiece.deficit)

/-- The same with `s̃(w) = slack_int(w) - 2 χ(w)` in place of `slack_int(w)`: the stronger
statement. -/
def HStatementTilde (k cn bn q : ℕ) : Prop :=
  ∀ (p : HPath k), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
    ChainC.IsWindow (chain.pieces.map ComponentIntervalPiece.deficit) →
    ChainC.WindowBoundTilde k cn bn q (chain.pieces.map ComponentIntervalPiece.deficit)

theorem hStatement_of_tilde {cn bn q : ℕ} (h : HStatementTilde k cn bn q) :
    HStatement k cn bn q :=
  fun p hp chain hw => ChainC.windowBound_of_tilde (h p hp chain hw)

/-! ### Parts of a chain -/

theorem adjacent_suffix {α : Type} {R : α → α → Prop} (L1 : List α) {rest : List α}
    (h : AdjacentList R (L1 ++ rest)) : AdjacentList R rest := by
  induction L1 with
  | nil => exact h
  | cons x L1 ih => exact ih (AdjacentList.tail h)

theorem adjacent_prefix {α : Type} {R : α → α → Prop} :
    ∀ (W L2 : List α), AdjacentList R (W ++ L2) → AdjacentList R W
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: W, L2, h => by
    have h' : R x y ∧ AdjacentList R ((y :: W) ++ L2) := h
    exact ⟨h'.1, adjacent_prefix (y :: W) L2 h'.2⟩

theorem adjacent_infix (chain : ExactWeightThreePieceChain p)
    {L1 W L2 : List (ComponentIntervalPiece p)} (h : chain.pieces = L1 ++ W ++ L2) :
    AdjacentList PieceExactJoin W := by
  have hadj := exactWeightThreeChain_adjacent chain
  rw [h, List.append_assoc] at hadj
  exact adjacent_prefix W L2 (adjacent_suffix L1 hadj)

/-- A non-empty contiguous part of the piece list of a chain is the piece list of a chain. -/
def subchain (chain : ExactWeightThreePieceChain p)
    (L1 W L2 : List (ComponentIntervalPiece p)) (h : chain.pieces = L1 ++ W ++ L2)
    (hW : W ≠ []) : ExactWeightThreePieceChain p where
  pieces := W
  nonempty := hW
  consecutive := fun i hi => (AdjacentList.get (adjacent_infix chain h) i hi).1
  seamWeight := fun i hi => (AdjacentList.get (adjacent_infix chain h) i hi).2

@[simp] theorem subchain_pieces (chain : ExactWeightThreePieceChain p)
    (L1 W L2 : List (ComponentIntervalPiece p)) (h : chain.pieces = L1 ++ W ++ L2)
    (hW : W ≠ []) : (subchain chain L1 W L2 h hW).pieces = W := rfl

/-! ### The decompositions of three simple lists of pieces -/

theorem full_partition (R : List (ComponentIntervalPiece p))
    (h : ∀ x ∈ R, x.deficit = 0) : ExactPieceGapPartition R [R] [] := by
  induction R with
  | nil => exact .nil
  | cons x xs ih =>
    exact .full (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem full_then_partial_partition (R : List (ComponentIntervalPiece p))
    (h : ∀ x ∈ R, x.deficit = 0) (y : ComponentIntervalPiece p) (hy : 1 ≤ y.deficit) :
    ExactPieceGapPartition (R ++ [y]) [R, []] [y] := by
  induction R with
  | nil => exact .positive hy .nil
  | cons x xs ih =>
    exact .full (h x List.mem_cons_self) (ih (fun u hu => h u (List.mem_cons_of_mem x hu)))

theorem partial_then_full_partition (y : ComponentIntervalPiece p) (hy : 1 ≤ y.deficit)
    (R : List (ComponentIntervalPiece p)) (h : ∀ x ∈ R, x.deficit = 0) :
    ExactPieceGapPartition (y :: R) [[], R] [y] :=
  .positive hy (full_partition R h)

/-! ### The three facts about the deficits of a chain -/

/-- A run of full pieces of a chain has at most `k - 2` pieces. -/
theorem chain_run_le (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ∀ L1 R L2 : List ℕ, chain.pieces.map ComponentIntervalPiece.deficit = L1 ++ R ++ L2 →
      (∀ u ∈ R, u = 0) → R.length ≤ k - 2 := by
  intro L1 R L2 hD hR
  obtain ⟨P12, P3, hpieces, hP12, -⟩ := List.map_eq_append_iff.mp hD
  obtain ⟨P1, PR, rfl, -, hPR⟩ := List.map_eq_append_iff.mp hP12
  have hlen : R.length = PR.length := by rw [← hPR, List.length_map]
  by_cases hne : PR = []
  · rw [hlen, hne]
    exact Nat.zero_le _
  · have hzero : ∀ x ∈ PR, x.deficit = 0 := fun x hx =>
      hR _ (by rw [← hPR]; exact List.mem_map_of_mem hx)
    have partition : ExactPieceGapPartition (subchain chain P1 PR P3 hpieces hne).pieces
        [PR] [] := full_partition PR hzero
    have geometry : ExactPieceGapGeometry [PR] [] :=
      (partition.toRunWitness (by omega : 4 ≤ k) hp
        (leading_gap_length_le hk hp partition)).toGeometry hk hp
    have h := geometry.allFullBound rfl
    rw [hlen]
    simpa [gapLengths] using h

/-- A run of full pieces followed by a partial piece has at most `k - 3` pieces. -/
theorem chain_run_right_le (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ∀ (L1 R : List ℕ) (z : ℕ) (L2 : List ℕ),
      chain.pieces.map ComponentIntervalPiece.deficit = L1 ++ R ++ z :: L2 →
      (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3 := by
  intro L1 R z L2 hD hR hz
  obtain ⟨P12, Pz2, hpieces, hP12, hPz2⟩ := List.map_eq_append_iff.mp hD
  obtain ⟨P1, PR, rfl, -, hPR⟩ := List.map_eq_append_iff.mp hP12
  obtain ⟨pz, P2, rfl, hpz, -⟩ := List.map_eq_cons_iff.mp hPz2
  have hlen : R.length = PR.length := by rw [← hPR, List.length_map]
  have hzero : ∀ x ∈ PR, x.deficit = 0 := fun x hx =>
    hR _ (by rw [← hPR]; exact List.mem_map_of_mem hx)
  have hpieces' : chain.pieces = P1 ++ (PR ++ [pz]) ++ P2 := by
    rw [hpieces]
    simp
  have partition : ExactPieceGapPartition
      (subchain chain P1 (PR ++ [pz]) P2 hpieces' (by simp)).pieces [PR, []] [pz] :=
    full_then_partial_partition PR hzero pz (by omega)
  have geometry : ExactPieceGapGeometry [PR, []] [pz] :=
    (partition.toRunWitness (by omega : 4 ≤ k) hp
      (leading_gap_length_le hk hp partition)).toGeometry hk hp
  have h := geometry.partialGapBound (by simp) 0 (by simp)
  rw [hlen]
  simpa [gapLengths] using h

/-- A run of full pieces preceded by a partial piece has at most `k - 3` pieces. -/
theorem chain_run_left_le (hk : 5 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ∀ (L1 : List ℕ) (z : ℕ) (R L2 : List ℕ),
      chain.pieces.map ComponentIntervalPiece.deficit = L1 ++ z :: R ++ L2 →
      (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3 := by
  intro L1 z R L2 hD hR hz
  obtain ⟨P1R, P2, hpieces, hP1R, -⟩ := List.map_eq_append_iff.mp hD
  obtain ⟨P1, PzR, rfl, -, hPzR⟩ := List.map_eq_append_iff.mp hP1R
  obtain ⟨pz, PR, rfl, hpz, hPR⟩ := List.map_eq_cons_iff.mp hPzR
  have hlen : R.length = PR.length := by rw [← hPR, List.length_map]
  have hzero : ∀ x ∈ PR, x.deficit = 0 := fun x hx =>
    hR _ (by rw [← hPR]; exact List.mem_map_of_mem hx)
  have partition : ExactPieceGapPartition
      (subchain chain P1 (pz :: PR) P2 hpieces (by simp)).pieces [[], PR] [pz] :=
    partial_then_full_partition pz (by omega) PR hzero
  have geometry : ExactPieceGapGeometry [[], PR] [pz] :=
    (partition.toRunWitness (by omega : 4 ≤ k) hp
      (leading_gap_length_le hk hp partition)).toGeometry hk hp
  have h := geometry.partialGapBound (by simp) 1 (by simp)
  rw [hlen]
  simpa [gapLengths] using h

/-- The deficit-one lemma for the list of deficits of a chain. -/
theorem chain_unitRule (hk : 4 ≤ k) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    ChainC.UnitRule (chain.pieces.map ComponentIntervalPiece.deficit) := by
  intro L1 L2 z hD
  obtain ⟨P1, Prest, hpieces, -, hrest⟩ := List.map_eq_append_iff.mp hD
  obtain ⟨px, Prest1, rfl, hx, hrest1⟩ := List.map_eq_cons_iff.mp hrest
  obtain ⟨py, Prest2, rfl, hy, hrest2⟩ := List.map_eq_cons_iff.mp hrest1
  obtain ⟨pz, P2, rfl, hz, -⟩ := List.map_eq_cons_iff.mp hrest2
  have hadj := exactWeightThreeChain_adjacent chain
  rw [hpieces] at hadj
  have hadj' : AdjacentList PieceExactJoin (px :: py :: pz :: P2) := adjacent_suffix P1 hadj
  have hxy : PieceExactJoin px py := hadj'.1
  have hyz : PieceExactJoin py pz := hadj'.2.1
  rw [← hz]
  exact actualPiece_after_full_unit_deficit_ge_two hk hp px.valid py.valid pz.valid hx hy
    hxy.1 hyz.1 hxy.2 hyz.2

/-! ### Chain capacity -/

/-- Price of the first piece of a chain. -/
def chainFirstPriceC (cn bn q : ℕ) (chain : ExactWeightThreePieceChain p) : ℤ :=
  ChainC.priceC k cn bn q (firstNatValue ComponentIntervalPiece.deficit chain.pieces)
    chain.pieces.length

/-- Price of the last piece of a chain. -/
def chainLastPriceC (cn bn q : ℕ) (chain : ExactWeightThreePieceChain p) : ℤ :=
  ChainC.priceC k cn bn q (lastNatValue ComponentIntervalPiece.deficit chain.pieces)
    chain.pieces.length

/-- **(C-chain) for actual chains, multiplied by `2 q`.** -/
theorem chain_capacity_C {cn bn q : ℕ} (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    (hH : HStatement k cn bn q) (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    4 * (q : ℤ) * (chain.pieces.length : ℤ) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * ((pieceListTotalDeficit chain.pieces : ℕ) : ℤ) +
        (chainFirstPriceC cn bn q chain + chainLastPriceC cn bn q chain) := by
  have hx : ∃ t, chain.pieces.map ComponentIntervalPiece.deficit =
      firstNatValue ComponentIntervalPiece.deficit chain.pieces :: t := by
    obtain ⟨px, rest, hpieces⟩ := List.exists_cons_of_ne_nil chain.nonempty
    rw [hpieces]
    exact ⟨rest.map ComponentIntervalPiece.deficit, rfl⟩
  have hy : ∃ t, chain.pieces.map ComponentIntervalPiece.deficit =
      t ++ [lastNatValue ComponentIntervalPiece.deficit chain.pieces] := by
    have hrevne : chain.pieces.reverse ≠ [] := by simpa using chain.nonempty
    obtain ⟨py, rest, hrev⟩ := List.exists_cons_of_ne_nil hrevne
    have hpieces : chain.pieces = rest.reverse ++ [py] := by
      have h' := congrArg List.reverse hrev
      simpa using h'
    refine ⟨rest.reverse.map ComponentIntervalPiece.deficit, ?_⟩
    unfold lastNatValue
    rw [hrev]
    rw [hpieces]
    simp [firstNatValue]
  have hW : ∀ L1 W L2 : List ℕ,
      chain.pieces.map ComponentIntervalPiece.deficit = L1 ++ W ++ L2 → ChainC.IsWindow W →
      ChainC.WindowBound k cn bn q W := by
    intro L1 W L2 hD hwin
    obtain ⟨P12, P3, hpieces, hP12, -⟩ := List.map_eq_append_iff.mp hD
    obtain ⟨P1, PW, rfl, -, hPW⟩ := List.map_eq_append_iff.mp hP12
    have hne : PW ≠ [] := by
      rintro rfl
      obtain ⟨x, rest, hWx, -⟩ := hwin.first_partial
      rw [hWx] at hPW
      simp at hPW
    have h := hH p hp (subchain chain P1 PW P3 hpieces hne)
    rw [subchain_pieces, hPW] at h
    exact h hwin
  have h := ChainC.chain_capacity_list (bn := bn) hk hc hx hy (chain_run_le hk hp chain)
    (chain_run_right_le hk hp chain) (chain_run_left_le hk hp chain)
    (chain_unitRule (by omega) hp chain) hW
  rw [List.length_map] at h
  unfold chainFirstPriceC chainLastPriceC pieceListTotalDeficit
  linarith

/-! ### Sums over lists, with integer values -/

section Lists

variable {α : Type*}

/-- Value at the first entry of a list; `0` for the empty list. -/
def firstZ (f : α → ℤ) : List α → ℤ
  | [] => 0
  | x :: _ => f x

/-- Value at the last entry of a list; `0` for the empty list. -/
def lastZ (f : α → ℤ) (xs : List α) : ℤ := firstZ f xs.reverse

theorem list_sum_capacity_int (a c : ℤ) (items : List α) (r δ : α → ℕ) (e : α → ℤ)
    (h : ∀ x ∈ items, a * ((r x : ℕ) : ℤ) ≤ c * ((δ x : ℕ) : ℤ) + e x) :
    a * (((items.map r).sum : ℕ) : ℤ) ≤
      c * (((items.map δ).sum : ℕ) : ℤ) + (items.map e).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add]
    linarith

theorem sum_map_le_mul_length_int (f : α → ℤ) (M : ℤ) (hf : ∀ x, f x ≤ M) (xs : List α) :
    (xs.map f).sum ≤ M * (xs.length : ℤ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h1 := hf x
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    rw [mul_add, mul_one]
    linarith

theorem sum_map_le_first_int (f : α → ℤ) (M : ℤ) (hf : ∀ x, f x ≤ M) (xs : List α)
    (hne : xs ≠ []) : (xs.map f).sum + M ≤ M * (xs.length : ℤ) + firstZ f xs := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h := sum_map_le_mul_length_int f M hf t
  simp only [List.map_cons, List.sum_cons, List.length_cons, firstZ]
  push_cast
  rw [mul_add, mul_one]
  linarith

theorem sum_map_le_last_int (f : α → ℤ) (M : ℤ) (hf : ∀ x, f x ≤ M) (xs : List α)
    (hne : xs ≠ []) : (xs.map f).sum + M ≤ M * (xs.length : ℤ) + lastZ f xs := by
  have h := sum_map_le_first_int f M hf xs.reverse (by simpa using hne)
  rw [List.map_reverse, List.sum_reverse, List.length_reverse] at h
  exact h

/-- Every item has two ends of price at most `M`; all ends but the two outer ones are bounded
by `M`. -/
theorem sum_two_ends_le_int (ff fl : α → ℤ) (M : ℤ) (hff : ∀ x, ff x ≤ M)
    (hfl : ∀ x, fl x ≤ M) (xs : List α) (hne : xs ≠ []) :
    (xs.map fun x => ff x + fl x).sum + 2 * M ≤
      2 * (M * (xs.length : ℤ)) + firstZ ff xs + lastZ fl xs := by
  have hsplit : (xs.map fun x => ff x + fl x).sum = (xs.map ff).sum + (xs.map fl).sum := by
    clear hne
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  have h1 := sum_map_le_first_int ff M hff xs hne
  have h2 := sum_map_le_last_int fl M hfl xs hne
  rw [hsplit]
  linarith

end Lists

/-! ### Component capacity -/

/-- Price of the first piece of a strongly exitless path. -/
noncomputable def tailPriceC (cn bn q : ℕ) (p : HPath k) (hk : 1 ≤ k)
    (hp : p.StronglyExitless) : ℤ :=
  ChainC.priceC k cn bn q
    (firstNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

/-- Price of the last piece of a strongly exitless path. -/
noncomputable def headPriceC (cn bn q : ℕ) (p : HPath k) (hk : 1 ≤ k)
    (hp : p.StronglyExitless) : ℤ :=
  ChainC.priceC k cn bn q
    (lastNatValue ComponentIntervalPiece.deficit (componentIntervalPieces p hk hp))
    (componentPieceCount p)

/-- **Component capacity for Theorem C**, multiplied by `2 q`; every seam of weight at least 4
costs two full ends. -/
theorem component_capacity_C_cuts {cn bn q : ℕ} (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    (hH : HStatement k cn bn q) (hp : p.StronglyExitless) :
    4 * (q : ℤ) * (componentPieceCount p : ℤ) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (componentPieceDeficit p : ℤ) +
        2 * ((2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) *
          ((componentPositiveSeams p).card : ℤ)) +
        tailPriceC cn bn q p (by omega) hp + headPriceC cn bn q p (by omega) hp := by
  classical
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by omega) hp
  have hne : chains ≠ [] := by
    intro h
    rw [h] at hlength
    simp at hlength
  have hlocal : ∀ chain ∈ chains,
      4 * (q : ℤ) * ((chain.pieces.length : ℕ) : ℤ) ≤
        2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) *
            ((pieceListTotalDeficit chain.pieces : ℕ) : ℤ) +
          (chainFirstPriceC cn bn q chain + chainLastPriceC cn bn q chain) :=
    fun chain _ => chain_capacity_C hk hc hH hp chain
  have hsum := list_sum_capacity_int (4 * (q : ℤ))
    (2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ))) chains
    (fun chain => chain.pieces.length)
    (fun chain => pieceListTotalDeficit chain.pieces)
    (fun chain => chainFirstPriceC cn bn q chain + chainLastPriceC cn bn q chain) hlocal
  have hr := exactWeightThreeChainPartition_pieceCount_sum p (by omega) hp chains hflatten
  have hΔ := exactWeightThreeChainPartition_totalDeficit_sum (by omega : 4 ≤ k) hp chains
    hflatten
  rw [hr, hΔ] at hsum
  have hends := sum_two_ends_le_int (chainFirstPriceC (p := p) cn bn q)
    (chainLastPriceC (p := p) cn bn q) (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ))
    (fun _ => ChainC.priceC_le hk hc _ _) (fun _ => ChainC.priceC_le hk hc _ _) chains hne
  have hlenle : ∀ chain ∈ chains, chain.pieces.length ≤ componentPieceCount p := by
    intro chain hmem
    rw [← hr]
    exact le_sum_of_mem_nat _ _
      (List.mem_map_of_mem (f := fun chain : ExactWeightThreePieceChain p =>
        chain.pieces.length) hmem)
  -- the first piece of the first chain is the first piece of the path
  have hfirst : firstZ (chainFirstPriceC cn bn q) chains ≤ tailPriceC cn bn q p (by omega) hp := by
    unfold tailPriceC
    rw [← hflatten]
    cases hch : chains with
    | nil => exact absurd hch hne
    | cons Q rest =>
      rw [List.map_cons, firstNatValue_flatten_cons _ _ _ Q.nonempty]
      exact ChainC.priceC_mono _ (hlenle Q (by rw [hch]; exact List.mem_cons_self))
  -- the last piece of the last chain is the last piece of the path
  have hlast : lastZ (chainLastPriceC cn bn q) chains ≤ headPriceC cn bn q p (by omega) hp := by
    unfold headPriceC
    rw [← hflatten]
    unfold lastZ
    cases hch : chains.reverse with
    | nil =>
      exfalso
      apply hne
      simpa using hch
    | cons Q rest =>
      have hQmem : Q ∈ chains := by
        have : Q ∈ chains.reverse := by rw [hch]; exact List.mem_cons_self
        simpa using this
      have hrev : (chains.map ExactWeightThreePieceChain.pieces).reverse =
          Q.pieces :: rest.map ExactWeightThreePieceChain.pieces := by
        rw [← List.map_reverse, hch, List.map_cons]
      have hflat := lastNatValue_flatten_of_reverse_cons ComponentIntervalPiece.deficit
        (chains.map ExactWeightThreePieceChain.pieces) Q.pieces _ Q.nonempty hrev
      rw [hflat]
      exact ChainC.priceC_mono _ (hlenle Q hQmem)
  have hlenZ : ((chains.length : ℕ) : ℤ) = ((componentPositiveSeams p).card : ℤ) + 1 := by
    rw [hlength]
    push_cast
    ring
  rw [hlenZ] at hends
  linarith

/-- The same with the seam residual `x(p)` in place of the number of seams of weight at
least 4. -/
theorem component_capacity_C {cn bn q : ℕ} (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    (hH : HStatement k cn bn q) (hp : p.StronglyExitless) :
    4 * (q : ℤ) * (componentPieceCount p : ℤ) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (componentPieceDeficit p : ℤ) +
        2 * ((2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) * (componentSeamResidual p : ℤ)) +
        tailPriceC cn bn q p (by omega) hp + headPriceC cn bn q p (by omega) hp := by
  have h := component_capacity_C_cuts (bn := bn) hk hc hH hp
  have hle : ((componentPositiveSeams p).card : ℤ) ≤ (componentSeamResidual p : ℤ) := by
    exact_mod_cast componentPositiveSeams_card_le_residual (p := p)
  have hM : (0 : ℤ) ≤ 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) := by
    have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
    have hb : (0 : ℤ) ≤ (bn : ℤ) := Int.natCast_nonneg _
    have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hle hM
  linarith

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.chain_unitRule
#print axioms SuperpermLowerBounds.chain_capacity_C
#print axioms SuperpermLowerBounds.component_capacity_C_cuts
#print axioms SuperpermLowerBounds.component_capacity_C

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Chain capacity with slope `k - 3`: the arithmetic

A chain of pieces is described by its profile: `n` partial pieces with deficits
`d 0, …, d (n-1) ≥ 1`, and the numbers `g 0, …, g n` of full pieces before, between and
after them.  The chain has `r = n + Σ g i` pieces and total deficit `δ = Σ d j`.

From the five local facts

* (G1) `n = 0 → g 0 ≤ k - 2`,
* (G2) `0 < n → g i ≤ k - 3`,
* (G3) a partial piece of deficit 1 has a full piece on at most one side,
* (G4) an internal gap of length `k - 3` has `d (i-1) + d i ≥ k - 1`,
* (G5) full piece, then deficit 1, then a partial piece: that piece has deficit `≥ 2`,

this file proves, for `k ≥ 7`,

  `2 r ≤ (k - 3) δ + endFirst + endLast`,

where an end of the chain costs `k - 2` if its piece is full, `1` if its piece has deficit 1
and the chain has a full piece somewhere, and `0` otherwise.

No geometry and no permutations here: only natural numbers and finite sums.
-/

namespace SuperpermLowerBounds

open scoped BigOperators

namespace ChainB

/-! ### Sums over `range` with shifted indices -/

theorem sum_range_succ_pred (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n + 1), (if 1 ≤ i then f (i - 1) else 0) =
      ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_range_succ']
  simp

theorem sum_range_succ_lt (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n + 1), (if i < n then f i else 0) =
      ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_range_succ, if_neg (lt_irrefl n), add_zero]
  exact Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))

theorem sum_pred_eq_sum_succ (n : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range n, (if 1 ≤ j then f (j - 1) else 0) =
      ∑ j ∈ Finset.range n, (if j + 1 < n then f j else 0) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ_pred m f]
    have h : ∑ j ∈ Finset.range (m + 1), (if j + 1 < m + 1 then f j else 0) =
        ∑ j ∈ Finset.range (m + 1), (if j < m then f j else 0) :=
      Finset.sum_congr rfl (fun j _ => by
        by_cases hj : j < m
        · rw [if_pos hj, if_pos (by omega)]
        · rw [if_neg hj, if_neg (by omega)])
    rw [h, sum_range_succ_lt m f]

theorem sum_range_single (n a c : ℕ) (ha : a < n) :
    ∑ j ∈ Finset.range n, (if j = a then c else 0) = c := by
  rw [Finset.sum_ite_eq' (Finset.range n) a (fun _ => c), if_pos (Finset.mem_range.mpr ha)]

theorem sum_range_const (n c : ℕ) : ∑ _j ∈ Finset.range n, c = n * c := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.succ_mul]

/-! ### The local quantities -/

variable (k n : ℕ) (g d : ℕ → ℕ)

/-- `k - 4` for a gap that is not empty. -/
def gapNeed (x : ℕ) : ℕ := if 0 < x then k - 4 else 0

/-- Gap `j` is internal, of length `k - 3`, and charged to the partial piece on its right. -/
def chargeL (j : ℕ) : ℕ :=
  if (1 ≤ j ∧ j < n ∧ g j = k - 3) ∧ d (j - 1) < 3 then 1 else 0

/-- Gap `j + 1` is internal, of length `k - 3`, and charged to the partial piece on its
left. -/
def chargeR (j : ℕ) : ℕ :=
  if (j + 1 < n ∧ g (j + 1) = k - 3) ∧ 3 ≤ d j then 1 else 0

/-- What partial piece `j` owes for the gap before it. -/
def needL (j : ℕ) : ℕ := gapNeed k (g j) + 2 * chargeL k n g d j

/-- What partial piece `j` owes for the gap after it. -/
def needR (j : ℕ) : ℕ := gapNeed k (g (j + 1)) + 2 * chargeR k n g d j

/-- Partial piece `j` has a full piece before it and deficit 1: it takes one unit from
partial piece `j + 1`. -/
def flowL (j : ℕ) : ℕ := if 0 < g j ∧ d j = 1 then 1 else 0

/-- Partial piece `j + 1` has a full piece after it, none before it, and deficit 1: it takes
one unit from partial piece `j`. -/
def flowR (j : ℕ) : ℕ := if g (j + 1) = 0 ∧ 0 < g (j + 2) ∧ d (j + 1) = 1 then 1 else 0

/-- The chain starts with a partial piece of deficit 1. -/
def bonusFirst : ℕ := if g 0 = 0 ∧ d 0 = 1 then 1 else 0

/-- The chain ends with a partial piece of deficit 1. -/
def bonusLast : ℕ := if g n = 0 ∧ d (n - 1) = 1 then 1 else 0

/-- Price of the first end of the chain. -/
def endFirst : ℕ :=
  if 0 < g 0 then k - 2
  else if d 0 = 1 ∧ 0 < ∑ i ∈ Finset.range (n + 1), g i then 1 else 0

/-- Price of the last end of the chain. -/
def endLast : ℕ :=
  if 0 < g n then k - 2
  else if d (n - 1) = 1 ∧ 0 < ∑ i ∈ Finset.range (n + 1), g i then 1 else 0

variable {k n g d}

theorem endFirst_le (hk : 3 ≤ k) : endFirst k n g d ≤ k - 2 := by
  unfold endFirst
  split_ifs <;> omega

theorem endLast_le (hk : 3 ≤ k) : endLast k n g d ≤ k - 2 := by
  unfold endLast
  split_ifs <;> omega

/-- An internal gap of length `k - 3` is charged to one of its two neighbours. -/
theorem charge_long (m : ℕ) (h1 : m + 1 < n) (h2 : g (m + 1) = k - 3) :
    1 ≤ chargeL k n g d (m + 1) + chargeR k n g d m := by
  by_cases h : d m < 3
  · have hc : chargeL k n g d (m + 1) = 1 := by
      unfold chargeL
      rw [if_pos]
      refine ⟨⟨by omega, h1, h2⟩, ?_⟩
      simpa using h
    omega
  · have hc : chargeR k n g d m = 1 := by
      unfold chargeR
      rw [if_pos]
      exact ⟨⟨h1, h2⟩, by omega⟩
    omega

/-- The local inequality (LI) of the written proof: what partial piece `j` has, with what it
receives, covers what it owes and what it gives. -/
theorem local_ineq (hk : 7 ≤ k)
    (hd : ∀ j < n, 1 ≤ d j)
    (G3 : ∀ j < n, d j = 1 → g j = 0 ∨ g (j + 1) = 0)
    (G4 : ∀ i, 1 ≤ i → i < n → g i = k - 3 → k - 1 ≤ d (i - 1) + d i)
    (G5 : ∀ j, j + 1 < n → 0 < g j → d j = 1 → 2 ≤ d (j + 1))
    (j : ℕ) (hj : j < n) :
    needL k n g d j + needR k n g d j +
        (if 1 ≤ j then flowL g d (j - 1) else 0) +
        (if j + 1 < n then flowR g d j else 0) + 2 ≤
      (k - 3) * d j + (if j + 1 < n then flowL g d j else 0) +
        (if 1 ≤ j then flowR g d (j - 1) else 0) +
        (if j = 0 then bonusFirst g d else 0) +
        (if j = n - 1 then bonusLast n g d else 0) := by
  have hdj := hd j hj
  have h3 := G3 j hj
  -- the two long-gap charges
  have hcl : chargeL k n g d j = 0 ∨ (chargeL k n g d j = 1 ∧ 0 < g j ∧ 3 ≤ d j) := by
    unfold chargeL
    split_ifs with h
    · right
      have h4 := G4 j h.1.1 h.1.2.1 h.1.2.2
      have h5 := h.2
      have h6 := h.1.2.2
      refine ⟨rfl, ?_, ?_⟩ <;> omega
    · left
      rfl
  have hcr : chargeR k n g d j = 0 ∨ (chargeR k n g d j = 1 ∧ 0 < g (j + 1) ∧ 3 ≤ d j) := by
    unfold chargeR
    split_ifs with h
    · right
      have h6 := h.1.2
      refine ⟨rfl, ?_, h.2⟩
      omega
    · left
      rfl
  -- what `j` gives to its left neighbour
  have hgl : (if 1 ≤ j then flowL g d (j - 1) else 0) = 0 ∨
      ((if 1 ≤ j then flowL g d (j - 1) else 0) = 1 ∧ g j = 0 ∧ 2 ≤ d j) := by
    by_cases h1 : 1 ≤ j
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [if_pos h1, Nat.add_sub_cancel]
      unfold flowL
      split_ifs with h
      · right
        have ha := G3 m (by omega) h.2
        have hb := G5 m hj h.1 h.2
        have hc := h.1
        refine ⟨rfl, ?_, hb⟩
        omega
      · left
        rfl
    · left
      rw [if_neg h1]
  -- what `j` gives to its right neighbour
  have hgr : (if j + 1 < n then flowR g d j else 0) = 0 ∨
      ((if j + 1 < n then flowR g d j else 0) = 1 ∧ g (j + 1) = 0 ∧ (g j = 0 ∨ 2 ≤ d j)) := by
    by_cases h1 : j + 1 < n
    · rw [if_pos h1]
      unfold flowR
      split_ifs with h
      · right
        refine ⟨rfl, h.1, ?_⟩
        by_contra hcon
        have hb := G5 j h1 (by omega) (by omega)
        have hc := h.2.2
        omega
      · left
        rfl
    · left
      rw [if_neg h1]
  -- a piece of deficit 1 after a full piece receives one unit
  have hrl : 0 < g j → d j = 1 →
      1 ≤ (if j + 1 < n then flowL g d j else 0) +
        (if j = n - 1 then bonusLast n g d else 0) := by
    intro hg hdj1
    by_cases h1 : j + 1 < n
    · have hf : flowL g d j = 1 := by
        unfold flowL
        rw [if_pos ⟨hg, hdj1⟩]
      rw [if_pos h1, hf]
      omega
    · have hjn : j = n - 1 := by omega
      have hgn : g n = 0 := by
        have hnj : n = j + 1 := by omega
        rw [hnj]
        omega
      have hb : bonusLast n g d = 1 := by
        unfold bonusLast
        rw [if_pos ⟨hgn, by rw [← hjn]; exact hdj1⟩]
      rw [if_pos hjn, hb]
      omega
  -- a piece of deficit 1 before a full piece receives one unit
  have hrr : g j = 0 → 0 < g (j + 1) → d j = 1 →
      1 ≤ (if 1 ≤ j then flowR g d (j - 1) else 0) +
        (if j = 0 then bonusFirst g d else 0) := by
    intro hg0 hg1 hdj1
    by_cases h1 : 1 ≤ j
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hf : flowR g d m = 1 := by
        unfold flowR
        rw [if_pos ⟨hg0, hg1, hdj1⟩]
      rw [if_pos h1, Nat.add_sub_cancel, hf]
      omega
    · have hj0 : j = 0 := by omega
      subst hj0
      have hb : bonusFirst g d = 1 := by
        unfold bonusFirst
        rw [if_pos ⟨hg0, hdj1⟩]
      rw [if_pos rfl, hb]
      omega
  -- the two gaps next to `j`
  have hLv : (gapNeed k (g j) = 0 ∧ g j = 0) ∨ (gapNeed k (g j) = k - 4 ∧ 0 < g j) := by
    unfold gapNeed
    split_ifs with h
    · right
      exact ⟨rfl, h⟩
    · left
      exact ⟨rfl, by omega⟩
  have hRv : (gapNeed k (g (j + 1)) = 0 ∧ g (j + 1) = 0) ∨
      (gapNeed k (g (j + 1)) = k - 4 ∧ 0 < g (j + 1)) := by
    unfold gapNeed
    split_ifs with h
    · right
      exact ⟨rfl, h⟩
    · left
      exact ⟨rfl, by omega⟩
  -- the product `(k - 3) * d j`
  have hX : (d j = 1 ∧ (k - 3) * d j = k - 3) ∨ (d j = 2 ∧ (k - 3) * d j = 2 * (k - 3)) ∨
      (3 ≤ d j ∧ 3 * (k - 3) ≤ (k - 3) * d j) := by
    rcases (by omega : d j = 1 ∨ d j = 2 ∨ 3 ≤ d j) with h | h | h
    · left
      exact ⟨h, by rw [h, Nat.mul_one]⟩
    · right
      left
      exact ⟨h, by rw [h, Nat.mul_comm]⟩
    · right
      right
      exact ⟨h, by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ h⟩
  unfold needL needR
  rcases hLv with ⟨hL1, hL2⟩ | ⟨hL1, hL2⟩ <;> rcases hRv with ⟨hR1, hR2⟩ | ⟨hR1, hR2⟩ <;>
    rcases hX with ⟨hX1, hX2⟩ | ⟨hX1, hX2⟩ | ⟨hX1, hX2⟩ <;> omega

/-- Twice a gap is covered by the two partial pieces next to it and, at an end of the chain,
by the price of that end. -/
theorem gap_le_need (hk : 7 ≤ k) (hn : 0 < n) (G2 : ∀ i < n + 1, g i ≤ k - 3)
    (i : ℕ) (hi : i < n + 1) :
    2 * g i ≤ (if i < n then needL k n g d i else 0) +
      (if 1 ≤ i then needR k n g d (i - 1) else 0) +
      (if i = 0 then (if 0 < g 0 then k - 2 else 0) else 0) +
      (if i = n then (if 0 < g n then k - 2 else 0) else 0) := by
  have hgi := G2 i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [if_pos hn, if_neg (by omega : ¬ 1 ≤ 0), if_pos rfl, if_neg (by omega : ¬ 0 = n)]
    unfold needL gapNeed
    split_ifs with h <;> omega
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [if_pos (by omega : 1 ≤ m + 1), Nat.add_sub_cancel, if_neg (by omega : ¬ m + 1 = 0)]
    by_cases hin : m + 1 < n
    · rw [if_pos hin, if_neg (by omega : ¬ m + 1 = n)]
      unfold needL needR gapNeed
      by_cases hlong : g (m + 1) = k - 3
      · have hc := charge_long (d := d) m hin hlong
        split_ifs with h <;> omega
      · split_ifs with h <;> omega
    · have hmn : m + 1 = n := by omega
      subst hmn
      rw [if_neg hin, if_pos rfl]
      unfold needR gapNeed
      split_ifs with h <;> omega

/-! ### The chain capacity -/

/-- **Lemma C1″.** Chain capacity with slope `k - 3`, from the five local facts. -/
theorem chain_capacity_slope3 (hk : 7 ≤ k)
    (hd : ∀ j < n, 1 ≤ d j)
    (G1 : n = 0 → g 0 ≤ k - 2)
    (G2 : 0 < n → ∀ i < n + 1, g i ≤ k - 3)
    (G3 : ∀ j < n, d j = 1 → g j = 0 ∨ g (j + 1) = 0)
    (G4 : ∀ i, 1 ≤ i → i < n → g i = k - 3 → k - 1 ≤ d (i - 1) + d i)
    (G5 : ∀ j, j + 1 < n → 0 < g j → d j = 1 → 2 ≤ d (j + 1)) :
    2 * (n + ∑ i ∈ Finset.range (n + 1), g i) ≤
      (k - 3) * ∑ j ∈ Finset.range n, d j + endFirst k n g d + endLast k n g d := by
  by_cases hG : ∑ i ∈ Finset.range (n + 1), g i = 0
  · -- no full piece at all
    rw [hG]
    have hsum : n ≤ ∑ j ∈ Finset.range n, d j := by
      calc n = ∑ _j ∈ Finset.range n, 1 := by simp
        _ ≤ ∑ j ∈ Finset.range n, d j :=
          Finset.sum_le_sum (fun j hj => hd j (Finset.mem_range.mp hj))
    have h2 : 2 * n ≤ (k - 3) * ∑ j ∈ Finset.range n, d j :=
      calc 2 * n ≤ (k - 3) * n := Nat.mul_le_mul_right n (by omega)
        _ ≤ (k - 3) * ∑ j ∈ Finset.range n, d j := Nat.mul_le_mul_left _ hsum
    omega
  · have hGpos : 0 < ∑ i ∈ Finset.range (n + 1), g i := Nat.pos_of_ne_zero hG
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- only full pieces
      subst hn
      have h0 := G1 rfl
      have hs1 : ∑ i ∈ Finset.range (0 + 1), g i = g 0 := by simp
      have hs0 : ∑ j ∈ Finset.range 0, d j = 0 := by simp
      have hg0 : 0 < g 0 := by rw [hs1] at hGpos; exact hGpos
      unfold endFirst endLast
      rw [if_pos hg0, hs1, hs0]
      omega
    · -- partial pieces and at least one full piece
      have hLI := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range n) =>
        local_ineq hk hd G3 G4 G5 j (Finset.mem_range.mp hj))
      simp only [Finset.sum_add_distrib] at hLI
      have hNeed := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (n + 1)) =>
        gap_le_need (d := d) hk hn (G2 hn) i (Finset.mem_range.mp hi))
      simp only [Finset.sum_add_distrib] at hNeed
      rw [sum_pred_eq_sum_succ n (flowL g d), sum_pred_eq_sum_succ n (flowR g d),
        sum_range_single n 0 _ hn, sum_range_single n (n - 1) _ (by omega),
        ← Finset.mul_sum] at hLI
      rw [sum_range_succ_lt n (needL k n g d), sum_range_succ_pred n (needR k n g d),
        sum_range_single (n + 1) 0 _ (by omega), sum_range_single (n + 1) n _ (by omega),
        ← Finset.mul_sum] at hNeed
      have hc2 : ∑ _j ∈ Finset.range n, 2 = 2 * n := by
        rw [sum_range_const, Nat.mul_comm]
      rw [hc2] at hLI
      have hF : bonusFirst g d + (if 0 < g 0 then k - 2 else 0) ≤ endFirst k n g d := by
        unfold bonusFirst endFirst
        split_ifs <;> omega
      have hL : bonusLast n g d + (if 0 < g n then k - 2 else 0) ≤ endLast k n g d := by
        unfold bonusLast endLast
        split_ifs <;> omega
      omega

end ChainB

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.ChainB.chain_capacity_slope3

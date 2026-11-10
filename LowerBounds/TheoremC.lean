import LowerBounds.TheoremCCore

/-!
# Theorem C: a conditional lower bound beyond the denominator k² - 4k + 1

Let `c = cn / q` and `b = bn / q`.  The one unproved input is the window hypothesis
`HStatement k cn bn q` (`ComponentCapacityC.lean`; a finite statement for each `k`, to be
certified by a search).  Under it and the conditions `ConditionsC k cn bn q`, for `k ≥ 5`,

  `Ssuper k ≥ hpv k + ⌈(2 (k-2)! - 2 (k-2) - b) / (k² - 4k + 1 - c (k - 1))⌉`.

Final statements (every bound has `HStatement`, in one case `HStatementTilde`, as an explicit
hypothesis):

* `theoremC_reduced`, `theoremC_pathwise`: `2 q (k-2)! + piC · hpv k ≤ piC · (wt(P) + k) +
  (2 q (k-2) + bn)` for `σ²`-reduced and for all Hamiltonian paths, `piC = q (k² - 4k + 1) -
  cn (k - 1)`;
* `theoremC_pathwise_expanded`: the same with the product by `piC` multiplied out, so that no
  subtraction involves the constants;
* `boundC_le_pathwise`, `superperm_boundC`: `boundC k cn bn q ≤ wt(P) + k` and `≤ Ssuper k`;
* `superperm_boundC_of_tilde`: the same from the stronger hypothesis with `s̃`;
* `superperm_boundC_explicit`: the same with the conditions as separate hypotheses;
* `hStatement_iff`: the hypothesis written out in the objects of the preimage-chain library;
* `conditionsC_8`, …, `conditionsC_14` and `superperm_boundC_8`, …, `superperm_boundC_14`: the
  seven sets of constants and the resulting numbers.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k cn bn q : ℕ}

/-- **Theorem C for `σ²`-reduced Hamiltonian paths**, conditional on the window hypothesis. -/
theorem theoremC_reduced (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian)
    (hred : Sigma2Reduced P) :
    2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) :=
  reduced_pathwise_C_of hk hcond hH hP hred

/-- **Theorem C for every Hamiltonian path**, conditional on the window hypothesis. -/
theorem theoremC_pathwise (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    2 * q * (k - 2).factorial + piC k cn q * hpv k ≤
      piC k cn q * (P.wtP + k) + (2 * q * (k - 2) + bn) :=
  pathwise_C_of hk hcond hH hP

/-- Theorem C for every Hamiltonian path with the product by `q Π` multiplied out. -/
theorem theoremC_pathwise_expanded (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    2 * q * (k - 2).factorial + q * (k * k - 4 * k + 1) * hpv k +
        cn * (k - 1) * (P.wtP + k) ≤
      q * (k * k - 4 * k + 1) * (P.wtP + k) + cn * (k - 1) * hpv k +
        (2 * q * (k - 2) + bn) := by
  have h := pathwise_C_of hk hcond hH hP
  have hle : cn * (k - 1) ≤ q * (k * k - 4 * k + 1) := by
    have h3 := hcond.cond_iii
    omega
  have h1 : piC k cn q * hpv k =
      q * (k * k - 4 * k + 1) * hpv k - cn * (k - 1) * hpv k := by
    unfold piC
    rw [Nat.sub_mul]
  have h2 : piC k cn q * (P.wtP + k) =
      q * (k * k - 4 * k + 1) * (P.wtP + k) - cn * (k - 1) * (P.wtP + k) := by
    unfold piC
    rw [Nat.sub_mul]
  have h3 : cn * (k - 1) * hpv k ≤ q * (k * k - 4 * k + 1) * hpv k :=
    Nat.mul_le_mul_right _ hle
  have h4 : cn * (k - 1) * (P.wtP + k) ≤ q * (k * k - 4 * k + 1) * (P.wtP + k) :=
    Nat.mul_le_mul_right _ hle
  rw [h1, h2] at h
  omega

/-- Theorem C for every Hamiltonian path, with the ceiling. -/
theorem boundC_le_pathwise (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) {P : HPath k} (hP : P.IsHamiltonian) :
    boundC k cn bn q ≤ P.wtP + k :=
  boundC_le_pathwise_of hk hcond hH hP

/-- **Theorem C**, conditional on the window hypothesis.  For `k ≥ 5`, every superpermutation
on `k` symbols has at least
`k! + (k-1)! + (k-2)! + k - 3 + ⌈(2 (k-2)! - 2 (k-2) - b) / (k² - 4k + 1 - c (k - 1))⌉`
letters, where `c = cn / q` and `b = bn / q`. -/
theorem superperm_boundC (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) : boundC k cn bn q ≤ Ssuper k :=
  superperm_boundC_of hk hcond hH

/-- Theorem C from the hypothesis in the form with `s̃(w) = slack_int(w) - 2 χ(w)`. -/
theorem superperm_boundC_of_tilde (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatementTilde k cn bn q) : boundC k cn bn q ≤ Ssuper k :=
  superperm_boundC_of hk hcond (hStatement_of_tilde hH)

/-- Theorem C with the conditions on the constants as separate hypotheses: `0 < q`,
(i) `b ≤ (k-3)(k-2) - c k - 6`, (ii) `b ≤ 2(k-6) - 4c + (k-5-c)(k-2)`,
(iii) `2(k-2) + b ≤ k² - 4k + 1 - c(k-1)`, each multiplied by `q`. -/
theorem superperm_boundC_explicit (hk : 5 ≤ k) (hq : 0 < q)
    (hi : bn + cn * k ≤ q * k * (k - 5))
    (hii : bn + 4 * cn + 2 * q * k ≤ 4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2))
    (hiii : 2 * q * (k - 2) + bn + cn * (k - 1) ≤ q * (k * k - 4 * k + 1))
    (hH : HStatement k cn bn q) : boundC k cn bn q ≤ Ssuper k :=
  superperm_boundC hk ⟨hq, hi, hii, hiii⟩ hH

/-! ### The hypothesis written out -/

/-- `HStatement k cn bn q` without the definitions of this development: for every exact
weight-three chain of a strongly exitless path on `k` symbols whose list of deficits `ds`
starts and ends with a non-zero entry and has an entry `≥ 2` in every maximal block of
non-zero entries, `q (2 |ds| + 2 (k - 4)) + cn Σds ≤ q (k - 3) Σds + bn`. -/
theorem hStatement_iff (k cn bn q : ℕ) :
    HStatement k cn bn q ↔
      ∀ (p : HPath k), p.StronglyExitless → ∀ chain : ExactWeightThreePieceChain p,
        ((∃ x rest, chain.pieces.map ComponentIntervalPiece.deficit = x :: rest ∧ 0 < x) ∧
          (∃ init y, chain.pieces.map ComponentIntervalPiece.deficit = init ++ [y] ∧ 0 < y) ∧
          (∀ pre blk post : List ℕ,
            chain.pieces.map ComponentIntervalPiece.deficit = pre ++ blk ++ post → blk ≠ [] →
            (∀ x ∈ blk, 0 < x) → (pre = [] ∨ ∃ pre', pre = pre' ++ [0]) →
            (post = [] ∨ ∃ post', post = 0 :: post') → ∃ x ∈ blk, 2 ≤ x)) →
        q * (2 * (chain.pieces.map ComponentIntervalPiece.deficit).length + 2 * (k - 4)) +
            cn * (chain.pieces.map ComponentIntervalPiece.deficit).sum ≤
          q * ((k - 3) * (chain.pieces.map ComponentIntervalPiece.deficit).sum) + bn := by
  constructor
  · intro h p hp chain hw
    exact h p hp chain ⟨hw.1, hw.2.1, hw.2.2⟩
  · intro h p hp chain hw
    exact h p hp chain ⟨hw.first_partial, hw.last_partial, hw.excess⟩

/-! ### The seven sets of constants -/

/-- `k = 8`, `c = 9/20`, `b = 73/5`. -/
theorem conditionsC_8 : ConditionsC 8 9 292 20 := ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 9`, `c = 1/10`, `b = 19/5`. -/
theorem conditionsC_9 : ConditionsC 9 1 38 10 := ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 10`, `c = 47/200`, `b = 88/25`. -/
theorem conditionsC_10 : ConditionsC 10 47 704 200 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 11`, `c = 7/80`, `b = 37/10`. -/
theorem conditionsC_11 : ConditionsC 11 7 296 80 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 12`, `c = 19/500`, `b = 266/125`. -/
theorem conditionsC_12 : ConditionsC 12 19 1064 500 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 13`, `c = 61/400`, `b = 149/50`. -/
theorem conditionsC_13 : ConditionsC 13 61 1192 400 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `k = 14`, `c = 19/400`, `b = 171/50`. -/
theorem conditionsC_14 : ConditionsC 14 19 1368 400 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem boundC_8 : boundC 8 9 292 20 = 46133 := by decide
theorem boundC_9 : boundC 9 1 38 10 = 408469 := by decide
theorem boundC_10 : boundC 10 47 704 200 = 4033377 := by decide
theorem boundC_11 : boundC 11 7 296 80 = 43917898 := by decide
theorem boundC_12 : boundC 12 19 1064 500 = 522622354 := by decide
theorem boundC_13 : boundC 13 61 1192 400 = 6746626424 := by decide
theorem boundC_14 : boundC 14 19 1368 400 = 93891137847 := by decide

/-- `H(8; 9/20, 73/5)` gives `Ssuper 8 ≥ 46133`. -/
theorem superperm_boundC_8 (hH : HStatement 8 9 292 20) : 46133 ≤ Ssuper 8 :=
  boundC_8 ▸ superperm_boundC (by norm_num) conditionsC_8 hH

/-- `H(9; 1/10, 19/5)` gives `Ssuper 9 ≥ 408469`. -/
theorem superperm_boundC_9 (hH : HStatement 9 1 38 10) : 408469 ≤ Ssuper 9 :=
  boundC_9 ▸ superperm_boundC (by norm_num) conditionsC_9 hH

/-- `H(10; 47/200, 88/25)` gives `Ssuper 10 ≥ 4033377`. -/
theorem superperm_boundC_10 (hH : HStatement 10 47 704 200) : 4033377 ≤ Ssuper 10 :=
  boundC_10 ▸ superperm_boundC (by norm_num) conditionsC_10 hH

/-- `H(11; 7/80, 37/10)` gives `Ssuper 11 ≥ 43917898`. -/
theorem superperm_boundC_11 (hH : HStatement 11 7 296 80) : 43917898 ≤ Ssuper 11 :=
  boundC_11 ▸ superperm_boundC (by norm_num) conditionsC_11 hH

/-- `H(12; 19/500, 266/125)` gives `Ssuper 12 ≥ 522622354`. -/
theorem superperm_boundC_12 (hH : HStatement 12 19 1064 500) : 522622354 ≤ Ssuper 12 :=
  boundC_12 ▸ superperm_boundC (by norm_num) conditionsC_12 hH

/-- `H(13; 61/400, 149/50)` gives `Ssuper 13 ≥ 6746626424`. -/
theorem superperm_boundC_13 (hH : HStatement 13 61 1192 400) : 6746626424 ≤ Ssuper 13 :=
  boundC_13 ▸ superperm_boundC (by norm_num) conditionsC_13 hH

/-- `H(14; 19/400, 171/50)` gives `Ssuper 14 ≥ 93891137847`. -/
theorem superperm_boundC_14 (hH : HStatement 14 19 1368 400) : 93891137847 ≤ Ssuper 14 :=
  boundC_14 ▸ superperm_boundC (by norm_num) conditionsC_14 hH

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.theoremC_reduced
#print axioms SuperpermLowerBounds.theoremC_pathwise
#print axioms SuperpermLowerBounds.theoremC_pathwise_expanded
#print axioms SuperpermLowerBounds.boundC_le_pathwise
#print axioms SuperpermLowerBounds.superperm_boundC
#print axioms SuperpermLowerBounds.superperm_boundC_of_tilde
#print axioms SuperpermLowerBounds.superperm_boundC_explicit
#print axioms SuperpermLowerBounds.hStatement_iff
#print axioms SuperpermLowerBounds.superperm_boundC_8
#print axioms SuperpermLowerBounds.superperm_boundC_9
#print axioms SuperpermLowerBounds.superperm_boundC_10
#print axioms SuperpermLowerBounds.superperm_boundC_11
#print axioms SuperpermLowerBounds.superperm_boundC_12
#print axioms SuperpermLowerBounds.superperm_boundC_13
#print axioms SuperpermLowerBounds.superperm_boundC_14

import K5897.Sound
import K5897.CapRules
import LowerBounds.PRules
import LowerBounds.PFinal

/-!
# Chain caps on 7 symbols from the kernel search

Halfar's `K6/Cap.lean` for 7 symbols.

`pstmt_of_capParts`: if the search of `Engine.lean` with the rules `capRules caps lo hi TB TK`
answers `false` in all its parts, and the bit tables agree with the rules of `PSearch.lean`, then the
statement `PS.PStmt` of `PSeq.lean` holds for the chain search F0 on the levels `lo … hi`.  From
there the theorems of `PLevels.lean` and `PRules.lean` of Halfar's proof of 5,899 (unchanged) give the chain
caps: `chainCapK_of_capParts`.

The proof relabels the symbols so that the first word is `1 2 3 4 5 6 7`, as `PS.stmt_of_parts` does,
and reads the rule along the sequence (`PS.RuleAlong`) as the rule of the engine (`KAlong`).
-/

namespace SuperpermLowerBounds
namespace K5897

open SuperpermLowerBounds.S SuperpermLowerBounds.PS

/-- The table `T` agrees with `f` on `r < 160`, `d < 80`. -/
def TabAgrees (T : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  (List.range 160).all fun r => (List.range 80).all fun d => T.testBit (80 * r + d) == f r d

theorem lk_eq {T : ℕ} {f : ℕ → ℕ → Bool} (h : TabAgrees T f = true) (r d : ℕ) : lk T f r d = f r d := by
  unfold lk
  by_cases hr : r < 160
  · by_cases hd : d < 80
    · have hrb : r.blt 160 = true := Nat.blt_eq.mpr hr
      have hdb : d.blt 80 = true := Nat.blt_eq.mpr hd
      rw [hrb, hdb]
      have h1 := List.all_eq_true.mp h r (List.mem_range.mpr hr)
      have h2 := List.all_eq_true.mp h1 d (List.mem_range.mpr hd)
      simpa using h2
    · have hdb : d.blt 80 = false := by
        cases h : d.blt 80
        · rfl
        · exact absurd (Nat.blt_eq.mp h) hd
      rw [hdb, Bool.and_false, cond_false]
  · have hrb : r.blt 160 = false := by
      cases h : r.blt 160
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hr
    rw [hrb, Bool.false_and, cond_false]

/-- `PS.PCont` is `KCont`. -/
theorem kcont_of_pcont : ∀ (rest : List TRow) (last : List ℕ) (used : List (List ℕ)),
    PCont 7 last used rest → KCont last used rest
  | [], _, _, _ => trivial
  | (_, []) :: _, _, _, h => h.elim
  | (kd, v :: R) :: rest, last, used, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨by omega, h2, fun hk => h3.1 hk, h4, h5, h6, kcont_of_pcont rest _ _ h7⟩

section Cap

variable {caps : List (List ℕ)} {lo hi TB TK : ℕ}

/-- The rule along a sequence of the chain search is the rule of the engine. -/
theorem kalong_of_ruleAlong (hB : TabAgrees TB (seqBad caps 0 lo hi 0) = true)
    (hK : TabAgrees TK (seqKeepN caps 0 lo hi 0) = true) :
    ∀ (rest : List TRow) (r d : ℕ) (last : List ℕ) (used : List (List ℕ)),
      RuleAlong 7 false (seqBad caps 0 lo hi) noRule (seqKeepN caps 0 lo hi)
        (seqKeepS caps 0 lo hi) noRule 0 r d last rest →
      KAlong (capRules caps lo hi TB TK) (r, d) used rest
  | [], r, d, last, used, h => by
    simp only [RuleAlong, noRule, Bool.false_eq_true, false_and, or_false] at h
    show lk TB (seqBad caps 0 lo hi 0) r d = true
    rw [lk_eq hB]
    exact h
  | (_, []) :: _, _, _, _, _, h => by simp [RuleAlong] at h
  | (kd, v :: R) :: rest, r, d, last, used, h => by
    simp only [RuleAlong] at h
    obtain ⟨hk, h'⟩ := h
    match kd, hk, h' with
    | 0, hk, h' =>
      refine ⟨?_, ?_⟩
      · show lk TK (seqKeepN caps 0 lo hi 0) r d = true
        rw [lk_eq hK]
        exact hk
      · have e : stepC (capRules caps lo hi TB TK) (r, d) 0 (5 - R.length)
            (enc ((v :: R).getLast (List.cons_ne_nil v R))) = (r + 1, d + (5 - R.length)) :=
          rfl
        rw [e]
        simp only [tK, rK, if_pos] at h'
        have e2 : 7 - 2 - R.length = 5 - R.length := rfl
        rw [e2] at h'
        exact kalong_of_ruleAlong hB hK rest _ _ _ _ h'
    | 1, hk, _ => simp [keepK, seqKeepS] at hk
    | kd + 2, hk, _ => simp [keepK, noRule] at hk

/-- **The chain search on 7 symbols, evaluated by the kernel, proves the statement of
`PSeq.lean`.** -/
theorem pstmt_of_capParts {fuel : ℕ}
    (hB : TabAgrees TB (seqBad caps 0 lo hi 0) = true)
    (hK : TabAgrees TK (seqKeepN caps 0 lo hi 0) = true)
    (hs : part (capRules caps lo hi TB TK) fuel = false) :
    PStmt 7 false (seqBad caps 0 lo hi) noRule (seqKeepN caps 0 lo hi) (seqKeepS caps 0 lo hi)
      noRule := by
  intro L hL hne hkeep
  refine ⟨?_, fun h => by simp [ap, noRule] at h⟩
  by_contra hbad
  rw [Bool.not_eq_false] at hbad
  cases L with
  | nil => exact hne rfl
  | cons x0 rest0 =>
    obtain ⟨kd0, Q0⟩ := x0
    have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
    obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    have hv0 : PermW 7 v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
    have hL' := hL.relabel hv0
    have hkeep' : ∀ u x w, relabSeq v0 ((kd0, v0 :: R0) :: rest0) = u ++ x :: w → u ≠ [] →
        ap (keepK (seqKeepN caps 0 lo hi) (seqKeepS caps 0 lo hi) noRule x.1) (cnt 7 false u)
          = true := by
      intro u x w huw hu
      obtain ⟨u0, L2, e0, hu0, hL2⟩ := List.map_eq_append_iff.mp huw
      obtain ⟨x1, w1, e1, hx1, _⟩ := List.map_eq_cons_iff.mp hL2
      have h := hkeep u0 x1 w1 (by rw [e0, e1]) (by
        rintro rfl
        exact hu hu0.symm)
      have ec : cnt 7 false u = cnt 7 false u0 := by
        rw [← hu0]
        exact cnt_relab false v0 u0
      rw [ec, ← hx1]
      exact h
    have hbad' : ap (seqBad caps 0 lo hi) (cnt 7 false (relabSeq v0 ((kd0, v0 :: R0) :: rest0)))
        = true := by
      rw [cnt_relab]
      exact hbad
    have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
        (kd0, [1, 2, 3, 4, 5, 6, 7] :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
      have e := S.map_relab_self hv0.1
      rw [hv0.2.1] at e
      have e' : v0.map (S.relab v0) = [1, 2, 3, 4, 5, 6, 7] := by rw [e]; rfl
      simp [relabSeq, e']
    rw [hshape] at hL' hkeep' hbad'
    generalize R0.map (List.map (S.relab v0)) = R1 at hL' hkeep' hbad'
    generalize relabSeq v0 rest0 = rest1 at hL' hkeep' hbad'
    have hperm : ∀ w ∈ [1, 2, 3, 4, 5, 6, 7] :: R1, PermW 7 w :=
      hL'.words (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self
    have hcl : List.Pairwise (fun a b => ¬ a ~r b)
        (([1, 2, 3, 4, 5, 6, 7] :: R1) ++ (rest1.map Prod.snd).flatten) := by
      have := hL'.classes
      simp only [List.map_cons, List.flatten_cons] at this
      exact this
    have hcl' := List.pairwise_append.mp hcl
    have hsz := hL'.size_le (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self
    have hR1 : R1.length ≤ 5 := by
      simp only [List.length_cons] at hsz
      omega
    have hdoor := S.door_chain (by norm_num) _ hperm
      (hL'.doors (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self) hcl'.1
    have hcont := pcont_of_seq (by norm_num) rest1 (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1)
      ([1, 2, 3, 4, 5, 6, 7] :: R1) (List.cons_ne_nil _ _) hL' hcl'.2.2
    have hne1 : ∀ y ∈ rest1, y.2 ≠ [] :=
      fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)
    have ec : (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) = (0, 1, 5 - R1.length) := by
      simp only [List.length_cons, Prod.mk.injEq, true_and]
      omega
    have hA := ruleAlong_of_prefix (k := 7) false (seqBad caps 0 lo hi) noRule
      (seqKeepN caps 0 lo hi) (seqKeepS caps 0 lo hi) noRule rest1 (0, 1, 5 - R1.length)
      (([1, 2, 3, 4, 5, 6, 7] :: R1).getLast (List.cons_ne_nil _ _)) hne1
      (by
        intro u x w huw
        have h := hkeep' ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: u) x w (by rw [huw]; rfl) (by simp)
        have e2 : cnt 7 false ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: u)
            = u.foldl (SuperpermLowerBounds.PS.stepC 7 false) (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) := rfl
        rw [e2, ec] at h
        exact h)
      (by
        have e2 : cnt 7 false ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: rest1)
            = rest1.foldl (SuperpermLowerBounds.PS.stepC 7 false) (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) := rfl
        rw [e2, ec] at hbad'
        exact Or.inl hbad')
    have hK' := kalong_of_ruleAlong hB hK rest1 1 (5 - R1.length) _ ([1, 2, 3, 4, 5, 6, 7] :: R1) hA
    exact not_kalong (capRules caps lo hi TB TK) hs R1 rest1 hR1 hperm hdoor hcl'.1
      (kcont_of_pcont _ _ _ hcont) hK'

end Cap

/-- **Chain caps from the kernel search** (levels `0 … hi`). -/
theorem wcap_of_capParts {caps : List (List ℕ)} {hi TB TK fuel : ℕ}
    (hB : TabAgrees TB (seqBad caps 0 0 hi 0) = true)
    (hK : TabAgrees TK (seqKeepN caps 0 0 hi 0) = true)
    (hs : part (capRules caps 0 hi TB TK) fuel = false) :
    WCap 7 (capF caps 0) hi :=
  wcap_of_seqCap (seqCap_level (fun j hj => absurd hj (Nat.not_lt_zero j))
    (seqCapLt_zero 7 0 _) (pstmt_of_capParts hB hK hs))

/-- **Chain caps from the kernel search** (levels `0 … hi`), on vertices. -/
theorem chainCapK_of_capParts {caps : List (List ℕ)} {hi TB TK fuel : ℕ}
    (hB : TabAgrees TB (seqBad caps 0 0 hi 0) = true)
    (hK : TabAgrees TK (seqKeepN caps 0 0 hi 0) = true)
    (hs : part (capRules caps 0 hi TB TK) fuel = false) :
    ChainCapK 7 (capF caps 0) hi :=
  chainCapK_of_wcap (wcap_of_capParts hB hK hs)

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.chainCapK_of_capParts

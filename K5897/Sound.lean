import K5897.EngineOK
import LowerBounds.PSound

/-!
# The search of `Engine.lean` is complete

Halfar's `K6/Sound.lean` for 7 symbols (rows of up to 6 blocks, six successors of weight 3, 5,040
words).

A sequence of rows on words is a list of `TRow`s (`PS.TRow`, the type of `PSearch.lean`): the kind of
the link before the row (`0`: a seam, the exit of the last block overlaps the entry in 3 letters;
anything else: a jump) and the words of its blocks.  `KCont last used rest`: the rows `rest`
continue a sequence whose last entry is `last` and whose blocks are `used`: every row has 1 to 6
blocks joined by doors, a seam is a seam, and all classes are new.  `KAlong ρ c used rest`: the
rule `ρ` holds along `rest` from the counters `c`: every row is preceded by a sequence that the
rule continues with the kind of that row, and the whole sequence is found (`ρ.bad`, given the set of
its classes `maskOf`).

`not_kalong`: if every part of the search answers `false`, the rule holds along no sequence that
starts with a row whose first word is `1 2 3 4 5 6 7`.

The search is a function of its arguments only (no state comes back from a call), so the proof is
a plain induction: the walk that starts at the first block of a row of new classes reaches the end
of the row (`walk_found`), the seam and the jump that lead to the row are among those the search
tries (`succ3_found`, `jumps_found`), and at the end the rule says "found" (`go_found`).
-/

namespace SuperpermLowerBounds
namespace K5897

open SuperpermLowerBounds.S

/-- A row with the kind of the link before it. -/
abbrev TRow := SuperpermLowerBounds.PS.TRow

/-- The set of classes of a list of words, as a number (bit `ci (enc w)` for every word `w`). -/
def maskOf (used : List (List ℕ)) : ℕ := used.foldl (fun U w => U ||| bit (ciC (enc w))) 0

theorem maskOf_append_singleton (used : List (List ℕ)) (v : List ℕ) :
    maskOf (used ++ [v]) = maskOf used ||| bit (ciC (enc v)) := by
  unfold maskOf
  rw [List.foldl_append]
  rfl

theorem testBit_bit (c d : ℕ) : (bit c).testBit d = decide (c = d) := by
  show (1 <<< c).testBit d = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_foldl (c : ℕ) : ∀ (l : List (List ℕ)) (U0 : ℕ),
    (l.foldl (fun U w => U ||| bit (ciC (enc w))) U0).testBit c = true ↔
      U0.testBit c = true ∨ ∃ u ∈ l, ciC (enc u) = c
  | [], U0 => by simp
  | w :: l, U0 => by
    rw [List.foldl_cons, testBit_foldl c l, Nat.testBit_or, testBit_bit]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp, or_assoc]

theorem testBit_maskOf (used : List (List ℕ)) (c : ℕ) :
    (maskOf used).testBit c = true ↔ ∃ u ∈ used, ciC (enc u) = c := by
  unfold maskOf
  rw [testBit_foldl]
  simp

/-- A word of a class that no used word has is not marked. -/
theorem unmarked {used : List (List ℕ)} (hused : ∀ u ∈ used, PermW 7 u) {v : List ℕ}
    (hv : PermW 7 v) (hnew : ∀ u ∈ used, ¬ u ~r v) : (maskOf used).testBit (ciC (enc v)) = false := by
  by_contra h
  rw [Bool.not_eq_false, testBit_maskOf] at h
  obtain ⟨u, hu, he⟩ := h
  exact hnew u hu (ci_rot (hused u hu) hv he)

/-! ### The walk, the seams, the jumps -/

theorem walk_succ (g : ℕ → ℕ → ℕ → Bool) (U D n : ℕ) :
    walk g U D (n + 1) = cond (U.testBit (ciC D)) false
      (g (U ||| bit (ciC D)) D n || walk g (U ||| bit (ciC D)) (nxtC D) n) := rfl

/-- The walk that starts at the first block of a row `v :: R` of new classes finds what the
search below the sequence extended by the row finds. -/
theorem walk_found (g : ℕ → ℕ → ℕ → Bool) :
    ∀ (R : List (List ℕ)) (n : ℕ) (v : List ℕ) (used : List (List ℕ)),
      R.length ≤ n → (∀ w ∈ v :: R, PermW 7 w) → List.IsChain (DoorEq 7) (v :: R) →
      (∀ u ∈ used, PermW 7 u) → (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) →
      List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      g (maskOf (used ++ v :: R)) (enc ((v :: R).getLast (List.cons_ne_nil v R))) (n - R.length)
        = true →
      walk g (maskOf used) (enc v) (n + 1) = true := by
  intro R
  induction R with
  | nil =>
    intro n v used _ hperm _ hused hnew _ hg
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    rw [walk_succ, h0, cond_false]
    rw [List.getLast_singleton, List.length_nil, Nat.sub_zero, maskOf_append_singleton] at hg
    rw [hg, Bool.true_or]
  | cons v' R' ih =>
    intro n v used hn hperm hdoor hused hnew hpw hg
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    rw [walk_succ, h0, cond_false, ← maskOf_append_singleton, nx_enc hv hdc.1]
    have hw := ih m v' (used ++ [v]) (by simp only [List.length_cons] at hn; omega)
      (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2
      (by
        intro u hu
        rcases List.mem_append.mp hu with h | h
        · exact hused u h
        · rw [List.mem_singleton.mp h]
          exact hv)
      (by
        intro u hu w hw
        rcases List.mem_append.mp hu with h | h
        · exact hnew u h w (List.mem_cons_of_mem _ hw)
        · rw [List.mem_singleton.mp h]
          exact hpc.1 w hw)
      hpc.2
      (by
        have e : used ++ [v] ++ v' :: R' = used ++ v :: v' :: R' := by simp
        rw [e]
        rw [List.getLast_cons (List.cons_ne_nil v' R')] at hg
        have e2 : m + 1 - (v' :: R').length = m - R'.length := by
          simp only [List.length_cons]
          omega
        rw [e2] at hg
        exact hg)
    rw [hw, Bool.or_true]

theorem succ3_found (g : ℕ → ℕ → ℕ → Bool) (U q : ℕ) {j : ℕ} (hw : walk g U (s3 q j) 6 = true) :
    ∀ m, j < m → succ3 g U q m = true
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    show (walk g U (s3 q m) 6 || succ3 g U q m) = true
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [succ3_found g U q hw m h', Bool.or_true]
    · rw [hw, Bool.true_or]

theorem jumps_found (g : ℕ → ℕ → ℕ → Bool) (U : ℕ) {i : ℕ} (hw : walk g U i 6 = true) :
    ∀ m, i < m → jumps g U m = true
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    show (walk g U m 6 || jumps g U m) = true
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [jumps_found g U hw m h', Bool.or_true]
    · rw [hw, Bool.true_or]

/-! ### Sequences and the rule along them -/

section Rule

variable {Cn : Type} (ρ : Rules Cn)

/-- The counters after a row with `n` holes and last entry `e` that follows a link of kind `kd`. -/
def stepC (c : Cn) (kd n e : ℕ) : Cn := if kd = 0 then ρ.stN c n e else ρ.stJ c n e

/-- The rule for a link of kind `kd`. -/
def keepC (c : Cn) (kd : ℕ) : Bool := if kd = 0 then ρ.keepN c else ρ.keepJ c

/-- The rows `rest` continue a sequence with last entry `last` and blocks `used`. -/
def KCont : List ℕ → List (List ℕ) → List TRow → Prop
  | _, _, [] => True
  | _, _, (_, []) :: _ => False
  | last, used, (kd, v :: R) :: rest =>
    R.length ≤ 5 ∧ (∀ w ∈ v :: R, PermW 7 w) ∧ (kd = 0 → WLink 7 3 last v) ∧
      List.IsChain (DoorEq 7) (v :: R) ∧ (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      List.Pairwise (fun a b => ¬ a ~r b) (v :: R) ∧
      KCont ((v :: R).getLast (List.cons_ne_nil v R)) (used ++ v :: R) rest

/-- The rule holds along `rest` from the counters `c`, the blocks so far being `used`. -/
def KAlong : Cn → List (List ℕ) → List TRow → Prop
  | c, used, [] => ρ.bad c (maskOf used) = true
  | _, _, (_, []) :: _ => False
  | c, used, (kd, v :: R) :: rest =>
    keepC ρ c kd = true ∧
      KAlong (stepC ρ c kd (5 - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))))
        (used ++ v :: R) rest

theorem go_succ (f U q : ℕ) (c : Cn) :
    go ρ (f + 1) U q c =
      (ρ.bad c U || (ρ.keepN c && succ3 (fun U' e n => go ρ f U' e (ρ.stN c n e)) U q 6) ||
        (ρ.keepJ c && jumps (fun U' e n => go ρ f U' e (ρ.stJ c n e)) U 5040)) := rfl

/-- The search finds the end of a sequence of which it has reached a prefix, if the rule holds
along the rest. -/
theorem go_found :
    ∀ (fuel : ℕ) (rest : List TRow) (c : Cn) (last : List ℕ) (used : List (List ℕ)),
      PermW 7 last → last ∈ used → (∀ u ∈ used, PermW 7 u) → KCont last used rest →
      KAlong ρ c used rest → go ρ fuel (maskOf used) (enc last) c = true := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ f ih =>
    intro rest c last used hlast hlu hused hcont hal
    rw [go_succ]
    by_cases hb : ρ.bad c (maskOf used) = true
    · rw [hb, Bool.true_or, Bool.true_or]
    · cases rest with
      | nil => exact absurd hal hb
      | cons x rest' =>
        obtain ⟨kd, Q⟩ := x
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
          obtain ⟨hkeep, hal'⟩ := hal
          have hv : PermW 7 v := hperm v List.mem_cons_self
          have hused' : ∀ u ∈ used ++ v :: R, PermW 7 u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          -- the walk along the row reaches the end
          have hwalk : ∀ (st : Cn → ℕ → ℕ → Cn),
              st c (5 - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) =
                stepC ρ c kd (5 - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) →
              walk (fun U' e n => go ρ f U' e (st c n e)) (maskOf used) (enc v) 6 = true := by
            intro st hst
            apply walk_found _ R 5 v used hR hperm hdoor hused hnew hpw
            show go ρ f _ _ (st c (5 - R.length) _) = true
            rw [hst]
            exact ih rest' _ _ _ (hperm _ (List.getLast_mem _))
              (List.mem_append_right _ (List.getLast_mem _)) hused' hcont' hal'
          by_cases hk : kd = 0
          · subst hk
            have hkN : ρ.keepN c = true := by simpa [keepC] using hkeep
            obtain ⟨j, hj, hjv⟩ := s3_enc hlast hv (hlink rfl)
            have hw := hwalk ρ.stN (by simp [stepC])
            rw [← hjv] at hw
            rw [hkN, succ3_found _ _ _ hw 6 hj]
            simp
          · have hkJ : ρ.keepJ c = true := by simpa [keepC, hk] using hkeep
            have hw := hwalk ρ.stJ (by simp [stepC, hk])
            rw [hkJ, jumps_found _ _ hw 5040 (enc_lt hv)]
            simp

/-- **The search is complete.**  If the search answers `false`, the rule holds along no sequence
whose first row starts at `1 2 3 4 5 6 7`. -/
theorem not_kalong {fuel : ℕ} (hs : part ρ fuel = false)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ 5) (hperm : ∀ w ∈ [1, 2, 3, 4, 5, 6, 7] :: R1, PermW 7 w)
    (hdoor : List.IsChain (DoorEq 7) ([1, 2, 3, 4, 5, 6, 7] :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) ([1, 2, 3, 4, 5, 6, 7] :: R1))
    (hcont : KCont ((([1, 2, 3, 4, 5, 6, 7] :: R1).getLast (List.cons_ne_nil _ _)))
      ([1, 2, 3, 4, 5, 6, 7] :: R1) rest) :
    ¬ KAlong ρ (ρ.init (5 - R1.length)
      (enc (([1, 2, 3, 4, 5, 6, 7] :: R1).getLast (List.cons_ne_nil _ _))))
      ([1, 2, 3, 4, 5, 6, 7] :: R1) rest := by
  intro hA
  have h := walk_found (fun U e n => go ρ fuel U e (ρ.init n e)) R1 5 [1, 2, 3, 4, 5, 6, 7] []
    hR1 hperm hdoor (by simp) (by simp) hpw
    (by
      show go ρ fuel _ _ _ = true
      exact go_found ρ fuel rest _ _ _ (hperm _ (List.getLast_mem _))
        (List.getLast_mem _) hperm hcont (by simpa using hA))
  rw [enc_id] at h
  have h2 : part ρ fuel = true := h
  rw [hs] at h2
  cases h2

end Rule

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.not_kalong

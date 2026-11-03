import LowerBounds.DSound
import LowerBounds.PSearch

/-!
# The search of `PSearch.lean` is complete

The engine `PS.go` is given functions `ci`, `nxt`, `s3`, `s4`, a list `jl` and a number `st`.
`Enc k enc ci nxt s3 s4 jl st` says what the proof needs about them, for a coding `enc` of
permutation words by numbers:

* words with the same class index are rotations of each other;
* `nxt` is the door;
* `s3`, `s4` list (at least) the words that the exit of a block overlaps in `k - 3`, `k - 4`
  symbols; `jl` lists (at least) all words; `st` is the word `1 2 … k`.

`not_ruleAlong_of_search`: if every part of the search answers `false`, there is no sequence of
rows that starts at `1 2 … k`, is a valid continuation at every row (`PCont`) and along which the
rule holds (`RuleAlong`): every proper prefix satisfies the `keep` of the link that follows, and
the whole sequence is found.

A row is a pair `(kd, blocks)`: `kd` is the kind of the link before it (`0`: weight 3, `1`: weight
4, otherwise a jump).  The proof is the proof of `DSound.lean` (`pgo_complete`) with the three
kinds of links; the lemmas about the table of marks are taken from there.
-/

namespace SuperpermLowerBounds
namespace PS

open S (PermW WLink DoorEq Sub)

/-- A row with the kind of the link before it. -/
abbrev TRow := ℕ × List (List ℕ)

/-- What the engine needs to know about its tables. -/
structure Enc (k : ℕ) (enc : List ℕ → ℕ) (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (jl : List ℕ)
    (st : ℕ) : Prop where
  ci_inj : ∀ u v, PermW k u → PermW k v → ci (enc u) = ci (enc v) → u ~r v
  nxt_eq : ∀ a b, PermW k a → DoorEq k a b → nxt (enc a) = enc b
  s3_mem : ∀ u v, PermW k u → PermW k v → WLink k 3 u v → enc v ∈ s3 (enc u)
  s4_mem : ∀ u v, PermW k u → PermW k v → WLink k 4 u v → enc v ∈ s4 (enc u)
  jl_mem : ∀ v, PermW k v → enc v ∈ jl
  st_eq : st = enc (List.range' 1 k)

/-! ### The table of marks -/

/-- Every mark of the table is the class index of one of the words of `used`. -/
def MInv (enc : List ℕ → ℕ) (ci : ℕ → ℕ) (M : ByteArray) (used : List (List ℕ)) : Prop :=
  ∀ j, M.get! j ≠ 0 → ∃ u ∈ used, j = ci (enc u)

theorem MInv.sub {enc : List ℕ → ℕ} {ci : ℕ → ℕ} {M' M : ByteArray} {used : List (List ℕ)}
    (h : MInv enc ci M used) (hs : Sub M' M) : MInv enc ci M' used := fun j hj => h j (hs j hj)

theorem minv_marks0 (enc : List ℕ → ℕ) (ci : ℕ → ℕ) (sz : ℕ) : MInv enc ci (marks0 sz) [] :=
  fun j hj => absurd (S.get!_marks0 sz j) hj

theorem minv_set {enc : List ℕ → ℕ} {ci : ℕ → ℕ} {M : ByteArray} {used : List (List ℕ)}
    (h : MInv enc ci M used) (v : List ℕ) :
    MInv enc ci (M.set! (ci (enc v)) 1) (used ++ [v]) := by
  intro j hj
  rcases S.marked_set M _ j 1 hj with h1 | h1
  · exact ⟨v, by simp, h1⟩
  · obtain ⟨u, hu, he⟩ := h j h1
    exact ⟨u, List.mem_append_left _ hu, he⟩

section Engine

variable {k : ℕ} {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ}
  {st : ℕ}

/-- A word that is not a rotation of any used word has no mark. -/
theorem unmarked_of_new (E : Enc k enc ci nxt s3 s4 jl st) {M : ByteArray}
    {used : List (List ℕ)} (hM : MInv enc ci M used) (hused : ∀ u ∈ used, PermW k u)
    {v : List ℕ} (hv : PermW k v) (hnew : ∀ u ∈ used, ¬ u ~r v) : M.get! (ci (enc v)) = 0 := by
  by_contra hm
  obtain ⟨u, hu, he⟩ := hM _ hm
  exact hnew u hu (E.ci_inj u v (hused u hu) hv he.symm)

/-! ### The equations of the search -/

theorem walk_zero (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (D : ℕ)
    (M : ByteArray) : walk ci nxt visit 0 D M = M := rfl

theorem walk_succ (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (n D : ℕ)
    (M : ByteArray) : walk ci nxt visit (n + 1) D M =
      if M.get! (ci D) = 0 then
        if (visit n D (M.set! (ci D) 1)).size = 0 then visit n D (M.set! (ci D) 1)
        else (walk ci nxt visit n (nxt D) (visit n D (M.set! (ci D) 1))).set! (ci D) 0
      else M := by
  rw [← S.if_size, ← S.if_bne]
  rfl

theorem all_nil (w : ℕ → ByteArray → ByteArray) (M : ByteArray) : all w [] M = M := rfl

theorem all_cons (w : ℕ → ByteArray → ByteArray) (D : ℕ) (Ds : List ℕ) (M : ByteArray) :
    all w (D :: Ds) M = if (w D M).size = 0 then w D M else all w Ds (w D M) := by
  rw [← S.if_size]
  rfl

/-- The calls below a sequence for one kind of link, if the rule allows it. -/
def stepW (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (kb : ℕ) (c : Bool)
    (l : List ℕ) (M : ByteArray) : ByteArray :=
  if c then all (fun D M' => walk ci nxt visit kb D M') l M else M

theorem go_zero (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (jl : List ℕ) (st kb : ℕ) (rs : Bool)
    (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) (fg nt tp t r d q : ℕ) (M : ByteArray) :
    go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp 0 t r d q M =
      ByteArray.empty := rfl

theorem go_succ (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (jl : List ℕ) (st kb : ℕ) (rs : Bool)
    (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) (fg nt tp fuel t r d q : ℕ)
    (M : ByteArray) :
    go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp (fuel + 1) t r d q M =
      if (bad t r d || (badR t r d && (s3 q).contains st)) = true then ByteArray.empty
      else if (fuel != fg || q % nt == tp) = true then
        if (stepW ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1) (d + n)
              e M'') kb (keepN t r d) (s3 q) M).size = 0 then
          stepW ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1) (d + n)
              e M'') kb (keepN t r d) (s3 q) M
        else if (stepW ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
              ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb (keepS t r d)
            (s4 q) (stepW ci nxt (fun n e M'' =>
              go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1)
                (d + n) e M'') kb (keepN t r d) (s3 q) M)).size = 0 then
          stepW ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
              ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb (keepS t r d)
            (s4 q) (stepW ci nxt (fun n e M'' =>
              go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1)
                (d + n) e M'') kb (keepN t r d) (s3 q) M)
        else
          stepW ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
              ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb (keepJ t r d)
            jl (stepW ci nxt (fun n e M'' =>
              go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
                ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb (keepS t r d)
              (s4 q) (stepW ci nxt (fun n e M'' =>
                go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1)
                  (d + n) e M'') kb (keepN t r d) (s3 q) M))
      else M := by
  rw [← S.if_size, ← S.if_size]
  rfl

/-! ### No part of the search leaves a new mark -/

theorem walk_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) :
    ∀ (n D : ℕ) (M : ByteArray), Sub (walk ci nxt visit n D M) M := by
  intro n
  induction n with
  | zero =>
    intro D M
    rw [walk_zero]
    exact Sub.refl M
  | succ n ih =>
    intro D M
    rw [walk_succ]
    by_cases h0 : M.get! (ci D) = 0
    · rw [if_pos h0]
      by_cases hz : (visit n D (M.set! (ci D) 1)).size = 0
      · rw [if_pos hz]
        exact S.sub_of_size_zero hz M
      · rw [if_neg hz]
        exact S.sub_clear ((ih _ _).trans (hv _ _ _))
    · rw [if_neg h0]
      exact Sub.refl M

theorem all_sub (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Sub (w D M) M) :
    ∀ (Ds : List ℕ) (M : ByteArray), Sub (all w Ds M) M
  | [], M => Sub.refl M
  | D :: Ds, M => by
    rw [all_cons]
    by_cases hz : (w D M).size = 0
    · rw [if_pos hz]
      exact hw D M
    · rw [if_neg hz]
      exact (all_sub w hw Ds _).trans (hw D M)

theorem stepW_sub (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb : ℕ) (c : Bool) (l : List ℕ) (M : ByteArray) :
    Sub (stepW ci nxt visit kb c l M) M := by
  unfold stepW
  by_cases hc : c = true
  · rw [if_pos hc]
    exact all_sub _ (fun D M' => walk_sub ci nxt visit hv kb D M') l M
  · rw [if_neg hc]
    exact Sub.refl M

theorem go_sub (ci nxt : ℕ → ℕ) (s3 s4 : ℕ → List ℕ) (jl : List ℕ) (st kb : ℕ) (rs : Bool)
    (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) (fg nt tp : ℕ) :
    ∀ (fuel t r d q : ℕ) (M : ByteArray),
      Sub (go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t r d q M) M := by
  intro fuel
  induction fuel with
  | zero =>
    intro t r d q M
    rw [go_zero]
    exact S.sub_of_size_zero ByteArray.size_empty M
  | succ fuel ih =>
    intro t r d q M
    rw [go_succ]
    have h1 := stepW_sub ci nxt (fun n e M'' =>
      go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1) (d + n) e M'')
      (fun n e M'' => ih _ _ _ _ _) kb (keepN t r d) (s3 q) M
    have h2 := fun X => stepW_sub ci nxt (fun n e M'' =>
      go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
        ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'')
      (fun n e M'' => ih _ _ _ _ _) kb (keepS t r d) (s4 q) X
    have h3 := fun X => stepW_sub ci nxt (fun n e M'' =>
      go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
        ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'')
      (fun n e M'' => ih _ _ _ _ _) kb (keepJ t r d) jl X
    split_ifs
    · exact S.sub_of_size_zero ByteArray.size_empty M
    · exact h1
    · exact (h2 _).trans h1
    · exact ((h3 _).trans (h2 _)).trans h1
    · exact Sub.refl M

/-! ### The search follows a sequence -/

/-- The walk that starts at the first block of a row `v :: R` whose classes are new finds what
the search below the sequence extended by that row finds. -/
theorem walk_complete (E : Enc k enc ci nxt s3 s4 jl st)
    (visit : ℕ → ℕ → ByteArray → ByteArray) (hsub : ∀ n e M, Sub (visit n e M) M) :
    ∀ (R : List (List ℕ)) (n : ℕ) (v : List ℕ) (M : ByteArray) (used : List (List ℕ)),
      R.length ≤ n → (∀ w ∈ v :: R, PermW k w) → List.IsChain (DoorEq k) (v :: R) →
      MInv enc ci M used → (∀ u ∈ used, PermW k u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      (∀ M', MInv enc ci M' (used ++ v :: R) →
        (visit (n - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) M').size = 0) →
      (walk ci nxt visit (n + 1) (enc v) M).size = 0 := by
  intro R
  induction R with
  | nil =>
    intro n v M used _ hperm _ hM hused hnew _ hfin
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hf : (visit n (enc v) (M.set! (ci (enc v)) 1)).size = 0 := hfin _ (minv_set hM v)
    rw [walk_succ, if_pos h0, if_pos hf]
    exact hf
  | cons v' R' ih =>
    intro n v M used hn hperm hdoor hM hused hnew hpw hfin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked_of_new E hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    have hused' : ∀ u ∈ used ++ [v], PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hused u h
      · rw [List.mem_singleton.mp h]
        exact hv
    rw [walk_succ, if_pos h0]
    by_cases hz : (visit (m + 1) (enc v) (M.set! (ci (enc v)) 1)).size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz, ByteArray.size_set!, E.nxt_eq v v' hv hdc.1]
      apply ih m v' _ (used ++ [v]) (by simp only [List.length_cons] at hn; omega)
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2
        ((minv_set hM v).sub (hsub _ _ _)) hused'
        (by
          intro u hu w hw
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]
            exact hpc.1 w hw)
        hpc.2
      intro M' hM'
      have e : used ++ [v] ++ v' :: R' = used ++ v :: v' :: R' := by simp
      rw [e] at hM'
      have h := hfin M' hM'
      rw [List.getLast_cons (List.cons_ne_nil v' R')] at h
      have e2 : m + 1 - (v' :: R').length = m - R'.length := by
        simp only [List.length_cons]
        omega
      rw [e2] at h
      exact h

/-- One of the calls of `all` is found: then `all` is found, if the property `P` that this call
needs survives the calls before it. -/
theorem all_found (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Sub (w D M) M)
    (P : ByteArray → Prop) (hP : ∀ M' M, Sub M' M → P M → P M') (D : ℕ)
    (hD : ∀ M, P M → (w D M).size = 0) :
    ∀ (Ds : List ℕ) (M : ByteArray), D ∈ Ds → P M → (all w Ds M).size = 0
  | [], _, h, _ => by cases h
  | D0 :: Ds, M, h, hM => by
    rw [all_cons]
    by_cases hz : (w D0 M).size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz]
      rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hD
        exact absurd (hD M hM) hz
      · exact all_found w hw P hP D hD Ds _ h' (hP _ _ (hw D0 M) hM)

theorem stepW_found (ci nxt : ℕ → ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ n e M, Sub (visit n e M) M) (kb : ℕ) {c : Bool} (hc : c = true)
    (P : ByteArray → Prop) (hP : ∀ M' M, Sub M' M → P M → P M') (D : ℕ)
    (hD : ∀ M, P M → (walk ci nxt visit kb D M).size = 0) {l : List ℕ} (hl : D ∈ l)
    {M : ByteArray} (hM : P M) : (stepW ci nxt visit kb c l M).size = 0 := by
  unfold stepW
  rw [if_pos hc]
  exact all_found _ (fun D M' => walk_sub ci nxt visit hv kb D M') P hP D hD l M hl hM

/-! ### Sequences of rows and the rule along them -/

/-- The link of kind `kd` from the block entered at `u` to the block entered at `v`. -/
def LinkK (k kd : ℕ) (u v : List ℕ) : Prop := (kd = 0 → WLink k 3 u v) ∧ (kd = 1 → WLink k 4 u v)

/-- The rows `rest` continue a sequence with last entry `last` whose blocks are `used`: every row
is a row (at most `k - 1` blocks joined by doors), is joined to the block before it by the link of
its kind, and has blocks of new classes. -/
def PCont (k : ℕ) : List ℕ → List (List ℕ) → List TRow → Prop
  | _, _, [] => True
  | _, _, (_, []) :: _ => False
  | last, used, (kd, v :: R) :: rest =>
    R.length ≤ k - 2 ∧ (∀ w ∈ v :: R, PermW k w) ∧ LinkK k kd last v ∧
      List.IsChain (DoorEq k) (v :: R) ∧ (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) ∧
      List.Pairwise (fun a b => ¬ a ~r b) (v :: R) ∧
      PCont k ((v :: R).getLast (List.cons_ne_nil v R)) (used ++ v :: R) rest

/-- The `keep` of a kind of link. -/
def keepK (keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0 => keepN
  | 1 => keepS
  | _ => keepJ

/-- The counter of special links after a link of kind `kd`. -/
def tK (kd t : ℕ) : ℕ := if kd = 0 then t else t + 1

/-- The counter of rows (or of holes) before the row that follows a link of kind `kd`. -/
def rK (rs : Bool) (kd r : ℕ) : ℕ := if kd = 0 then r else (bif rs then 0 else r)

/-- The rule holds along the rows `rest` that continue a sequence with counters `t`, `r`, `d` and
last entry `last`: the sequence and all sequences on the way satisfy the `keep` of the link that
follows, and the sequence at the end is found. -/
def RuleAlong (k : ℕ) (rs : Bool) (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) :
    ℕ → ℕ → ℕ → List ℕ → List TRow → Prop
  | t, r, d, last, [] =>
    bad t r d = true ∨ (badR t r d = true ∧ WLink k 3 last (List.range' 1 k))
  | _, _, _, _, (_, []) :: _ => False
  | t, r, d, _, (kd, v :: R) :: rest =>
    keepK keepN keepS keepJ kd t r d = true ∧
      RuleAlong k rs bad badR keepN keepS keepJ (tK kd t) (rK rs kd r + 1)
        (rK rs kd d + (k - 2 - R.length)) ((v :: R).getLast (List.cons_ne_nil v R)) rest

/-- The same with the fuel and the gate of part `tp` of `nt`: nothing is asked once the fuel has
run out. -/
def PAlong (k : ℕ) (enc : List ℕ → ℕ) (rs : Bool)
    (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) (fg nt tp : ℕ) :
    ℕ → ℕ → ℕ → ℕ → List ℕ → List TRow → Prop
  | 0, _, _, _, _, _ => True
  | _ + 1, t, r, d, last, [] =>
    bad t r d = true ∨ (badR t r d = true ∧ WLink k 3 last (List.range' 1 k))
  | _ + 1, _, _, _, _, (_, []) :: _ => False
  | f + 1, t, r, d, last, (kd, v :: R) :: rest =>
    keepK keepN keepS keepJ kd t r d = true ∧ (f ≠ fg ∨ enc last % nt = tp) ∧
      PAlong k enc rs bad badR keepN keepS keepJ fg nt tp f (tK kd t) (rK rs kd r + 1)
        (rK rs kd d + (k - 2 - R.length)) ((v :: R).getLast (List.cons_ne_nil v R)) rest

variable {rs : Bool} {bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool} {fg nt tp : ℕ}

theorem palong_of_ruleAlong (fg : ℕ) :
    ∀ (rest : List TRow) (fuel t r d : ℕ) (last : List ℕ),
      RuleAlong k rs bad badR keepN keepS keepJ t r d last rest →
      PAlong k enc rs bad badR keepN keepS keepJ fg 1 0 fuel t r d last rest
  | _, 0, _, _, _, _, _ => by simp [PAlong]
  | [], _ + 1, _, _, _, _, h => by simpa [PAlong, RuleAlong] using h
  | (_, []) :: _, _ + 1, _, _, _, _, h => by simp [RuleAlong] at h
  | (kd, v :: R) :: rest, f + 1, t, r, d, last, h => by
    simp only [RuleAlong] at h
    simp only [PAlong]
    exact ⟨h.1, Or.inr (Nat.mod_one _), palong_of_ruleAlong fg rest f _ _ _ _ h.2⟩

/-- Below the depth of the gate every part of the search is the whole search. -/
theorem palong_gate_le (nt tp : ℕ) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (last : List ℕ), fuel ≤ fg →
      PAlong k enc rs bad badR keepN keepS keepJ fg 1 0 fuel t r d last rest →
      PAlong k enc rs bad badR keepN keepS keepJ fg nt tp fuel t r d last rest
  | 0, _, _, _, _, _, _, _ => by simp [PAlong]
  | _ + 1, [], _, _, _, _, _, h => by simpa [PAlong] using h
  | _ + 1, (_, []) :: _, _, _, _, _, _, h => by simp [PAlong] at h
  | f + 1, (kd, v :: R) :: rest, t, r, d, last, hf, h => by
    simp only [PAlong] at h ⊢
    exact ⟨h.1, Or.inl (by omega), palong_gate_le nt tp f rest _ _ _ _ (by omega) h.2.2⟩

/-- A sequence along which the rule holds passes the gate of one of the `nt` parts. -/
theorem palong_gate (hnt : 0 < nt) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (last : List ℕ),
      PAlong k enc rs bad badR keepN keepS keepJ fg 1 0 fuel t r d last rest →
      ∃ tp, tp < nt ∧ PAlong k enc rs bad badR keepN keepS keepJ fg nt tp fuel t r d last rest
  | 0, _, _, _, _, _, _ => ⟨0, hnt, by simp [PAlong]⟩
  | _ + 1, [], _, _, _, _, h => ⟨0, hnt, by simpa [PAlong] using h⟩
  | _ + 1, (_, []) :: _, _, _, _, _, h => by simp [PAlong] at h
  | f + 1, (kd, v :: R) :: rest, t, r, d, last, h => by
    simp only [PAlong] at h
    by_cases hf : f = fg
    · refine ⟨enc last % nt, Nat.mod_lt _ hnt, ?_⟩
      simp only [PAlong]
      refine ⟨h.1, ?_, palong_gate_le nt _ f rest _ _ _ _ (by omega) h.2.2⟩
      right
      first | rfl | trivial
    · obtain ⟨tp, htp, hA⟩ := palong_gate hnt f rest _ _ _ _ h.2.2
      refine ⟨tp, htp, ?_⟩
      simp only [PAlong]
      exact ⟨h.1, Or.inl hf, hA⟩

/-- The search finds the end of a sequence of which it has reached a prefix, if the rule holds
along the rest of the sequence. -/
theorem go_complete (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hid : PermW k (List.range' 1 k)) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (M : ByteArray) (last : List ℕ)
      (used : List (List ℕ)),
      PermW k last → (∀ u ∈ used, PermW k u) → MInv enc ci M used → PCont k last used rest →
      PAlong k enc rs bad badR keepN keepS keepJ fg nt tp fuel t r d last rest →
      (go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel t r d (enc last)
        M).size = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rw [go_zero]
    exact ByteArray.size_empty
  | succ fuel ih =>
    intro rest t r d M last used hlast hused hM hcont halong
    rw [go_succ]
    by_cases hb : (bad t r d || (badR t r d && (s3 (enc last)).contains st)) = true
    · rw [if_pos hb]
      exact ByteArray.size_empty
    · rw [if_neg hb]
      cases rest with
      | nil =>
        exfalso
        apply hb
        simp only [PAlong] at halong
        rcases halong with h | ⟨h1, h2⟩
        · simp [h]
        · have hm := E.s3_mem last _ hlast hid h2
          rw [← E.st_eq] at hm
          simp [h1, hm]
      | cons Q rest' =>
        obtain ⟨kd, Q⟩ := Q
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
          simp only [PAlong] at halong
          obtain ⟨hkeep, hgate, halong'⟩ := halong
          have hc : (fuel != fg || enc last % nt == tp) = true := by
            rcases hgate with h | h <;> simp [h]
          rw [if_pos hc]
          have hv : PermW k v := hperm v List.mem_cons_self
          have hused' : ∀ u ∈ used ++ v :: R, PermW k u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          have hsubg : ∀ (t' r' d' : ℕ) (n e : ℕ) (M'' : ByteArray),
              Sub (go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel t' r'
                (d' + n) e M'') M'' := fun t' r' d' n e M'' => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _
          -- the walk at the first block of the row finds the end, from any table that has
          -- only marks of the sequence so far
          have hwalk : ∀ M', MInv enc ci M' used →
              (walk ci nxt (fun n e M'' =>
                go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (tK kd t)
                  (rK rs kd r + 1) (rK rs kd d + n) e M'') (k - 1) (enc v) M').size = 0 := by
            intro M' hM'
            have h := walk_complete E
              (fun n e M'' =>
                go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (tK kd t)
                  (rK rs kd r + 1) (rK rs kd d + n) e M'')
              (hsubg _ _ _) R (k - 2) v M' used hR hperm hdoor hM' hused hnew hpw
              (by
                intro M'' hM''
                exact ih rest' _ _ _ M'' _ (used ++ v :: R) (hperm _ (List.getLast_mem _)) hused'
                  hM'' hcont' halong')
            rw [show k - 2 + 1 = k - 1 from by omega] at h
            exact h
          have hPsub : ∀ M' M : ByteArray, Sub M' M → MInv enc ci M used → MInv enc ci M' used :=
            fun M' M hs hM => hM.sub hs
          have h1 := stepW_sub ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel t (r + 1)
              (d + n) e M'') (hsubg _ _ _) (k - 1) (keepN t r d) (s3 (enc last)) M
          have h2 := fun X => stepW_sub ci nxt (fun n e M'' =>
            go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
              ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') (hsubg _ _ _)
            (k - 1) (keepS t r d) (s4 (enc last)) X
          match kd, hkeep, hlink, hwalk with
          | 0, hkeep, hlink, hwalk =>
            have hwalk' : ∀ M', MInv enc ci M' used →
                (walk ci nxt (fun n e M'' =>
                  go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel t
                    (r + 1) (d + n) e M'') (k - 1) (enc v) M').size = 0 := by
              simpa [tK, rK] using hwalk
            have hf := stepW_found ci nxt (fun n e M'' =>
                go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel t
                  (r + 1) (d + n) e M'') (hsubg t (r + 1) d) (k - 1) (c := keepN t r d) hkeep
              (fun M' => MInv enc ci M' used) hPsub (enc v) hwalk'
              (E.s3_mem last v hlast hv (hlink.1 rfl)) hM
            rw [if_pos hf]
            exact hf
          | 1, hkeep, hlink, hwalk =>
            have hwalk' : ∀ M', MInv enc ci M' used →
                (walk ci nxt (fun n e M'' =>
                  go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') (k - 1)
                  (enc v) M').size = 0 := by
              simpa [tK, rK] using hwalk
            split_ifs with hz1 hz2
            · exact hz1
            · exact hz2
            · exact absurd (stepW_found ci nxt (fun n e M'' =>
                  go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'')
                (hsubg (t + 1) ((bif rs then 0 else r) + 1) (bif rs then 0 else d)) (k - 1)
                (c := keepS t r d) hkeep
                (fun M' => MInv enc ci M' used) hPsub (enc v) hwalk'
                (E.s4_mem last v hlast hv (hlink.2 rfl)) (hM.sub h1)) hz2
          | kd + 2, hkeep, hlink, hwalk =>
            have hwalk' : ∀ M', MInv enc ci M' used →
                (walk ci nxt (fun n e M'' =>
                  go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') (k - 1)
                  (enc v) M').size = 0 := by
              simpa [tK, rK] using hwalk
            split_ifs with hz1 hz2
            · exact hz1
            · exact hz2
            · exact stepW_found ci nxt (fun n e M'' =>
                  go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'')
                (hsubg (t + 1) ((bif rs then 0 else r) + 1) (bif rs then 0 else d)) (k - 1)
                (c := keepJ t r d) hkeep
                (fun M' => MInv enc ci M' used) hPsub (enc v) hwalk' (E.jl_mem v hv)
                (hM.sub ((h2 _).trans h1))

/-- A part of the search finds a sequence along which the rule holds. -/
theorem searchPart_true (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hid : PermW k (List.range' 1 k)) (sz fuel : ℕ) (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ k - 2) (hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (List.range' 1 k :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 k :: R1))
    (hcont : PCont k ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _))
      (List.range' 1 k :: R1) rest)
    (halong : PAlong k enc rs bad badR keepN keepS keepJ fg nt tp fuel 0 1 (k - 2 - R1.length)
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest) :
    searchPart ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ sz fuel fg nt tp
      = true := by
  have h := walk_complete E
    (fun n e M => go ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ fg nt tp fuel 0 1 n e
      M)
    (fun n e M => go_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) R1 (k - 2)
    (List.range' 1 k) (marks0 sz) [] hR1 hperm hdoor (minv_marks0 enc ci sz) (by simp) (by simp)
    hpw
    (by
      intro M' hM'
      have h := go_complete (rs := rs) (bad := bad) (badR := badR) (keepN := keepN)
        (keepS := keepS) (keepJ := keepJ) (fg := fg) (nt := nt) (tp := tp) E hk hid fuel rest 0 1
        (k - 2 - R1.length) M' _ (List.range' 1 k :: R1) (hperm _ (List.getLast_mem _))
        hperm (by simpa using hM') hcont halong
      exact h)
  rw [show k - 2 + 1 = k - 1 from by omega, ← E.st_eq] at h
  unfold searchPart
  rw [h]
  rfl

/-- The parts evaluated as tasks are the parts. -/
theorem searchPar_false {sz fuel pa pb : ℕ}
    (h : searchPar ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ sz fuel fg nt pa pb
      = false) :
    ∀ tp, pa ≤ tp → tp < pb →
      searchPart ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ sz fuel fg nt tp
        = false := by
  intro tp h1 h2
  unfold searchPar at h
  rw [List.any_map, List.any_eq_false] at h
  have h3 := h (tp - pa) (List.mem_range.mpr (by omega))
  have e : pa + (tp - pa) = tp := by omega
  simpa [Task.spawn, e] using h3

/-- **The search is complete.**  If all `nt` parts answer `false`, the rule does not hold along
any sequence that starts at the word `1 2 … k`. -/
theorem not_ruleAlong_of_search (E : Enc k enc ci nxt s3 s4 jl st) (hk : 2 ≤ k)
    (hid : PermW k (List.range' 1 k)) (hnt : 0 < nt) {sz fuel : ℕ}
    (hs : ∀ tp, tp < nt →
      searchPart ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ sz fuel fg nt tp
        = false)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ k - 2) (hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w)
    (hdoor : List.IsChain (DoorEq k) (List.range' 1 k :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 k :: R1))
    (hcont : PCont k ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _))
      (List.range' 1 k :: R1) rest) :
    ¬ RuleAlong k rs bad badR keepN keepS keepJ 0 1 (k - 2 - R1.length)
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest := by
  intro hA
  obtain ⟨tp, htp, hP⟩ := palong_gate (enc := enc) (fg := fg) hnt fuel rest _ _ _ _
    (palong_of_ruleAlong (enc := enc) fg rest fuel _ _ _ _ hA)
  have h := searchPart_true E hk hid sz fuel R1 rest hR1 hperm hdoor hpw hcont hP
  rw [hs tp htp] at h
  cases h

end Engine

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.not_ruleAlong_of_search

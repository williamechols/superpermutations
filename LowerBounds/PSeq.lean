import LowerBounds.PSound

/-!
# Sequences of rows on words, and what a search proves about them

`IsSeq k L`: a list of rows (`TRow`: the kind of the link before the row, and the entries of its
blocks) on words: every row has between 1 and `k - 1` blocks joined by doors, consecutive rows are
joined by the link of the second row's kind (`0`: the exit overlaps the next entry in `k - 3`
symbols, `1`: in `k - 4` symbols, otherwise nothing is asked), and all blocks lie in different
rotation classes.  The kind of the first row means nothing.

`cnt k rs L` are the counters `(t, r, d)` of the search after the rows `L`.

`PStmt k rs bad badR keepN keepS keepJ`: there is no sequence all of whose non-empty proper
prefixes satisfy the `keep` of the link that follows them and that is `bad`, or `badR` and closed
(`Closes`).  `stmt_of_parts`: a search all of whose parts answer `false` proves this
(for any tables that satisfy `Enc`).  The proof relabels the symbols so that the first entry is
`1 2 … k`, as `pstatement_of_parts` in `DSound.lean`.
-/

namespace SuperpermLowerBounds
namespace PS

open S (PermW WLink DoorEq)

/-- A sequence of rows on words. -/
structure IsSeq (k : ℕ) (L : List TRow) : Prop where
  words : ∀ x ∈ L, ∀ w ∈ x.2, PermW k w
  pieces_ne : ∀ x ∈ L, x.2 ≠ []
  size_le : ∀ x ∈ L, x.2.length ≤ k - 1
  doors : ∀ x ∈ L, List.IsChain (WLink k 2) x.2
  links : List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
    LinkK k y.1 (x.2.getLast hx) (y.2.head hy)) L
  classes : List.Pairwise (fun u v : List ℕ => ¬ u ~r v) (L.map Prod.snd).flatten

variable {k : ℕ}

/-- Every contiguous part of a sequence is a sequence. -/
theorem IsSeq.infix {L L' : List TRow} (h : IsSeq k L) (hi : L' <:+: L) : IsSeq k L' :=
  ⟨fun x hx => h.words x (hi.subset hx), fun x hx => h.pieces_ne x (hi.subset hx),
    fun x hx => h.size_le x (hi.subset hx), fun x hx => h.doors x (hi.subset hx),
    h.links.infix hi, h.classes.sublist (List.Sublist.flatten (hi.sublist.map _))⟩

theorem IsSeq.mem_perm {L : List TRow} (h : IsSeq k L) {w : List ℕ}
    (hw : w ∈ (L.map Prod.snd).flatten) : PermW k w := by
  obtain ⟨P, hP, hwP⟩ := List.mem_flatten.mp hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hP
  exact h.words x hx w hwP

/-- The sequence with every word relabelled. -/
def relabSeq (e : List ℕ) (L : List TRow) : List TRow :=
  L.map fun x => (x.1, x.2.map (List.map (S.relab e)))

theorem LinkK.map {kd : ℕ} {u v : List ℕ} (f : ℕ → ℕ) (h : LinkK k kd u v) :
    LinkK k kd (u.map f) (v.map f) :=
  ⟨fun h0 => (h.1 h0).map f, fun h1 => (h.2 h1).map f⟩

/-- A relabelled sequence is a sequence. -/
theorem IsSeq.relabel {e : List ℕ} (he : PermW k e) {L : List TRow} (h : IsSeq k L) :
    IsSeq k (relabSeq e L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    exact he.map_relab (h.words x0 hx0 w0 hw0)
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    simpa using h.pieces_ne x0 hx0
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    simpa using h.size_le x0 hx0
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    show List.IsChain (WLink k 2) (x0.2.map (List.map (S.relab e)))
    rw [List.isChain_map]
    exact (h.doors x0 hx0).imp (fun a b hab => hab.map _)
  · unfold relabSeq
    rw [List.isChain_map]
    refine h.links.imp ?_
    intro x y hxy hx hy
    have hx0 : x.2 ≠ [] := by simpa using hx
    have hy0 : y.2 ≠ [] := by simpa using hy
    show LinkK k y.1 ((x.2.map (List.map (S.relab e))).getLast hx)
      ((y.2.map (List.map (S.relab e))).head hy)
    rw [List.getLast_map, List.head_map]
    exact (hxy hx0 hy0).map _
  · have e1 : (relabSeq e L).map Prod.snd
        = (L.map Prod.snd).map (List.map (List.map (S.relab e))) := by
      simp [relabSeq, List.map_map, Function.comp_def]
    rw [e1, ← List.map_flatten, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ h.classes
    intro a b ha hb hab
    exact S.not_isRotated_map_relab he (h.mem_perm ha) (h.mem_perm hb) hab

/-- The rows after the first row of a sequence continue it. -/
theorem pcont_of_seq (hk : 3 ≤ k) : ∀ (rest : List TRow) (x : TRow) (used : List (List ℕ))
    (hx : x.2 ≠ []), IsSeq k (x :: rest) →
    (∀ u ∈ used, ∀ w ∈ (rest.map Prod.snd).flatten, ¬ u ~r w) →
    PCont k (x.2.getLast hx) used rest
  | [], _, _, _, _, _ => trivial
  | (kd, Q) :: rest', x, used, hx, h, hnew => by
    have hQne : Q ≠ [] := h.pieces_ne (kd, Q) (by simp)
    obtain ⟨v, R, rfl⟩ := List.exists_cons_of_ne_nil hQne
    have hperm : ∀ w ∈ v :: R, PermW k w := h.words (kd, v :: R) (by simp)
    have hsz := h.size_le (kd, v :: R) (by simp)
    have hlink : LinkK k kd (x.2.getLast hx) v :=
      (List.isChain_cons_cons.mp h.links).1 hx (List.cons_ne_nil v R)
    have hcl : List.Pairwise (fun a b => ¬ a ~r b)
        (x.2 ++ ((v :: R) ++ (rest'.map Prod.snd).flatten)) := by
      have := h.classes
      simp only [List.map_cons, List.flatten_cons] at this
      exact this
    have hcl3 := List.pairwise_append.mp (List.pairwise_append.mp hcl).2.1
    have htail : IsSeq k ((kd, v :: R) :: rest') := h.infix ⟨[x], [], by simp⟩
    refine ⟨by simp only [List.length_cons] at hsz; omega, hperm, hlink,
      S.door_chain hk _ hperm (h.doors (kd, v :: R) (by simp)) hcl3.1, ?_, hcl3.1, ?_⟩
    · intro u hu w hw
      exact hnew u hu w (by
        simp only [List.map_cons, List.flatten_cons]
        exact List.mem_append_left _ hw)
    · apply pcont_of_seq hk rest' (kd, v :: R) (used ++ v :: R) (List.cons_ne_nil v R) htail
      intro u hu w hw
      rcases List.mem_append.mp hu with hu' | hu'
      · exact hnew u hu' w (by
          simp only [List.map_cons, List.flatten_cons]
          exact List.mem_append_right _ hw)
      · exact hcl3.2.2 u hu' w hw

/-! ### Counters -/

/-- A rule function applied to a triple of counters. -/
def ap (f : ℕ → ℕ → ℕ → Bool) (c : ℕ × ℕ × ℕ) : Bool := f c.1 c.2.1 c.2.2

/-- The counters after one more row. -/
def stepC (k : ℕ) (rs : Bool) (c : ℕ × ℕ × ℕ) (x : TRow) : ℕ × ℕ × ℕ :=
  (tK x.1 c.1, rK rs x.1 c.2.1 + 1, rK rs x.1 c.2.2 + (k - 1 - x.2.length))

/-- The counters `(t, r, d)` of the search after the rows `L`. -/
def cnt (k : ℕ) (rs : Bool) : List TRow → ℕ × ℕ × ℕ
  | [] => (0, 0, 0)
  | x :: u => u.foldl (stepC k rs) (0, 1, k - 1 - x.2.length)

/-- The last block after the rows `rest` (`last` if there is none). -/
def lastW (last : List ℕ) : List TRow → List ℕ
  | [] => last
  | x :: rest => lastW (x.2.getLast?.getD last) rest

theorem cnt_relab (rs : Bool) (e : List ℕ) (L : List TRow) :
    cnt k rs (relabSeq e L) = cnt k rs L := by
  cases L with
  | nil => rfl
  | cons x u =>
    show (List.map _ u).foldl (stepC k rs) _ = u.foldl (stepC k rs) _
    rw [List.foldl_map]
    simp only [stepC, List.length_map]
    rfl

/-- From the hypotheses on prefixes to the rule along the rows. -/
theorem ruleAlong_of_prefix (rs : Bool) (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) :
    ∀ (rest : List TRow) (c : ℕ × ℕ × ℕ) (last : List ℕ),
      (∀ x ∈ rest, x.2 ≠ []) →
      (∀ u x w, rest = u ++ x :: w →
        ap (keepK keepN keepS keepJ x.1) (u.foldl (stepC k rs) c) = true) →
      (ap bad (rest.foldl (stepC k rs) c) = true ∨
        (ap badR (rest.foldl (stepC k rs) c) = true ∧
          WLink k 3 (lastW last rest) (List.range' 1 k))) →
      RuleAlong k rs bad badR keepN keepS keepJ c.1 c.2.1 c.2.2 last rest
  | [], c, last, _, _, hbad => by
    simpa [RuleAlong, lastW, ap] using hbad
  | (kd, []) :: rest, c, last, hne, _, _ => absurd rfl (hne (kd, []) List.mem_cons_self)
  | (kd, v :: R) :: rest, c, last, hne, hkeep, hbad => by
    have e : stepC k rs c (kd, v :: R)
        = (tK kd c.1, rK rs kd c.2.1 + 1, rK rs kd c.2.2 + (k - 2 - R.length)) := by
      simp only [stepC, List.length_cons, Prod.mk.injEq, true_and]
      omega
    have h := ruleAlong_of_prefix rs bad badR keepN keepS keepJ rest (stepC k rs c (kd, v :: R))
      ((v :: R).getLast (List.cons_ne_nil v R))
      (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      (fun u x w huw => hkeep ((kd, v :: R) :: u) x w (by rw [huw]; rfl))
      (by
        have e2 : lastW last ((kd, v :: R) :: rest)
            = lastW ((v :: R).getLast (List.cons_ne_nil v R)) rest := by
          show lastW ((v :: R).getLast?.getD last) rest = _
          rw [List.getLast?_eq_some_getLast (List.cons_ne_nil v R)]
          rfl
        rw [e2] at hbad
        exact hbad)
    rw [e] at h
    exact ⟨hkeep [] (kd, v :: R) rest rfl, h⟩

/-! ### The statement about sequences -/

/-- The last block of the sequence and its first block are joined by a link of weight 3. -/
def Closes (k : ℕ) (L : List TRow) : Prop :=
  ∀ u ∈ L.getLast?.bind (fun x => x.2.getLast?), ∀ v ∈ L.head?.bind (fun x => x.2.head?),
    WLink k 3 u v

/-- No sequence all of whose non-empty proper prefixes satisfy the `keep` of the link that
follows them is `bad`, or `badR` and closed. -/
def PStmt (k : ℕ) (rs : Bool) (bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool) : Prop :=
  ∀ L : List TRow, IsSeq k L → L ≠ [] →
    (∀ u x w, L = u ++ x :: w → u ≠ [] →
      ap (keepK keepN keepS keepJ x.1) (cnt k rs u) = true) →
    ap bad (cnt k rs L) = false ∧ (ap badR (cnt k rs L) = true → ¬ Closes k L)

theorem lastBlock_eq : ∀ (rest : List TRow) (x : TRow) (hx : x.2 ≠ []),
    (∀ y ∈ rest, y.2 ≠ []) →
    (x :: rest).getLast?.bind (fun y => y.2.getLast?) = some (lastW (x.2.getLast hx) rest)
  | [], x, hx, _ => by
    show x.2.getLast? = some (x.2.getLast hx)
    exact List.getLast?_eq_some_getLast hx
  | y :: rest, x, hx, hne => by
    have hy : y.2 ≠ [] := hne y List.mem_cons_self
    rw [List.getLast?_cons_cons, lastBlock_eq rest y hy (fun z hz => hne z (List.mem_cons_of_mem _ hz))]
    show _ = some (lastW (y.2.getLast?.getD (x.2.getLast hx)) rest)
    rw [List.getLast?_eq_some_getLast hy]
    rfl

/-- **A search all of whose parts answer `false` proves the statement.** -/
theorem stmt_of_parts {enc : List ℕ → ℕ} {ci nxt : ℕ → ℕ} {s3 s4 : ℕ → List ℕ} {jl : List ℕ}
    {st : ℕ} {rs : Bool} {bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool} {sz fuel fg nt : ℕ}
    (E : Enc k enc ci nxt s3 s4 jl st) (hk : 3 ≤ k) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt →
      searchPart ci nxt s3 s4 jl st (k - 1) rs bad badR keepN keepS keepJ sz fuel fg nt tp
        = false) :
    PStmt k rs bad badR keepN keepS keepJ := by
  intro L hL hne hkeep
  by_contra hcon
  have hbad : ap bad (cnt k rs L) = true ∨ (ap badR (cnt k rs L) = true ∧ Closes k L) := by
    by_contra h
    apply hcon
    rw [not_or] at h
    refine ⟨by simpa using h.1, fun hb hc => h.2 ⟨hb, hc⟩⟩
  cases L with
  | nil => exact hne rfl
  | cons x0 rest0 =>
    obtain ⟨kd0, Q0⟩ := x0
    have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
    obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    have hv0 : PermW k v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
    have hL' := hL.relabel hv0
    -- the hypotheses, for the relabelled sequence
    have hkeep' : ∀ u x w, relabSeq v0 ((kd0, v0 :: R0) :: rest0) = u ++ x :: w → u ≠ [] →
        ap (keepK keepN keepS keepJ x.1) (cnt k rs u) = true := by
      intro u x w huw hu
      obtain ⟨u0, L2, e0, hu0, hL2⟩ := List.map_eq_append_iff.mp huw
      obtain ⟨x1, w1, e1, hx1, _⟩ := List.map_eq_cons_iff.mp hL2
      have h := hkeep u0 x1 w1 (by rw [e0, e1]) (by
        rintro rfl
        exact hu hu0.symm)
      have ec : cnt k rs u = cnt k rs u0 := by
        rw [← hu0]
        exact cnt_relab rs v0 u0
      rw [ec, ← hx1]
      exact h
    have hbad' : ap bad (cnt k rs (relabSeq v0 ((kd0, v0 :: R0) :: rest0))) = true ∨
        (ap badR (cnt k rs (relabSeq v0 ((kd0, v0 :: R0) :: rest0))) = true ∧
          Closes k (relabSeq v0 ((kd0, v0 :: R0) :: rest0))) := by
      rw [cnt_relab]
      rcases hbad with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        intro u hu v hv
        unfold relabSeq at hu hv
        rw [List.getLast?_map] at hu
        rw [List.head?_map] at hv
        simp only [Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hu hv
        obtain ⟨y, ⟨y0, hy0, rfl⟩, hyu⟩ := hu
        obtain ⟨z, ⟨z0, hz0, rfl⟩, hzv⟩ := hv
        rw [List.getLast?_map] at hyu
        rw [List.head?_map] at hzv
        simp only [Option.map_eq_some_iff] at hyu hzv
        obtain ⟨u0, hu0, rfl⟩ := hyu
        obtain ⟨w0, hw0, rfl⟩ := hzv
        exact (h2 u0 (by simp [hy0, hu0]) w0 (by simp [hz0, hw0])).map _
    have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
        (kd0, List.range' 1 k :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
      simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
    rw [hshape] at hL' hkeep' hbad'
    generalize R0.map (List.map (S.relab v0)) = R1 at hL' hkeep' hbad'
    generalize relabSeq v0 rest0 = rest1 at hL' hkeep' hbad'
    have hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w :=
      hL'.words (kd0, List.range' 1 k :: R1) List.mem_cons_self
    have hcl : List.Pairwise (fun a b => ¬ a ~r b)
        ((List.range' 1 k :: R1) ++ (rest1.map Prod.snd).flatten) := by
      have := hL'.classes
      simp only [List.map_cons, List.flatten_cons] at this
      exact this
    have hcl' := List.pairwise_append.mp hcl
    have hsz := hL'.size_le (kd0, List.range' 1 k :: R1) List.mem_cons_self
    have hR1 : R1.length ≤ k - 2 := by
      simp only [List.length_cons] at hsz
      omega
    have hdoor := S.door_chain hk _ hperm
      (hL'.doors (kd0, List.range' 1 k :: R1) List.mem_cons_self) hcl'.1
    have hcont := pcont_of_seq hk rest1 (kd0, List.range' 1 k :: R1) (List.range' 1 k :: R1)
      (List.cons_ne_nil _ _) hL' hcl'.2.2
    have hne1 : ∀ y ∈ rest1, y.2 ≠ [] :=
      fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)
    have ec : (0, 1, k - 1 - (List.range' 1 k :: R1).length) = (0, 1, k - 2 - R1.length) := by
      simp only [List.length_cons, Prod.mk.injEq, true_and]
      omega
    have hA := ruleAlong_of_prefix (k := k) rs bad badR keepN keepS keepJ rest1
      (0, 1, k - 2 - R1.length)
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) hne1
      (by
        intro u x w huw
        have h := hkeep' ((kd0, List.range' 1 k :: R1) :: u) x w (by rw [huw]; rfl) (by simp)
        have e2 : cnt k rs ((kd0, List.range' 1 k :: R1) :: u)
            = u.foldl (stepC k rs) (0, 1, k - 1 - (List.range' 1 k :: R1).length) := rfl
        rw [e2, ec] at h
        exact h)
      (by
        have e2 : cnt k rs ((kd0, List.range' 1 k :: R1) :: rest1)
            = rest1.foldl (stepC k rs) (0, 1, k - 1 - (List.range' 1 k :: R1).length) := rfl
        rw [e2, ec] at hbad'
        rcases hbad' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · refine Or.inr ⟨h1, ?_⟩
          have hl := lastBlock_eq rest1 (kd0, List.range' 1 k :: R1) (List.cons_ne_nil _ _) hne1
          exact h2 _ (by rw [hl]; rfl) (List.range' 1 k) (by simp))
    exact not_ruleAlong_of_search E (by omega) (hperm _ List.mem_cons_self) hnt hs R1 rest1 hR1
      hperm hdoor hcl'.1 hcont hA

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.stmt_of_parts

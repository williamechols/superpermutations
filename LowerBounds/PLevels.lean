import LowerBounds.PEnc

/-!
# The three kinds of rules are complete (the written proof, section 8), for sequences on words

* `seqCap_level` (8.1): the statement `PStmt` for the rule `seqBad`, `seqKeepN`, `seqKeepS` on the
  levels `lo … hi` gives the cap for sequences with `s` links of weight 4 and at most `hi` holes,
  given the caps for fewer links and the cap below `lo` (shortest counterexample).
* `ringCap_of_stmt` (8.2): the statement for `ringBad`, `ringKeep` gives the ring cap, given the
  chain cap (cycle lemma `cycle_lemma`, rotation of a ring `isSeq_rotate`).
* `prof_rule` (8.3): along a list of chains with exactly the rows of their targets, each within
  its holes and with every rest of a chain within the chain cap, the rule `profBad`, `profKeepN`,
  `profKeepJ` holds.
-/

namespace SuperpermLowerBounds
namespace PS

open S (PermW WLink)

variable {k : ℕ}

/-! ### Rows, holes and links of a sequence -/

/-- The number of holes of a list of rows. -/
def holesT (k : ℕ) (L : List TRow) : ℕ := (L.map fun x => k - 1 - x.2.length).sum

/-- The number of special links of a list of rows (the kind of the first row does not count). -/
def linksT (L : List TRow) : ℕ := L.tail.countP fun x => x.1 != 0

theorem holesT_nil : holesT k [] = 0 := rfl

theorem holesT_cons (x : TRow) (L : List TRow) :
    holesT k (x :: L) = (k - 1 - x.2.length) + holesT k L := by
  simp [holesT]

theorem holesT_append (A B : List TRow) : holesT k (A ++ B) = holesT k A + holesT k B := by
  simp [holesT]

theorem bne_if (n : ℕ) : (if (n != 0) = true then 1 else 0) = (if n = 0 then 0 else 1) := by
  by_cases h : n = 0 <;> simp [h]

theorem linksT_append (u : List TRow) (x : TRow) (w : List TRow) (hu : u ≠ []) :
    linksT (u ++ x :: w) = linksT u + (if x.1 = 0 then 0 else 1) + linksT (x :: w) := by
  obtain ⟨y, u', rfl⟩ := List.exists_cons_of_ne_nil hu
  show (u' ++ x :: w).countP _ = u'.countP _ + _ + w.countP _
  rw [List.countP_append, List.countP_cons, bne_if]
  generalize (if x.1 = 0 then 0 else 1) = z
  omega

theorem tK_eq (kd t : ℕ) : tK kd t = t + (if kd = 0 then 0 else 1) := by
  unfold tK
  split_ifs <;> rfl

theorem rK_false (kd r : ℕ) : rK false kd r = r := by
  unfold rK
  split_ifs <;> rfl

theorem rK_zero (rs : Bool) (r : ℕ) : rK rs 0 r = r := by
  unfold rK
  rfl

/-- The counters without restart. -/
theorem foldl_stepC_false : ∀ (u : List TRow) (c : ℕ × ℕ × ℕ),
    u.foldl (stepC k false) c
      = (c.1 + u.countP (fun x => x.1 != 0), c.2.1 + u.length, c.2.2 + holesT k u)
  | [], c => by simp [holesT]
  | x :: u, c => by
    rw [List.foldl_cons, foldl_stepC_false u, List.countP_cons, holesT_cons, bne_if]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show tK x.1 c.1 + u.countP _ = c.1 + (u.countP _ + if x.1 = 0 then 0 else 1)
      rw [tK_eq]
      generalize (if x.1 = 0 then 0 else 1) = z
      omega
    · show rK false x.1 c.2.1 + 1 + u.length = c.2.1 + (x :: u).length
      rw [rK_false, List.length_cons]
      omega
    · show rK false x.1 c.2.2 + (k - 1 - x.2.length) + holesT k u
        = c.2.2 + (k - 1 - x.2.length + holesT k u)
      rw [rK_false]
      omega

theorem cnt_false {L : List TRow} (hL : L ≠ []) :
    cnt k false L = (linksT L, L.length, holesT k L) := by
  obtain ⟨x, u, rfl⟩ := List.exists_cons_of_ne_nil hL
  show u.foldl (stepC k false) (0, 1, k - 1 - x.2.length) = _
  rw [foldl_stepC_false, holesT_cons]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show 0 + u.countP _ = u.countP _
    omega
  · show 1 + u.length = (x :: u).length
    rw [List.length_cons]
    omega
  · rfl

/-! ### 8.1: sequences with `s` links of weight 4, by levels -/

/-- Every sequence with exactly `s` links of weight 4 (and no jump) and fewer than `b` holes has
at most `P (holes)` rows. -/
def SeqCapLt (k s : ℕ) (P : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ L : List TRow, IsSeq k L → (∀ x ∈ L, x.1 ≤ 1) → linksT L = s → holesT k L < b →
    L.length ≤ P (holesT k L)

/-- **Shortest counterexample, by levels.** -/
theorem seqCap_level {caps : List (List ℕ)} {s lo hi : ℕ}
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hst : PStmt k false (seqBad caps s lo hi) noRule (seqKeepN caps s lo hi)
      (seqKeepS caps s lo hi) noRule) :
    SeqCapLt k s (capF caps s) (hi + 1) := by
  suffices hmain : ∀ n : ℕ, ∀ L : List TRow, L.length = n → IsSeq k L → (∀ x ∈ L, x.1 ≤ 1) →
      linksT L = s → holesT k L < hi + 1 → L.length ≤ capF caps s (holesT k L) from
    fun L h1 h2 h3 h4 => hmain L.length L rfl h1 h2 h3 h4
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL htag hlinks hholes
    by_cases hlo : holesT k L < lo
    · exact hprev L hL htag hlinks hlo
    by_cases hne : L = []
    · subst hne
      simp
    by_contra hnb
    have hkeep : ∀ u x w, L = u ++ x :: w → u ≠ [] →
        ap (keepK (seqKeepN caps s lo hi) (seqKeepS caps s lo hi) noRule x.1) (cnt k false u)
          = true := by
      intro u x w huw hu
      rw [cnt_false hu]
      have hB : IsSeq k (x :: w) := hL.infix ⟨u, [], by simp [huw]⟩
      have hBtag : ∀ y ∈ x :: w, y.1 ≤ 1 :=
        fun y hy => htag y (by rw [huw]; exact List.mem_append_right _ hy)
      have hlen2 : L.length = u.length + (x :: w).length := by rw [huw, List.length_append]
      have hh : holesT k L = holesT k u + holesT k (x :: w) := by rw [huw, holesT_append]
      have hl := linksT_append u x w hu
      rw [← huw, hlinks] at hl
      have hupos : 0 < u.length := List.length_pos_iff.mpr hu
      have hx1 : x.1 ≤ 1 := htag x (by rw [huw]; simp)
      have hBcap : (x :: w).length ≤ capF caps (linksT (x :: w)) (holesT k (x :: w)) := by
        by_cases hsB : linksT (x :: w) < s
        · exact hlow _ hsB (x :: w) hB hBtag rfl (by omega)
        · have hs : linksT (x :: w) = s := by
            split_ifs at hl <;> omega
          have h := ih (x :: w).length (by omega) (x :: w) rfl hB hBtag hs (by omega)
          rw [hs]
          exact h
      obtain ⟨kd, Q⟩ := x
      simp only at hx1 hl
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx1 with rfl | rfl
      · rw [if_pos rfl] at hl
        show seqKeepN caps s lo hi (linksT u) u.length (holesT k u) = true
        simp only [seqKeepN, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range]
        refine ⟨by omega, holesT k L, by omega, ⟨by omega, by omega⟩, ?_⟩
        have e1 : s - linksT u = linksT ((0, Q) :: w) := by omega
        have e2 : holesT k L - holesT k u = holesT k ((0, Q) :: w) := by omega
        rw [e1, e2]
        omega
      · rw [if_neg (by decide)] at hl
        show seqKeepS caps s lo hi (linksT u) u.length (holesT k u) = true
        simp only [seqKeepS, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range]
        refine ⟨by omega, holesT k L, by omega, ⟨by omega, by omega⟩, ?_⟩
        have e1 : s - linksT u - 1 = linksT ((1, Q) :: w) := by omega
        have e2 : holesT k L - holesT k u = holesT k ((1, Q) :: w) := by omega
        rw [e1, e2]
        omega
    have hb : ap (seqBad caps s lo hi) (cnt k false L) = true := by
      rw [cnt_false hne]
      simp only [ap, seqBad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨hlinks, by omega⟩, by omega⟩, by omega⟩
    rw [(hst L hL hne hkeep).1] at hb
    cases hb

/-! ### 8.2: rings -/

/-- The excess of a list over the line through the whole list (`T` rows, `H` holes). -/
def cycF {α : Type} (h : α → ℕ) (T H : ℕ) (u : List α) : ℤ :=
  ((u.map h).sum : ℤ) * T - (u.length : ℤ) * H

theorem cycF_append {α : Type} (h : α → ℕ) (T H : ℕ) (u v : List α) :
    cycF h T H (u ++ v) = cycF h T H u + cycF h T H v := by
  simp only [cycF, List.map_append, List.sum_append, List.length_append, Nat.cast_add]
  ring

theorem exists_max_le (f : ℕ → ℤ) : ∀ n : ℕ, ∃ i, i ≤ n ∧ ∀ j, j ≤ n → f j ≤ f i
  | 0 => ⟨0, le_refl 0, fun j hj => by rw [Nat.le_zero.mp hj]⟩
  | n + 1 => by
    obtain ⟨i, hi, hmax⟩ := exists_max_le f n
    by_cases h : f i ≤ f (n + 1)
    · refine ⟨n + 1, le_refl _, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (n + 1) with h1 | h1
      · exact le_trans (hmax j (by omega)) h
      · have e : j = n + 1 := by omega
        rw [e]
    · refine ⟨i, by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (n + 1) with h1 | h1
      · exact hmax j (by omega)
      · have e : j = n + 1 := by omega
        rw [e]
        omega

/-- **Cycle lemma.**  A list has a rotation all of whose prefixes have at most their share of
the total weight. -/
theorem cycle_lemma {α : Type} (h : α → ℕ) (L : List α) :
    ∃ A B, L = A ++ B ∧ ∀ u w, B ++ A = u ++ w →
      (u.map h).sum * L.length ≤ u.length * (L.map h).sum := by
  obtain ⟨i, _, hmax⟩ := exists_max_le
    (fun i => cycF h L.length (L.map h).sum (L.take i)) L.length
  have hL0 : cycF h L.length (L.map h).sum L = 0 := by
    simp only [cycF]
    ring
  have hpre : ∀ p q : List α, L = p ++ q →
      cycF h L.length (L.map h).sum p ≤ cycF h L.length (L.map h).sum (L.take i) := by
    intro p q hpq
    have hp : L.take p.length = p := by
      rw [hpq]
      exact List.take_left
    have hlen : p.length ≤ L.length := by
      rw [hpq, List.length_append]
      omega
    have := hmax p.length hlen
    rw [hp] at this
    exact this
  refine ⟨L.take i, L.drop i, (List.take_append_drop i L).symm, ?_⟩
  intro u w huw
  have hsplit := cycF_append h L.length (L.map h).sum (L.take i) (L.drop i)
  rw [List.take_append_drop, hL0] at hsplit
  have key : cycF h L.length (L.map h).sum u ≤ 0 := by
    rcases List.append_eq_append_iff.mp huw with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · -- `u` is the second part followed by a prefix of the first part
      have hp := hpre a' (w ++ L.drop i) (by
        rw [← List.append_assoc, ← h2, List.take_append_drop])
      rw [h1, cycF_append]
      omega
    · -- `u` is a prefix of the second part
      have hp := hpre (L.take i ++ u) c' (by
        rw [List.append_assoc, ← h1, List.take_append_drop])
      rw [cycF_append] at hp
      omega
  simp only [cycF] at key
  have key2 : ((u.map h).sum : ℤ) * L.length ≤ (u.length : ℤ) * (L.map h).sum := by omega
  exact_mod_cast key2

theorem linkK_zero {u v : List ℕ} (h : WLink k 3 u v) : LinkK k 0 u v :=
  ⟨fun _ => h, fun h1 => absurd h1 (by decide)⟩

/-- A ring read from its second row is a ring. -/
theorem isSeq_rotate_one {a : TRow} {R : List TRow} (h : IsSeq k (a :: R))
    (h0 : ∀ x ∈ a :: R, x.1 = 0) (hc : Closes k (a :: R)) :
    IsSeq k (R ++ [a]) ∧ Closes k (R ++ [a]) := by
  cases R with
  | nil => exact ⟨h, hc⟩
  | cons b R' =>
    have ha : a.2 ≠ [] := h.pieces_ne a List.mem_cons_self
    have hb : b.2 ≠ [] := h.pieces_ne b (by simp)
    have hmem : ∀ x, x ∈ (b :: R') ++ [a] → x ∈ a :: b :: R' := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ hx
      · rw [List.mem_singleton.mp hx]
        exact List.mem_cons_self
    have hlinks := List.isChain_cons_cons.mp h.links
    refine ⟨⟨fun x hx => h.words x (hmem x hx), fun x hx => h.pieces_ne x (hmem x hx),
      fun x hx => h.size_le x (hmem x hx), fun x hx => h.doors x (hmem x hx), ?_, ?_⟩, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hlinks.2, List.isChain_singleton _, ?_⟩
      intro x hx y hy hx' hy'
      have hy2 : y = a := by simpa using hy.symm
      subst hy2
      rw [h0 y List.mem_cons_self]
      apply linkK_zero
      apply hc
      · have e : (y :: b :: R').getLast? = (b :: R').getLast? := List.getLast?_cons_cons
        rw [e, Option.mem_def.mp hx]
        exact List.getLast?_eq_some_getLast hx'
      · show y.2.head hy' ∈ y.2.head?
        rw [List.head?_eq_some_head hy']
        rfl
    · have hp : (((b :: R') ++ [a]).map Prod.snd).flatten.Perm
          (((a :: b :: R').map Prod.snd)).flatten :=
        ((List.perm_append_comm (l₁ := b :: R') (l₂ := [a])).map Prod.snd).flatten
      exact (hp.pairwise_iff (fun {x y} (hxy : ¬ x ~r y) hr => hxy hr.symm)).mpr h.classes
    · intro u hu v hv
      have e1 : ((b :: R') ++ [a]).getLast? = some a := by
        rw [List.getLast?_append]
        rfl
      have e2 : ((b :: R') ++ [a]).head? = some b := rfl
      rw [e1] at hu
      rw [e2] at hv
      have hu' : u = a.2.getLast ha := by
        have : a.2.getLast? = some u := hu
        rw [List.getLast?_eq_some_getLast ha] at this
        exact (Option.some.inj this).symm
      have hv' : v = b.2.head hb := by
        have : b.2.head? = some v := hv
        rw [List.head?_eq_some_head hb] at this
        exact (Option.some.inj this).symm
      rw [hu', hv']
      exact (hlinks.1 ha hb).1 (h0 b (by simp))

/-- A ring read from any row is a ring. -/
theorem isSeq_rotate : ∀ (A B : List TRow), IsSeq k (A ++ B) → (∀ x ∈ A ++ B, x.1 = 0) →
    Closes k (A ++ B) → IsSeq k (B ++ A) ∧ Closes k (B ++ A)
  | [], B, h, _, hc => by
    rw [List.append_nil]
    exact ⟨h, hc⟩
  | a :: A', B, h, h0, hc => by
    obtain ⟨h1, hc1⟩ := isSeq_rotate_one (R := A' ++ B) h h0 hc
    rw [List.append_assoc] at h1 hc1
    have h01 : ∀ x ∈ A' ++ (B ++ [a]), x.1 = 0 := by
      intro x hx
      apply h0
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
    have h2 := isSeq_rotate A' (B ++ [a]) h1 h01 hc1
    rw [List.append_assoc] at h2
    exact h2

/-- Every ring on words with at most `G` holes has at most `PR (holes)` rows. -/
def RingCapT (k : ℕ) (PR : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ L : List TRow, IsSeq k L → (∀ x ∈ L, x.1 = 0) → 2 ≤ L.length → Closes k L →
    holesT k L ≤ G → L.length ≤ PR (holesT k L)

theorem linksT_zero {L : List TRow} (h0 : ∀ x ∈ L, x.1 = 0) : linksT L = 0 := by
  unfold linksT
  rw [List.countP_eq_zero]
  intro x hx
  simp [h0 x (List.mem_of_mem_tail hx)]

/-- **The ring rule is complete**, given the chain cap. -/
theorem ringCap_of_stmt {M PR : List ℕ} {G : ℕ}
    (hM : SeqCapLt k 0 (fun x => M.getD x 0) (G + 1))
    (hst : PStmt k false noRule (ringBad PR G) (ringKeep M PR G) noRule noRule) :
    RingCapT k (fun x => PR.getD x 0) G := by
  intro L hL h0 h2 hc hG
  by_contra hnb0
  have hnb : PR.getD (holesT k L) 0 < L.length := Nat.lt_of_not_le hnb0
  obtain ⟨A, B, hAB, hcyc⟩ := cycle_lemma (fun x : TRow => k - 1 - x.2.length) L
  subst hAB
  obtain ⟨hL', hc'⟩ := isSeq_rotate A B hL h0 hc
  have h0' : ∀ x ∈ B ++ A, x.1 = 0 := by
    intro x hx
    apply h0
    simp only [List.mem_append] at hx ⊢
    tauto
  have hlen : (B ++ A).length = (A ++ B).length := by
    simp only [List.length_append]
    omega
  have hhol : holesT k (B ++ A) = holesT k (A ++ B) := by
    rw [holesT_append, holesT_append]
    omega
  have hne : B ++ A ≠ [] := by
    intro e
    rw [e] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hcapL : (A ++ B).length ≤ M.getD (holesT k (A ++ B)) 0 :=
    hM (A ++ B) hL (fun x hx => by rw [h0 x hx]; omega) (linksT_zero h0) (by omega)
  have hkeep : ∀ u x w, B ++ A = u ++ x :: w → u ≠ [] →
      ap (keepK (ringKeep M PR G) noRule noRule x.1) (cnt k false u) = true := by
    intro u x w huw hu
    rw [cnt_false hu]
    have hx0 : x.1 = 0 := h0' x (by rw [huw]; simp)
    have hB : IsSeq k (x :: w) := hL'.infix ⟨u, [], by simp [huw]⟩
    have hB0 : ∀ y ∈ x :: w, y.1 = 0 :=
      fun y hy => h0' y (by rw [huw]; exact List.mem_append_right _ hy)
    have hlen2 : (A ++ B).length = u.length + (x :: w).length := by
      rw [← hlen, huw, List.length_append]
    have hh : holesT k (A ++ B) = holesT k u + holesT k (x :: w) := by
      rw [← hhol, huw, holesT_append]
    have hBcap : (x :: w).length ≤ M.getD (holesT k (x :: w)) 0 :=
      hM (x :: w) hB (fun y hy => by rw [hB0 y hy]; omega) (linksT_zero hB0) (by omega)
    have hcy := hcyc u (x :: w) huw
    obtain ⟨kd, Q⟩ := x
    simp only at hx0
    subst hx0
    show ringKeep M PR G (linksT u) u.length (holesT k u) = true
    simp only [ringKeep, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    refine ⟨holesT k (A ++ B), by omega, by omega, (A ++ B).length, by omega,
      ⟨⟨by omega, ?_⟩, hcy⟩, ?_⟩
    · simp only [List.length_cons] at hlen2
      omega
    · have e2 : holesT k (A ++ B) - holesT k u = holesT k ((0, Q) :: w) := by omega
      rw [e2]
      omega
  have hb : ap (ringBad PR G) (cnt k false (B ++ A)) = true := by
    rw [cnt_false hne, hlen, hhol]
    simp only [ap, ringBad, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h2, hG⟩, by omega⟩
  exact (hst (B ++ A) hL' hne hkeep).2 hb hc'

/-! ### 8.3: profiles -/

/-- What is left of a list of chains with targets `ts`, when the search is at counters `c` (chain
number `c.1`, `c.2.1` of its rows placed): the rest `rem` of the current chain, then the chains
`Ds`, each beginning with a jump.  Every chain has exactly the rows of its target, at most its
holes, and every rest of a chain obeys the chain cap `M`. -/
def ProfInv (k : ℕ) (M : List ℕ) (ts : List (ℕ × ℕ)) (c : ℕ × ℕ × ℕ) (rest : List TRow) : Prop :=
  ∃ (rem : List TRow) (Ds : List (List TRow)),
    rest = rem ++ Ds.flatten ∧ (∀ y ∈ rem, y.1 = 0) ∧
    c.1 + 1 + Ds.length = ts.length ∧
    c.2.1 + rem.length = (ts.getD c.1 (0, 0)).1 ∧
    c.2.2 + holesT k rem ≤ (ts.getD c.1 (0, 0)).2 ∧
    (∀ a b, rem = a ++ b → b.length ≤ M.getD (holesT k b) 0) ∧
    List.Forall₂ (fun (D : List TRow) (t : ℕ × ℕ) => ∃ P z, D = (2, P) :: z ∧ (∀ y ∈ z, y.1 = 0) ∧
      D.length = t.1 ∧ holesT k D ≤ t.2 ∧
      ∀ a b, z = a ++ b → b.length ≤ M.getD (holesT k b) 0) Ds (ts.drop (c.1 + 1))

theorem drop_eq_cons {α : Type} {l : List α} {n : ℕ} {t : α} {tl : List α} (d : α)
    (h : l.drop n = t :: tl) : l.getD n d = t ∧ l.drop (n + 1) = tl := by
  constructor
  · have h1 : (l.drop n).head? = some t := by rw [h]; rfl
    rw [List.head?_drop] at h1
    rw [List.getD_eq_getElem?_getD, h1]
    rfl
  · have h2 : (l.drop n).tail = tl := by rw [h]; rfl
    rw [List.tail_drop] at h2
    exact h2

/-- One row further. -/
theorem profInv_step {M : List ℕ} {ts : List (ℕ × ℕ)} {c : ℕ × ℕ × ℕ} {x : TRow}
    {w : List TRow} (h : ProfInv k M ts c (x :: w)) :
    ap (keepK (profKeepN M ts) noRule (profKeepJ ts) x.1) c = true ∧
      ProfInv k M ts (stepC k true c x) w := by
  obtain ⟨rem, Ds, hrest, hrem0, hlen, hrows, hholes, hcap, hDs⟩ := h
  cases rem with
  | cons y rem' =>
    -- a row of the current chain
    have hxy : x = y ∧ w = rem' ++ Ds.flatten := by
      simpa using hrest
    obtain ⟨rfl, rfl⟩ := hxy
    have hx0 : x.1 = 0 := hrem0 x List.mem_cons_self
    have hc0 := hcap [] (x :: rem') rfl
    rw [List.length_cons] at hrows hc0
    rw [holesT_cons] at hholes
    constructor
    · rw [hx0]
      show profKeepN M ts c.1 c.2.1 c.2.2 = true
      simp only [profKeepN, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.mem_range]
      refine ⟨⟨by omega, by omega⟩, holesT k (x :: rem'), ?_, by omega⟩
      rw [holesT_cons]
      omega
    · have e : stepC k true c x = (c.1, c.2.1 + 1, c.2.2 + (k - 1 - x.2.length)) := by
        simp [stepC, tK, rK, hx0]
      rw [e]
      refine ⟨rem', Ds, rfl, fun z hz => hrem0 z (List.mem_cons_of_mem _ hz), hlen, ?_, ?_, ?_,
        hDs⟩
      · show c.2.1 + 1 + rem'.length = (ts.getD c.1 (0, 0)).1
        omega
      · show c.2.2 + (k - 1 - x.2.length) + holesT k rem' ≤ (ts.getD c.1 (0, 0)).2
        omega
      · intro a b hab
        exact hcap (x :: a) b (by rw [hab]; rfl)
  | nil =>
    -- a jump to the next chain
    generalize hdr : ts.drop (c.1 + 1) = tsd at hDs
    cases hDs with
    | nil => simp at hrest
    | @cons D t Ds' tl hD hDs' =>
      obtain ⟨P, z, rfl, hz0, hDlen, hDhol, hDcap⟩ := hD
      have hxw : x = (2, P) ∧ w = z ++ Ds'.flatten := by
        simpa using hrest
      obtain ⟨rfl, rfl⟩ := hxw
      obtain ⟨ht, htl⟩ := drop_eq_cons (0, 0) hdr
      simp only [List.length_nil, holesT_nil, Nat.add_zero] at hrows hholes
      simp only [List.length_cons] at hlen hDlen
      constructor
      · show profKeepJ ts c.1 c.2.1 c.2.2 = true
        simp only [profKeepJ, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨by omega, hrows⟩, hholes⟩
      · have e : stepC k true c (2, P) = (c.1 + 1, 1, k - 1 - P.length) := by
          simp [stepC, tK, rK]
        rw [e]
        refine ⟨z, Ds', rfl, hz0, ?_, ?_, ?_, hDcap, ?_⟩
        · show c.1 + 1 + 1 + Ds'.length = ts.length
          omega
        · show 1 + z.length = (ts.getD (c.1 + 1) (0, 0)).1
          rw [ht]
          omega
        · show k - 1 - P.length + holesT k z ≤ (ts.getD (c.1 + 1) (0, 0)).2
          rw [ht]
          rw [holesT_cons] at hDhol
          exact hDhol
        · show List.Forall₂ _ Ds' (ts.drop (c.1 + 1 + 1))
          rw [htl]
          exact hDs'

/-- At the end the last chain has its rows. -/
theorem profInv_end {M : List ℕ} {ts : List (ℕ × ℕ)} {c : ℕ × ℕ × ℕ}
    (h : ProfInv k M ts c []) : ap (profBad ts) c = true := by
  obtain ⟨rem, Ds, hrest, _, hlen, hrows, hholes, _, hDs⟩ := h
  have h1 := List.append_eq_nil_iff.mp hrest.symm
  obtain ⟨rfl, hfl⟩ := h1
  generalize hdr : ts.drop (c.1 + 1) = tsd at hDs
  cases hDs with
  | nil =>
    simp only [List.length_nil, holesT_nil, Nat.add_zero] at hlen hrows hholes
    show profBad ts c.1 c.2.1 c.2.2 = true
    simp only [profBad, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨hlen, hrows⟩, hholes⟩
  | cons hD _ =>
    obtain ⟨P, z, rfl, _⟩ := hD
    simp at hfl

/-- **The profile rule holds along the chains.** -/
theorem prof_rule {M : List ℕ} {ts : List (ℕ × ℕ)} : ∀ (rest : List TRow) (c : ℕ × ℕ × ℕ),
    ProfInv k M ts c rest →
    (∀ u x w, rest = u ++ x :: w →
      ap (keepK (profKeepN M ts) noRule (profKeepJ ts) x.1) (u.foldl (stepC k true) c) = true) ∧
      ap (profBad ts) (rest.foldl (stepC k true) c) = true
  | [], c, h => ⟨fun u x w huw => by simp at huw, profInv_end h⟩
  | y :: rest, c, h => by
    obtain ⟨hk1, hinv⟩ := profInv_step h
    obtain ⟨ih1, ih2⟩ := prof_rule rest _ hinv
    refine ⟨?_, ih2⟩
    intro u x w huw
    cases u with
    | nil =>
      have e : y = x := by simpa using (List.cons.inj huw).1
      subst e
      exact hk1
    | cons y' u' =>
      obtain ⟨rfl, hr⟩ := List.cons.inj huw
      exact ih1 u' x w hr

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.seqCap_level
#print axioms SuperpermLowerBounds.PS.ringCap_of_stmt
#print axioms SuperpermLowerBounds.PS.prof_rule

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Chain capacity for Theorem C: the arithmetic

A chain of pieces is described here by the list `D` of the deficits of its pieces, in order:
`0` for a full piece, `d ≥ 1` for a partial piece.  The chain has `r = D.length` pieces and
total deficit `δ = D.sum`.

A *window* (`IsWindow`) is such a list that starts and ends with a non-zero entry and in which
every maximal block of non-zero entries contains an entry `≥ 2`.  The hypothesis of Theorem C
says that every window `W` of an actual chain satisfies `WindowBound k cn bn q W`:

  `2 r(W) + 2 (k - 4) + c δ(W) ≤ (k - 3) δ(W) + b`,   `c = cn / q`, `b = bn / q`.

From

* the run bounds: a block of zeros has length `≤ k - 2`, and `≤ k - 3` if a non-zero entry
  stands next to it,
* the unit rule (`UnitRule`): after a zero, an entry `1` is followed by an entry `≥ 2`,
* the window bound for the windows inside `D`,

this file proves the chain inequality (`chain_capacity_list`), multiplied by `2 q`:

  `4 q r ≤ 2 (q (k - 3) - cn) δ + priceC (first entry) + priceC (last entry)`.

The price of an end (`priceC`) is an integer and may be negative.  The file also contains the
facts about prices that the junction accounting needs (`priceC_le`, `priceC_mono`,
`priceC_pair_le_zero`).

No geometry and no permutations here: only lists of natural numbers.
-/

namespace SuperpermLowerBounds

namespace ChainC

/-! ### Windows and the window bound -/

/-- A window, as a list of deficits: the first and the last piece are partial, and every
interval (a maximal block of consecutive non-zero entries) contains a piece of deficit at
least 2, that is, has `ε ≥ 1`. -/
structure IsWindow (ds : List ℕ) : Prop where
  first_partial : ∃ x rest, ds = x :: rest ∧ 0 < x
  last_partial : ∃ init y, ds = init ++ [y] ∧ 0 < y
  excess : ∀ pre blk post : List ℕ, ds = pre ++ blk ++ post → blk ≠ [] →
    (∀ x ∈ blk, 0 < x) →
    (pre = [] ∨ ∃ pre', pre = pre' ++ [0]) →
    (post = [] ∨ ∃ post', post = 0 :: post') →
    ∃ x ∈ blk, 2 ≤ x

/-- `q · slack_int(w) + bn ≥ cn · δ(w)`, written without subtraction, with
`slack_int(w) = (k - 3) δ(w) - 2 r(w) - 2 (k - 4)`. -/
def WindowBound (k cn bn q : ℕ) (ds : List ℕ) : Prop :=
  q * (2 * ds.length + 2 * (k - 4)) + cn * ds.sum ≤ q * ((k - 3) * ds.sum) + bn

/-- `χ(w)`: the number of ends of the window (first piece, last piece) whose deficit is at
least `⌈(k - 1) / 2⌉`. -/
def chi (k : ℕ) (ds : List ℕ) : ℕ :=
  (if k ≤ 2 * ds.headD 0 + 1 then 1 else 0) + (if k ≤ 2 * ds.getLastD 0 + 1 then 1 else 0)

/-- The window bound for `s̃(w) = slack_int(w) - 2 χ(w)`: the stronger form. -/
def WindowBoundTilde (k cn bn q : ℕ) (ds : List ℕ) : Prop :=
  q * (2 * ds.length + 2 * (k - 4) + 2 * chi k ds) + cn * ds.sum ≤
    q * ((k - 3) * ds.sum) + bn

theorem windowBound_of_tilde {k cn bn q : ℕ} {ds : List ℕ}
    (h : WindowBoundTilde k cn bn q ds) : WindowBound k cn bn q ds := by
  unfold WindowBoundTilde at h
  unfold WindowBound
  have hle : q * (2 * ds.length + 2 * (k - 4)) ≤
      q * (2 * ds.length + 2 * (k - 4) + 2 * chi k ds) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  omega

/-- After a full piece, a piece of deficit 1 is followed by a piece of deficit at least 2
(in particular not by a full piece). -/
def UnitRule (D : List ℕ) : Prop :=
  ∀ (L1 L2 : List ℕ) (z : ℕ), D = L1 ++ 0 :: 1 :: z :: L2 → 2 ≤ z

/-! ### Lists -/

theorem nil_or_concat (l : List ℕ) : l = [] ∨ ∃ t y, l = t ++ [y] := by
  cases h : l.reverse with
  | nil =>
    left
    simpa using h
  | cons y t =>
    right
    refine ⟨t.reverse, y, ?_⟩
    have h' := congrArg List.reverse h
    simpa using h'

theorem last_eq_of_concat_eq {s t : List ℕ} {a b : ℕ} (h : s ++ [a] = t ++ [b]) : a = b := by
  have h' := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at h'
  exact (List.cons.inj h').1

theorem length_le_sum_of_pos (l : List ℕ) (h : ∀ x ∈ l, 0 < x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem sum_eq_zero_of_zeros (l : List ℕ) (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.sum_cons]
    omega

/-- A non-empty list of zeros starts with a zero and ends with a zero. -/
theorem zeros_forms {R : List ℕ} (hne : R ≠ []) (h : ∀ x ∈ R, x = 0) :
    (∃ t, R = 0 :: t) ∧ (∃ t, R = t ++ [0]) := by
  constructor
  · obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    have ha := h a List.mem_cons_self
    subst ha
    exact ⟨t, rfl⟩
  · rcases nil_or_concat R with rfl | ⟨t, y, rfl⟩
    · exact absurd rfl hne
    · have hy := h y (by simp)
      subst hy
      exact ⟨t, rfl⟩

/-- Split off the longest prefix whose entries satisfy `P`. -/
theorem split_front (P : ℕ → Prop) (l : List ℕ) :
    ∃ A M, l = A ++ M ∧ (∀ x ∈ A, P x) ∧ (M = [] ∨ ∃ y t, M = y :: t ∧ ¬ P y) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | cons x xs ih =>
    by_cases hx : P x
    · obtain ⟨A, M, h, hA, hM⟩ := ih
      refine ⟨x :: A, M, by rw [h]; rfl, ?_, hM⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hA z hz
    · exact ⟨[], x :: xs, rfl, by simp, Or.inr ⟨x, xs, rfl, hx⟩⟩

/-- Split off the longest suffix whose entries satisfy `P`. -/
theorem split_back (P : ℕ → Prop) (l : List ℕ) :
    ∃ M Z, l = M ++ Z ∧ (∀ x ∈ Z, P x) ∧ (M = [] ∨ ∃ t y, M = t ++ [y] ∧ ¬ P y) := by
  obtain ⟨A, M, h, hA, hM⟩ := split_front P l.reverse
  refine ⟨M.reverse, A.reverse, ?_, ?_, ?_⟩
  · have h' := congrArg List.reverse h
    simpa using h'
  · intro x hx
    exact hA x (List.mem_reverse.mp hx)
  · rcases hM with rfl | ⟨y, t, rfl, hy⟩
    · left
      rfl
    · right
      exact ⟨t.reverse, y, by simp, hy⟩

/-- Either all entries satisfy `P`, or the list is a prefix and a suffix of entries that
satisfy `P` around a middle part whose first and last entries do not. -/
theorem trim (P : ℕ → Prop) (l : List ℕ) :
    (∀ x ∈ l, P x) ∨ ∃ A M Z, l = A ++ M ++ Z ∧ (∀ x ∈ A, P x) ∧ (∀ x ∈ Z, P x) ∧
      (∃ y t, M = y :: t ∧ ¬ P y) ∧ (∃ t y, M = t ++ [y] ∧ ¬ P y) := by
  obtain ⟨A, M1, h1, hA, hM1⟩ := split_front P l
  rcases hM1 with rfl | ⟨y, t, rfl, hy⟩
  · left
    intro x hx
    rw [h1, List.append_nil] at hx
    exact hA x hx
  · right
    obtain ⟨M, Z, h2, hZ, hM⟩ := split_back P (y :: t)
    rcases hM with rfl | ⟨t', y', rfl, hy'⟩
    · exfalso
      have hmem : y ∈ Z := by
        rw [List.nil_append] at h2
        rw [← h2]
        exact List.mem_cons_self
      exact hy (hZ y hmem)
    · refine ⟨A, t' ++ [y'], Z, by rw [h1, h2]; simp, hA, hZ, ?_,
        ⟨t', y', rfl, hy'⟩⟩
      cases t' with
      | nil => exact ⟨y', [], rfl, hy'⟩
      | cons a t'' =>
        have hya : y = a := by
          have h3 : y :: t = a :: (t'' ++ [y'] ++ Z) := by simpa using h2
          exact (List.cons.inj h3).1
        exact ⟨a, t'' ++ [y'], rfl, by rw [← hya]; exact hy⟩

/-! ### The window between the first and the last run of a chain -/

/-- A list that stands between two zeros in a list with the unit rule, and that starts and
ends with a non-zero entry, is a window. -/
theorem isWindow_of_context {X W Y : List ℕ}
    (hU : UnitRule (X ++ [0] ++ W ++ 0 :: Y))
    (hfirst : ∃ x rest, W = x :: rest ∧ 0 < x)
    (hlast : ∃ init y, W = init ++ [y] ∧ 0 < y) : IsWindow W := by
  refine ⟨hfirst, hlast, ?_⟩
  intro pre blk post hW hblk hpos hpre hpost
  obtain ⟨y, rest, rfl⟩ := List.exists_cons_of_ne_nil hblk
  by_cases hy : 2 ≤ y
  · exact ⟨y, List.mem_cons_self, hy⟩
  · have hy1 : y = 1 := by
      have hy0 := hpos y List.mem_cons_self
      omega
    subst hy1
    -- the entry before the block is a zero
    obtain ⟨L1, hL1⟩ : ∃ L1, X ++ [0] ++ pre = L1 ++ [0] := by
      rcases hpre with rfl | ⟨pre', rfl⟩
      · exact ⟨X, by simp⟩
      · exact ⟨X ++ [0] ++ pre', by simp⟩
    -- the entry after the first entry of the block
    obtain ⟨z, L2, hL2, hz⟩ :
        ∃ z L2, rest ++ post ++ 0 :: Y = z :: L2 ∧ (z ∈ rest ∨ z = 0) := by
      cases rest with
      | nil =>
        rcases hpost with rfl | ⟨post', rfl⟩
        · exact ⟨0, Y, by simp, Or.inr rfl⟩
        · exact ⟨0, post' ++ 0 :: Y, by simp, Or.inr rfl⟩
      | cons z rest' =>
        exact ⟨z, rest' ++ post ++ 0 :: Y, by simp, Or.inl List.mem_cons_self⟩
    have hD : X ++ [0] ++ W ++ 0 :: Y = L1 ++ 0 :: 1 :: z :: L2 := by
      rw [hW]
      calc X ++ [0] ++ (pre ++ 1 :: rest ++ post) ++ 0 :: Y
          = (X ++ [0] ++ pre) ++ 1 :: (rest ++ post ++ 0 :: Y) := by simp
        _ = L1 ++ [0] ++ 1 :: (z :: L2) := by rw [hL1, hL2]
        _ = L1 ++ 0 :: 1 :: z :: L2 := by simp
    have h2 := hU L1 L2 z hD
    rcases hz with hz | hz
    · exact ⟨z, List.mem_cons_of_mem _ hz, h2⟩
    · omega

/-! ### The price of an end of a chain -/

/-- Price of an end piece of deficit `dd` in a list of `r` pieces, multiplied by `2 q`.
A full end costs `2 q (k - 2) + bn`.  A partial end costs
`2 q k + bn - 2 (q (k - 3) - cn) dd` (the bound for a chain with a full piece) or
`- (q (k - 5) - cn) dd` (the bound for a chain without a full piece), whichever is larger;
a single piece cannot contain a full piece besides itself, so there only the second counts. -/
def priceC (k cn bn q dd r : ℕ) : ℤ :=
  if dd = 0 then 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)
  else if r ≤ 1 then -(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ))
  else max (2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) -
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (dd : ℤ))
    (-(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ)))

variable {k cn bn q : ℕ}

theorem priceC_zero (r : ℕ) :
    priceC k cn bn q 0 r = 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) := by
  unfold priceC
  rw [if_pos rfl]

theorem priceC_single {dd r : ℕ} (hdd : dd ≠ 0) (hr : r ≤ 1) :
    priceC k cn bn q dd r = -(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ)) := by
  unfold priceC
  rw [if_neg hdd, if_pos hr]

theorem priceC_ge_bare {dd : ℕ} (hdd : dd ≠ 0) (r : ℕ) :
    -(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ)) ≤ priceC k cn bn q dd r := by
  unfold priceC
  rw [if_neg hdd]
  split_ifs
  · exact le_refl _
  · exact le_max_right _ _

theorem priceC_ge_full {dd r : ℕ} (hdd : dd ≠ 0) (hr : 2 ≤ r) :
    2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) - 2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (dd : ℤ) ≤
      priceC k cn bn q dd r := by
  unfold priceC
  rw [if_neg hdd, if_neg (by omega)]
  exact le_max_left _ _

/-- A partial end has one of the two prices. -/
theorem priceC_cases {dd : ℕ} (hdd : dd ≠ 0) (r : ℕ) :
    priceC k cn bn q dd r = 2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) -
        2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (dd : ℤ) ∨
      priceC k cn bn q dd r = -(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ)) := by
  unfold priceC
  rw [if_neg hdd]
  split_ifs
  · right
    rfl
  · rcases max_choice (2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) -
        2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * (dd : ℤ))
      (-(((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * (dd : ℤ))) with h | h
    · left
      exact h
    · right
      exact h

theorem cast_slope_nonneg (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) :
    (0 : ℤ) ≤ (q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ) := by
  have h : ((cn : ℕ) : ℤ) ≤ ((q * (k - 5) : ℕ) : ℤ) := by exact_mod_cast hc
  push_cast [Nat.cast_sub hk] at h
  linarith

/-- No end costs more than a full end. -/
theorem priceC_le (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) (dd r : ℕ) :
    priceC k cn bn q dd r ≤ 2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ) := by
  have hE := cast_slope_nonneg hk hc
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  have hb : (0 : ℤ) ≤ (bn : ℤ) := Int.natCast_nonneg _
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  by_cases hdd : dd = 0
  · subst hdd
    rw [priceC_zero]
  · have hd1 : (1 : ℤ) ≤ (dd : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdd
    have hm1 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ (dd : ℤ) - 1)
    have hm2 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (dd : ℤ) - 1)
    have hm3 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 5)
    rcases priceC_cases (k := k) (cn := cn) (bn := bn) (q := q) hdd r with h | h
    · rw [h]
      nlinarith
    · rw [h]
      nlinarith

/-- The price of an end does not decrease when the list of pieces is extended. -/
theorem priceC_mono (dd : ℕ) {r r' : ℕ} (h : r ≤ r') :
    priceC k cn bn q dd r ≤ priceC k cn bn q dd r' := by
  by_cases hdd : dd = 0
  · subst hdd
    rw [priceC_zero, priceC_zero]
  · by_cases hr : r ≤ 1
    · rw [priceC_single hdd hr]
      exact priceC_ge_bare hdd r'
    · have h1 : priceC k cn bn q dd r = priceC k cn bn q dd r' := by
        unfold priceC
        rw [if_neg hdd, if_neg hr, if_neg hdd, if_neg (by omega)]
      exact le_of_eq h1

/-- **The pair of ends at a junction of cost zero.**  Two partial ends of deficits `d, d' ≥ 2`
with `d + d' ≥ k` cost nothing together.  Conditions (i) and (ii) of the written proof are
used here and nowhere else. -/
theorem priceC_pair_le_zero (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    (hi : bn + cn * k ≤ q * k * (k - 5))
    (hii : bn + 4 * cn + 2 * q * k ≤ 4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2))
    {d d' : ℕ} (hd : 2 ≤ d) (hd' : 2 ≤ d') (hsum : k ≤ d + d') (r r' : ℕ) :
    priceC k cn bn q d r + priceC k cn bn q d' r' ≤ 0 := by
  have hE := cast_slope_nonneg hk hc
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hD : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hD' : (2 : ℤ) ≤ (d' : ℤ) := by exact_mod_cast hd'
  have hS : (k : ℤ) ≤ (d : ℤ) + (d' : ℤ) := by exact_mod_cast hsum
  have hI : (bn : ℤ) + (cn : ℤ) * (k : ℤ) ≤ (q : ℤ) * (k : ℤ) * ((k : ℤ) - 5) := by
    have h : ((bn + cn * k : ℕ) : ℤ) ≤ ((q * k * (k - 5) : ℕ) : ℤ) := by exact_mod_cast hi
    push_cast [Nat.cast_sub hk] at h
    exact h
  have hII : (bn : ℤ) + 4 * (cn : ℤ) + 2 * (q : ℤ) * (k : ℤ) ≤
      4 * (q : ℤ) * ((k : ℤ) - 3) + ((q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ)) * ((k : ℤ) - 2) := by
    have h : ((bn + 4 * cn + 2 * q * k : ℕ) : ℤ) ≤
        ((4 * q * (k - 3) + (q * (k - 5) - cn) * (k - 2) : ℕ) : ℤ) := by exact_mod_cast hii
    push_cast [Nat.cast_sub hk, Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub (by omega : 2 ≤ k),
      Nat.cast_sub hc] at h
    exact h
  -- abbreviations: `E = q (k - 5) - cn ≥ 0`
  obtain ⟨E, hEdef⟩ : ∃ E : ℤ, E = (q : ℤ) * ((k : ℤ) - 5) - (cn : ℤ) := ⟨_, rfl⟩
  have hKc : (q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ) = E + 2 * (q : ℤ) := by rw [hEdef]; ring
  rw [← hEdef] at hE hII
  have hI' : (bn : ℤ) ≤ (k : ℤ) * E := by rw [hEdef]; linarith
  have hII' : (bn : ℤ) + 2 * (q : ℤ) * (k : ℤ) ≤ E * ((k : ℤ) + 2) + 8 * (q : ℤ) := by
    have h3 : 4 * (q : ℤ) * ((k : ℤ) - 3) - 4 * (cn : ℤ) = 4 * E + 8 * (q : ℤ) := by
      rw [hEdef]; ring
    linarith
  have hd0 : d ≠ 0 := by omega
  have hd0' : d' ≠ 0 := by omega
  have p1 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ (d : ℤ) + (d' : ℤ) - (k : ℤ))
  have p2 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (d : ℤ) + (d' : ℤ) - (k : ℤ))
  have p3 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ (d : ℤ) - 2)
  have p4 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ (d' : ℤ) - 2)
  have p5 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (d : ℤ) - 2)
  have p6 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (d' : ℤ) - 2)
  have c1 : priceC k cn bn q d r =
        2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) - 2 * (E + 2 * (q : ℤ)) * (d : ℤ) ∨
      priceC k cn bn q d r = -(E * (d : ℤ)) := by
    rcases priceC_cases (k := k) (cn := cn) (bn := bn) (q := q) hd0 r with h | h
    · left
      rw [h, hKc]
    · right
      rw [h, hEdef]
  have c2 : priceC k cn bn q d' r' =
        2 * (q : ℤ) * (k : ℤ) + (bn : ℤ) - 2 * (E + 2 * (q : ℤ)) * (d' : ℤ) ∨
      priceC k cn bn q d' r' = -(E * (d' : ℤ)) := by
    rcases priceC_cases (k := k) (cn := cn) (bn := bn) (q := q) hd0' r' with h | h
    · left
      rw [h, hKc]
    · right
      rw [h, hEdef]
  rcases c1 with h | h <;> rcases c2 with h' | h' <;> rw [h, h'] <;> nlinarith

/-! ### The two ends of a chain -/

/-- The first end: the partial pieces before the first full piece, and the price of the first
piece, cover a full end. -/
theorem front_price (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) {A rest D : List ℕ} {x : ℕ}
    (hD : D = A ++ rest) (hA : ∀ u ∈ A, 0 < u) (hrest : ∃ t, rest = 0 :: t)
    (hx : ∃ t, D = x :: t) :
    4 * (q : ℤ) * (A.length : ℤ) + (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * ((A.sum : ℕ) : ℤ) +
        priceC k cn bn q x D.length := by
  have hE := cast_slope_nonneg hk hc
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  obtain ⟨t, rfl⟩ := hrest
  obtain ⟨tx, hx⟩ := hx
  cases A with
  | nil =>
    have hx0 : x = 0 := by
      rw [hD] at hx
      exact ((List.cons.inj hx).1).symm
    subst hx0
    rw [priceC_zero]
    simp
  | cons a A' =>
    have hxa : x = a := by
      rw [hD] at hx
      exact ((List.cons.inj hx).1).symm
    subst hxa
    have hxpos := hA x List.mem_cons_self
    have hlen : 2 ≤ D.length := by
      rw [hD]
      simp only [List.length_append, List.length_cons]
      omega
    have hprice := priceC_ge_full (k := k) (cn := cn) (bn := bn) (q := q)
      (by omega : x ≠ 0) hlen
    have hsum := length_le_sum_of_pos A' (fun u hu => hA u (List.mem_cons_of_mem x hu))
    have hsumZ : ((A'.length : ℕ) : ℤ) ≤ ((A'.sum : ℕ) : ℤ) := by exact_mod_cast hsum
    have hl0 : (0 : ℤ) ≤ ((A'.length : ℕ) : ℤ) := Int.natCast_nonneg _
    have m1 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ ((A'.sum : ℕ) : ℤ))
    have m2 := mul_nonneg hq
      (by linarith : (0 : ℤ) ≤ ((A'.sum : ℕ) : ℤ) - ((A'.length : ℕ) : ℤ))
    simp only [List.length_cons, List.sum_cons]
    push_cast
    nlinarith

/-- The last end: the mirror image of `front_price`. -/
theorem back_price (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5)) {Z rest D : List ℕ} {y : ℕ}
    (hD : D = rest ++ Z) (hZ : ∀ u ∈ Z, 0 < u) (hrest : ∃ t, rest = t ++ [0])
    (hy : ∃ t, D = t ++ [y]) :
    4 * (q : ℤ) * (Z.length : ℤ) + (2 * (q : ℤ) * ((k : ℤ) - 2) + (bn : ℤ)) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * ((Z.sum : ℕ) : ℤ) +
        priceC k cn bn q y D.length := by
  have hE := cast_slope_nonneg hk hc
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  obtain ⟨t, rfl⟩ := hrest
  obtain ⟨ty, hy⟩ := hy
  rcases nil_or_concat Z with rfl | ⟨Z', z, rfl⟩
  · have hy0 : y = 0 := by
      rw [hD, List.append_nil] at hy
      exact (last_eq_of_concat_eq hy).symm
    subst hy0
    rw [priceC_zero]
    simp
  · have hyz : y = z := by
      rw [hD, ← List.append_assoc] at hy
      exact (last_eq_of_concat_eq hy).symm
    subst hyz
    have hypos := hZ y (by simp)
    have hlen : 2 ≤ D.length := by
      rw [hD]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hprice := priceC_ge_full (k := k) (cn := cn) (bn := bn) (q := q)
      (by omega : y ≠ 0) hlen
    have hsum := length_le_sum_of_pos Z' (fun u hu => hZ u (by simp [hu]))
    have hsumZ : ((Z'.length : ℕ) : ℤ) ≤ ((Z'.sum : ℕ) : ℤ) := by exact_mod_cast hsum
    have hl0 : (0 : ℤ) ≤ ((Z'.length : ℕ) : ℤ) := Int.natCast_nonneg _
    have m1 := mul_nonneg hE (by linarith : (0 : ℤ) ≤ ((Z'.sum : ℕ) : ℤ))
    have m2 := mul_nonneg hq
      (by linarith : (0 : ℤ) ≤ ((Z'.sum : ℕ) : ℤ) - ((Z'.length : ℕ) : ℤ))
    simp only [List.length_append, List.length_cons, List.length_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    push_cast
    nlinarith

/-! ### The chain inequality -/

/-- **(C-chain), multiplied by `2 q`.**  `D` is the list of deficits of a chain, `x` its
first and `y` its last entry. -/
theorem chain_capacity_list (hk : 5 ≤ k) (hc : cn ≤ q * (k - 5))
    {D : List ℕ} {x y : ℕ} (hx : ∃ t, D = x :: t) (hy : ∃ t, D = t ++ [y])
    (hrun : ∀ L1 R L2 : List ℕ, D = L1 ++ R ++ L2 → (∀ u ∈ R, u = 0) → R.length ≤ k - 2)
    (hrunR : ∀ (L1 R : List ℕ) (z : ℕ) (L2 : List ℕ), D = L1 ++ R ++ z :: L2 →
      (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3)
    (hrunL : ∀ (L1 : List ℕ) (z : ℕ) (R L2 : List ℕ), D = L1 ++ z :: R ++ L2 →
      (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3)
    (hU : UnitRule D)
    (hW : ∀ L1 W L2 : List ℕ, D = L1 ++ W ++ L2 → IsWindow W → WindowBound k cn bn q W) :
    4 * (q : ℤ) * (D.length : ℤ) ≤
      2 * ((q : ℤ) * ((k : ℤ) - 3) - (cn : ℤ)) * ((D.sum : ℕ) : ℤ) +
        priceC k cn bn q x D.length + priceC k cn bn q y D.length := by
  have hE := cast_slope_nonneg hk hc
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  have hb : (0 : ℤ) ≤ (bn : ℤ) := Int.natCast_nonneg _
  have hK : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rcases trim (fun z => 0 < z) D with hall | ⟨A, M, Z, hD, hA, hZ, hMf, hMl⟩
  · -- no full piece
    obtain ⟨tx, hDx⟩ := hx
    obtain ⟨ty, hDy⟩ := hy
    have hxpos : 0 < x := hall x (by rw [hDx]; exact List.mem_cons_self)
    have hypos : 0 < y := hall y (by rw [hDy]; simp)
    have hsum := length_le_sum_of_pos D hall
    have hsumZ : ((D.length : ℕ) : ℤ) ≤ ((D.sum : ℕ) : ℤ) := by exact_mod_cast hsum
    have hx1 : (1 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hxpos
    by_cases hlen : D.length ≤ 1
    · have htx : tx = [] := by
        rw [hDx] at hlen
        simp only [List.length_cons] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst htx
      have hyx : y = x := by
        rw [hDx] at hDy
        have h1 : ([] : List ℕ) ++ [x] = ty ++ [y] := by simpa using hDy
        exact (last_eq_of_concat_eq h1).symm
      subst hyx
      rw [priceC_single (by omega : y ≠ 0) hlen, hDx]
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      push_cast
      have m1 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (y : ℤ) - 1)
      nlinarith
    · have hxy : x + y ≤ D.sum := by
        rcases nil_or_concat tx with rfl | ⟨tx', y', rfl⟩
        · rw [hDx] at hlen
          simp at hlen
        · have hyy : y' = y := by
            rw [hDx] at hDy
            have h1 : (x :: tx') ++ [y'] = ty ++ [y] := by simpa using hDy
            exact last_eq_of_concat_eq h1
          subst hyy
          rw [hDx]
          simp only [List.sum_cons, List.sum_append, List.sum_nil]
          omega
      have hxyZ : (x : ℤ) + (y : ℤ) ≤ ((D.sum : ℕ) : ℤ) := by exact_mod_cast hxy
      have hpx := priceC_ge_bare (k := k) (cn := cn) (bn := bn) (q := q)
        (by omega : x ≠ 0) D.length
      have hpy := priceC_ge_bare (k := k) (cn := cn) (bn := bn) (q := q)
        (by omega : y ≠ 0) D.length
      have m1 := mul_nonneg hE
        (by linarith : (0 : ℤ) ≤ ((D.sum : ℕ) : ℤ) - ((x : ℤ) + (y : ℤ)))
      have m2 := mul_nonneg hq
        (by linarith : (0 : ℤ) ≤ ((D.sum : ℕ) : ℤ) - ((D.length : ℕ) : ℤ))
      nlinarith
  · -- the part `M` between the first and the last full piece
    obtain ⟨m0, tM, hM0, hm0⟩ := hMf
    obtain ⟨tM', m1, hM1, hm1⟩ := hMl
    have hm0' : m0 = 0 := by omega
    have hm1' : m1 = 0 := by omega
    subst hm0'
    subst hm1'
    rcases trim (fun z => z = 0) M with hMall | ⟨R, W, R', hM, hR, hR', hWf, hWl⟩
    · -- one run of full pieces
      have hrunM := hrun A M Z hD hMall
      have hfront := front_price (bn := bn) hk hc (A := A) (rest := M ++ Z) (D := D) (x := x)
        (by rw [hD, List.append_assoc]) hA ⟨tM ++ Z, by rw [hM0]; rfl⟩ hx
      have hback := back_price (bn := bn) hk hc (Z := Z) (rest := A ++ M) (D := D) (y := y)
        hD hZ ⟨A ++ tM', by rw [hM1, List.append_assoc]⟩ hy
      have hlenD : D.length = A.length + M.length + Z.length := by
        rw [hD]
        simp only [List.length_append]
      have hsumD : D.sum = A.sum + Z.sum := by
        rw [hD]
        simp only [List.sum_append]
        rw [sum_eq_zero_of_zeros M hMall]
        omega
      have hrunZ : ((M.length : ℕ) : ℤ) ≤ (k : ℤ) - 2 := by
        have h : ((M.length : ℕ) : ℤ) ≤ ((k - 2 : ℕ) : ℤ) := by exact_mod_cast hrunM
        push_cast [Nat.cast_sub (by omega : 2 ≤ k)] at h
        exact h
      have hlenZ : ((D.length : ℕ) : ℤ) =
          ((A.length : ℕ) : ℤ) + ((M.length : ℕ) : ℤ) + ((Z.length : ℕ) : ℤ) := by
        rw [hlenD]
        push_cast
        ring
      have hsumZ : ((D.sum : ℕ) : ℤ) = ((A.sum : ℕ) : ℤ) + ((Z.sum : ℕ) : ℤ) := by
        rw [hsumD]
        push_cast
        ring
      rw [hlenZ, hsumZ]
      have m2 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 2 - ((M.length : ℕ) : ℤ))
      nlinarith
    · -- two runs of full pieces with a window between them
      obtain ⟨w0, tW, hW0, hw0⟩ := hWf
      obtain ⟨tW', w1, hW1, hw1⟩ := hWl
      have hw0pos : 0 < w0 := Nat.pos_of_ne_zero hw0
      have hw1pos : 0 < w1 := Nat.pos_of_ne_zero hw1
      have hRne : R ≠ [] := by
        rintro rfl
        rw [hM0, hW0] at hM
        have h1 : 0 :: tM = w0 :: (tW ++ R') := by simpa using hM
        exact hw0 ((List.cons.inj h1).1).symm
      have hR'ne : R' ≠ [] := by
        rintro rfl
        rw [hM1, hW1] at hM
        have h1 : tM' ++ [0] = (R ++ tW') ++ [w1] := by simpa using hM
        exact hw1 (last_eq_of_concat_eq h1).symm
      obtain ⟨⟨Rt, hRt⟩, ⟨Rs, hRs⟩⟩ := zeros_forms hRne hR
      obtain ⟨⟨Rt', hRt'⟩, ⟨Rs', hRs'⟩⟩ := zeros_forms hR'ne hR'
      -- the window
      have hDW : D = (A ++ Rs) ++ [0] ++ W ++ 0 :: (Rt' ++ Z) := by
        rw [hD, hM]
        conv_lhs => rw [hRs, hRt']
        simp
      have hwin : IsWindow W :=
        isWindow_of_context (hDW ▸ hU) ⟨w0, tW, hW0, hw0pos⟩ ⟨tW', w1, hW1, hw1pos⟩
      have hbound := hW (A ++ R) W (R' ++ Z) (by rw [hD, hM]; simp) hwin
      -- the two runs
      have hrun1 := hrunR A R w0 (tW ++ R' ++ Z) (by rw [hD, hM, hW0]; simp) hR hw0pos
      have hrun2 := hrunL (A ++ R ++ tW') w1 R' Z (by rw [hD, hM, hW1]; simp) hR' hw1pos
      -- the two ends
      have hfront := front_price (bn := bn) hk hc (A := A) (rest := M ++ Z) (D := D) (x := x)
        (by rw [hD, List.append_assoc]) hA ⟨tM ++ Z, by rw [hM0]; rfl⟩ hx
      have hback := back_price (bn := bn) hk hc (Z := Z) (rest := A ++ M) (D := D) (y := y)
        hD hZ ⟨A ++ tM', by rw [hM1, List.append_assoc]⟩ hy
      have hlenD : D.length = A.length + (R.length + W.length + R'.length) + Z.length := by
        rw [hD, hM]
        simp only [List.length_append]
      have hsumD : D.sum = A.sum + W.sum + Z.sum := by
        rw [hD, hM]
        simp only [List.sum_append]
        rw [sum_eq_zero_of_zeros R hR, sum_eq_zero_of_zeros R' hR']
        omega
      have hrun1Z : ((R.length : ℕ) : ℤ) ≤ (k : ℤ) - 3 := by
        have h : ((R.length : ℕ) : ℤ) ≤ ((k - 3 : ℕ) : ℤ) := by exact_mod_cast hrun1
        push_cast [Nat.cast_sub (by omega : 3 ≤ k)] at h
        exact h
      have hrun2Z : ((R'.length : ℕ) : ℤ) ≤ (k : ℤ) - 3 := by
        have h : ((R'.length : ℕ) : ℤ) ≤ ((k - 3 : ℕ) : ℤ) := by exact_mod_cast hrun2
        push_cast [Nat.cast_sub (by omega : 3 ≤ k)] at h
        exact h
      have hboundZ : (q : ℤ) * (2 * ((W.length : ℕ) : ℤ) + 2 * ((k : ℤ) - 4)) +
          (cn : ℤ) * ((W.sum : ℕ) : ℤ) ≤
          (q : ℤ) * (((k : ℤ) - 3) * ((W.sum : ℕ) : ℤ)) + (bn : ℤ) := by
        unfold WindowBound at hbound
        have h : ((q * (2 * W.length + 2 * (k - 4)) + cn * W.sum : ℕ) : ℤ) ≤
            ((q * ((k - 3) * W.sum) + bn : ℕ) : ℤ) := by exact_mod_cast hbound
        push_cast [Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub (by omega : 4 ≤ k)] at h
        exact h
      have hlenZ : ((D.length : ℕ) : ℤ) =
          ((A.length : ℕ) : ℤ) + (((R.length : ℕ) : ℤ) + ((W.length : ℕ) : ℤ) +
            ((R'.length : ℕ) : ℤ)) + ((Z.length : ℕ) : ℤ) := by
        rw [hlenD]
        push_cast
        ring
      have hsumZ : ((D.sum : ℕ) : ℤ) =
          ((A.sum : ℕ) : ℤ) + ((W.sum : ℕ) : ℤ) + ((Z.sum : ℕ) : ℤ) := by
        rw [hsumD]
        push_cast
        ring
      rw [hlenZ, hsumZ]
      have m2 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 3 - ((R.length : ℕ) : ℤ))
      have m3 := mul_nonneg hq (by linarith : (0 : ℤ) ≤ (k : ℤ) - 3 - ((R'.length : ℕ) : ℤ))
      nlinarith

end ChainC

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.ChainC.isWindow_of_context
#print axioms SuperpermLowerBounds.ChainC.priceC_pair_le_zero
#print axioms SuperpermLowerBounds.ChainC.chain_capacity_list

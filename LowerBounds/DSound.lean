import LowerBounds.SSound
import LowerBounds.DSearch

/-!
# The prefix search is complete

`pstatement_of_search`: if the search of `DSearch.lean` with the rule `keep`, `bad` answers `false`
(all `nt` parts of it), then no chain of words (`IsWChain`, `SSound.lean`) all of whose non-empty
proper prefixes satisfy `keep` is `bad` (`PStatement k keep bad`).  Here `keep` and `bad` are
arbitrary Boolean functions of the number of pieces and the total deficit; nothing is assumed
about them.

The proof follows a chain piece by piece, as `go_complete` of `SSound.lean` does, after the symbols
are relabelled so that the first entry is the word `1 2 … k`.  What is new is the table of marks:

* a mark of the table is always the class index of a block of the chain so far (`MInv`), and two
  words with the same class index are rotations of each other (`isRotated_of_ci_eq`), so a block
  of a new class is never refused;
* every part of the search returns a table with no new marks (`Sub`, `pgo_sub`), which is what
  makes the invariant survive the calls that are made before the chain is followed.

Nothing is proved about bounds of the table: an index outside it reads as "no mark" and writing
there does nothing, which is harmless for completeness.
-/

namespace SuperpermLowerBounds
namespace S

/-! ### Arithmetic of the compiled versions -/

theorem idcF_eq : ∀ n : ℕ, idcF n = idc n
  | 0 => rfl
  | n + 1 => by
    rw [idc_succ, ← idcF_eq n]
    rfl

theorem shr4 (x n : ℕ) : x >>> (4 * n) = x / 16 ^ n := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem and16 (x n : ℕ) : x &&& (16 ^ n - 1) = x % 16 ^ n := by
  have h : (16 : ℕ) ^ n = 2 ^ (4 * n) := by
    rw [pow_mul]
    norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

theorem m1_succ (k : ℕ) : 16 ^ (k - 1) - 1 + 1 = 16 ^ (k - 1) :=
  Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))

theorem excF_eq (k c : ℕ) : excF (16 ^ (k - 1) - 1) c = exc k c := by
  show c % 16 * (16 ^ (k - 1) - 1 + 1) + c / 16 = c % 16 * 16 ^ (k - 1) + c / 16
  rw [m1_succ]

theorem doorF_eq (k x : ℕ) (hk : 2 ≤ k) :
    doorF (4 * (k - 1)) (16 ^ (k - 1) - 1) x = doorc k x := by
  have h1 : (16 ^ (k - 1) - 1) >>> 4 = 16 ^ (k - 2) - 1 := by
    have e : k - 1 = k - 2 + 1 := by omega
    have hp : 0 < 16 ^ (k - 2) := Nat.pow_pos (by norm_num)
    have h24 : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [Nat.shiftRight_eq_div_pow, e, pow_succ, h24]
    generalize 16 ^ (k - 2) = X at hp ⊢
    omega
  have h2 : 4 * (k - 1) - 4 = 4 * (k - 2) := by omega
  show (x &&& ((16 ^ (k - 1) - 1) >>> 4)) * 256 + (x >>> (4 * (k - 1) - 4)) % 16 * 16 +
      (x >>> (4 * (k - 1))) =
    (x % 16 ^ (k - 2)) * 256 + (x / 16 ^ (k - 2) % 16) * 16 + x / 16 ^ (k - 1)
  rw [h1, h2, and16, shr4, shr4]

theorem canonF_zero (k s1 m1 c : ℕ) : canonF k s1 m1 0 c = c := rfl

theorem canonF_succ (k s1 m1 n c : ℕ) : canonF k s1 m1 (n + 1) c =
    if c >>> s1 == k then c else canonF k s1 m1 n ((c &&& m1) * 16 + (c >>> s1)) := rfl

/-- `canonF` returns the code of a rotation of the word. -/
theorem canonF_rot (k : ℕ) (hk : 1 ≤ k) : ∀ (n : ℕ) (w : List ℕ), w.length = k →
    (∀ a ∈ w, a < 16) →
    ∃ i, canonF k (4 * (k - 1)) (16 ^ (k - 1) - 1) n (code w) = code (w.rotate i)
  | 0, w, _, _ => ⟨0, by rw [List.rotate_zero, canonF_zero]⟩
  | n + 1, w, hw, hd => by
    by_cases h : (code w >>> (4 * (k - 1)) == k) = true
    · exact ⟨0, by rw [List.rotate_zero, canonF_succ, if_pos h]⟩
    · have hstep : (code w &&& (16 ^ (k - 1) - 1)) * 16 + (code w >>> (4 * (k - 1))) =
          code (w.rotate 1) := by
        rw [and16, shr4, ← rotl_code k w hw hd 1 hk]
        rfl
      obtain ⟨i, hi⟩ := canonF_rot k hk n (w.rotate 1) (by rw [List.length_rotate]; exact hw)
        (fun a ha => hd a (List.mem_rotate.mp ha))
      refine ⟨1 + i, ?_⟩
      rw [canonF_succ, if_neg h, hstep, hi, List.rotate_rotate]

theorem packF_succ (B n c : ℕ) : packF B (n + 1) c = packF B n (c / 16) * B + (c % 16 - 1) := rfl

/-- `packF` on the last digits of a code determines them, if they lie between `1` and `B`. -/
theorem packF_inj (B : ℕ) : ∀ (t t' pre pre' : List ℕ), t.length = t'.length →
    (∀ a ∈ t, 1 ≤ a ∧ a ≤ B ∧ a < 16) → (∀ a ∈ t', 1 ≤ a ∧ a ≤ B ∧ a < 16) →
    packF B t.length (code (pre ++ t)) = packF B t.length (code (pre' ++ t')) → t = t' := by
  intro t
  induction t using List.reverseRecOn with
  | nil =>
    intro t' pre pre' hl _ _ _
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | append_singleton u a ih =>
    intro t' pre pre' hl ht ht' h
    rcases List.eq_nil_or_concat t' with rfl | ⟨u', a', rfl⟩
    · simp at hl
    · rw [List.concat_eq_append] at hl ht' h ⊢
      have hl' : u.length = u'.length := by simpa using hl
      have ha := ht a (by simp)
      have ha' := ht' a' (by simp)
      have e1 : code (pre ++ (u ++ [a])) = code (pre ++ u) * 16 + a := by
        rw [← List.append_assoc, code_append, code_singleton]
        simp
      have e2 : code (pre' ++ (u' ++ [a'])) = code (pre' ++ u') * 16 + a' := by
        rw [← List.append_assoc, code_append, code_singleton]
        simp
      rw [List.length_append, List.length_singleton, packF_succ, packF_succ, e1, e2,
        mul_add_div' ha.2.2, mul_add_mod' ha.2.2, mul_add_div' ha'.2.2, mul_add_mod' ha'.2.2] at h
      have hB1 : a - 1 < B := by omega
      have hB2 : a' - 1 < B := by omega
      have h3 := congrArg (fun z => z / B) h
      simp only [mul_add_div' hB1, mul_add_div' hB2] at h3
      have h4 := congrArg (fun z => z % B) h
      simp only [mul_add_mod' hB1, mul_add_mod' hB2] at h4
      have hu := ih u' pre pre' hl' (fun x hx => ht x (by simp [hx]))
        (fun x hx => ht' x (by simp [hx])) h3
      have haa : a = a' := by omega
      rw [hu, haa]

/-- Two permutation words that differ at most in their first symbol are equal. -/
theorem permW_head_eq {k a b : ℕ} {t : List ℕ} (h1 : PermW k (a :: t)) (h2 : PermW k (b :: t)) :
    a = b := by
  have hb : b ∈ a :: t := (h1.2.2 b).mpr ((h2.2.2 b).mp List.mem_cons_self)
  rcases List.mem_cons.mp hb with h | h
  · exact h.symm
  · exact absurd h (List.nodup_cons.mp h2.1).1

/-- The class index with the constants that the search uses. -/
local notation "ci(" k ", " c ")" => cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1) c

/-- Two words with the same class index are rotations of each other. -/
theorem isRotated_of_ci_eq {k : ℕ} (hk : 1 ≤ k) (hk15 : k ≤ 15) {u v : List ℕ} (hu : PermW k u)
    (hv : PermW k v) (h : ci(k, code u) = ci(k, code v)) : u ~r v := by
  obtain ⟨i, hi⟩ := canonF_rot k hk k u hu.2.1 (hu.lt16 hk15)
  obtain ⟨j, hj⟩ := canonF_rot k hk k v hv.2.1 (hv.lt16 hk15)
  have hu' := hu.rotate i
  have hv' := hv.rotate j
  have h' : packF k (k - 1) (code (u.rotate i)) = packF k (k - 1) (code (v.rotate j)) := by
    rw [← hi, ← hj]
    exact h
  have h1 : u ~r u.rotate i := ⟨i, rfl⟩
  have h2 : v ~r v.rotate j := ⟨j, rfl⟩
  obtain ⟨a, t, hat⟩ : ∃ a t, u.rotate i = a :: t := by
    cases hc : u.rotate i with
    | nil =>
      have := hu'.2.1
      rw [hc] at this
      simp at this
      omega
    | cons a t => exact ⟨a, t, rfl⟩
  obtain ⟨b, t', hbt⟩ : ∃ b t', v.rotate j = b :: t' := by
    cases hc : v.rotate j with
    | nil =>
      have := hv'.2.1
      rw [hc] at this
      simp at this
      omega
    | cons b t' => exact ⟨b, t', rfl⟩
  rw [hat] at hu' h' h1
  rw [hbt] at hv' h' h2
  have hlt : t.length = k - 1 := by
    have := hu'.2.1
    simp only [List.length_cons] at this
    omega
  have hlt' : t'.length = k - 1 := by
    have := hv'.2.1
    simp only [List.length_cons] at this
    omega
  have htt : t = t' := by
    apply packF_inj k t t' [a] [b] (by rw [hlt, hlt'])
    · intro x hx
      have := (hu'.2.2 x).mp (List.mem_cons_of_mem _ hx)
      exact ⟨this.1, this.2, by omega⟩
    · intro x hx
      have := (hv'.2.2 x).mp (List.mem_cons_of_mem _ hx)
      exact ⟨this.1, this.2, by omega⟩
    · rw [hlt]
      exact h'
  subst htt
  have hab := permW_head_eq hu' hv'
  subst hab
  exact h1.trans h2.symm

/-! ### The table of marks -/

theorem get!_eq (M : ByteArray) (i : ℕ) : M.get! i = (M.data[i]?).getD 0 := by
  cases M with
  | mk bs =>
    show bs[i]! = _
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rfl

theorem data_set! (M : ByteArray) (i : ℕ) (v : UInt8) :
    (M.set! i v).data = M.data.setIfInBounds i v := by
  cases M
  rfl

theorem get!_set! (M : ByteArray) (i j : ℕ) (v : UInt8) :
    (M.set! i v).get! j = if i = j then (if i < M.data.size then v else 0) else M.get! j := by
  rw [get!_eq, get!_eq, data_set!, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
    by_cases h2 : i < M.data.size
    · rw [if_pos h2, if_pos h2]
      rfl
    · rw [if_neg h2, if_neg h2]
      rfl
  · rw [if_neg h, if_neg h]

/-- A mark after one byte was written: it is at the place written or it was there before. -/
theorem marked_set (M : ByteArray) (i j : ℕ) (v : UInt8) (h : (M.set! i v).get! j ≠ 0) :
    j = i ∨ M.get! j ≠ 0 := by
  rw [get!_set!] at h
  by_cases hij : i = j
  · exact Or.inl hij.symm
  · rw [if_neg hij] at h
    exact Or.inr h

/-- A mark after one byte was cleared: it was there before, and not at the place cleared. -/
theorem marked_clear (M : ByteArray) (i j : ℕ) (h : (M.set! i 0).get! j ≠ 0) :
    M.get! j ≠ 0 ∧ j ≠ i := by
  rw [get!_set!] at h
  by_cases hij : i = j
  · rw [if_pos hij] at h
    exfalso
    by_cases h2 : i < M.data.size
    · rw [if_pos h2] at h
      exact h rfl
    · rw [if_neg h2] at h
      exact h rfl
  · rw [if_neg hij] at h
    exact ⟨h, fun e => hij e.symm⟩

theorem get!_of_size_zero (M : ByteArray) (h : M.size = 0) (j : ℕ) : M.get! j = 0 := by
  rw [get!_eq]
  have hs : M.data.size = 0 := by
    rw [ByteArray.size_data]
    exact h
  have : M.data[j]? = none := Array.getElem?_eq_none (by omega)
  rw [this]
  rfl

theorem get!_marks0 (sz j : ℕ) : (marks0 sz).get! j = 0 := by
  rw [get!_eq]
  show ((Array.replicate sz (0 : UInt8))[j]?).getD 0 = 0
  rw [Array.getElem?_replicate]
  by_cases h : j < sz
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

/-- Every mark of the table is the class index of one of the words of `used`. -/
def MInv (k : ℕ) (M : ByteArray) (used : List (List ℕ)) : Prop :=
  ∀ j, M.get! j ≠ 0 → ∃ u ∈ used, j = ci(k, code u)

/-- `M'` has no mark that `M` does not have. -/
def Sub (M' M : ByteArray) : Prop := ∀ j, M'.get! j ≠ 0 → M.get! j ≠ 0

theorem Sub.refl (M : ByteArray) : Sub M M := fun _ h => h

theorem Sub.trans {A B C : ByteArray} (h1 : Sub A B) (h2 : Sub B C) : Sub A C :=
  fun j h => h2 j (h1 j h)

theorem sub_of_size_zero {M' : ByteArray} (h : M'.size = 0) (M : ByteArray) : Sub M' M :=
  fun j hj => absurd (get!_of_size_zero M' h j) hj

/-- Setting a mark, searching, and clearing the mark again leaves no new mark. -/
theorem sub_clear {M' M : ByteArray} {i : ℕ} (h : Sub M' (M.set! i 1)) :
    Sub (M'.set! i 0) M := by
  intro j hj
  obtain ⟨h1, h2⟩ := marked_clear M' i j hj
  rcases marked_set M i j 1 (h j h1) with h3 | h3
  · exact absurd h3 h2
  · exact h3

theorem MInv.sub {k : ℕ} {M' M : ByteArray} {used : List (List ℕ)} (h : MInv k M used)
    (hs : Sub M' M) : MInv k M' used := fun j hj => h j (hs j hj)

theorem minv_marks0 (k sz : ℕ) : MInv k (marks0 sz) [] :=
  fun j hj => absurd (get!_marks0 sz j) hj

theorem minv_set {k : ℕ} {M : ByteArray} {used : List (List ℕ)} (h : MInv k M used)
    (v : List ℕ) : MInv k (M.set! ci(k, code v) 1) (used ++ [v]) := by
  intro j hj
  rcases marked_set M _ j 1 hj with h1 | h1
  · exact ⟨v, by simp, h1⟩
  · obtain ⟨u, hu, he⟩ := h j h1
    exact ⟨u, List.mem_append_left _ hu, he⟩

/-- A word that is not a rotation of any used word has no mark. -/
theorem unmarked_of_new {k : ℕ} (hk : 1 ≤ k) (hk15 : k ≤ 15) {M : ByteArray}
    {used : List (List ℕ)} (hM : MInv k M used) (hused : ∀ u ∈ used, PermW k u) {v : List ℕ}
    (hv : PermW k v) (hnew : ∀ u ∈ used, ¬ u ~r v) : M.get! ci(k, code v) = 0 := by
  by_contra hm
  obtain ⟨u, hu, he⟩ := hM _ hm
  exact hnew u hu (isRotated_of_ci_eq hk hk15 (hused u hu) hv he.symm)

/-! ### The equations of the search -/

theorem if_size {α : Type} (X : ByteArray) (a b : α) :
    (if X.size == 0 then a else b) = if X.size = 0 then a else b := by
  by_cases h : X.size = 0 <;> simp [h]

theorem if_bne {α : Type} (x : UInt8) (a b : α) :
    (if x != 0 then a else b) = if x = 0 then b else a := by
  by_cases h : x = 0 <;> simp [h]

theorem pwalk_zero (k s1 m1 : ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (D : ℕ)
    (M : ByteArray) : pwalk k s1 m1 visit 0 D M = M := rfl

theorem pwalk_succ (k s1 m1 : ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray) (n D : ℕ)
    (M : ByteArray) : pwalk k s1 m1 visit (n + 1) D M =
      if M.get! (cidxF k s1 m1 D) = 0 then
        if (visit n (excF m1 D) (M.set! (cidxF k s1 m1 D) 1)).size = 0 then
          visit n (excF m1 D) (M.set! (cidxF k s1 m1 D) 1)
        else (pwalk k s1 m1 visit n (doorF s1 m1 (excF m1 D))
          (visit n (excF m1 D) (M.set! (cidxF k s1 m1 D) 1))).set! (cidxF k s1 m1 D) 0
      else M := by
  rw [← if_size, ← if_bne]
  rfl

theorem pall_nil (w : ℕ → ByteArray → ByteArray) (M : ByteArray) : pall w [] M = M := rfl

theorem pall_cons (w : ℕ → ByteArray → ByteArray) (D : ℕ) (Ds : List ℕ) (M : ByteArray) :
    pall w (D :: Ds) M = if (w D M).size = 0 then w D M else pall w Ds (w D M) := by
  rw [← if_size]
  rfl

theorem pgo_zero (k s1 m1 ds nt t : ℕ) (keep bad : ℕ → ℕ → Bool) (r δ y : ℕ) (M : ByteArray) :
    pgo k s1 m1 ds nt t keep bad 0 r δ y M = ByteArray.empty := rfl

theorem pgo_succ (k s1 m1 ds nt t : ℕ) (keep bad : ℕ → ℕ → Bool) (fuel r δ y : ℕ)
    (M : ByteArray) : pgo k s1 m1 ds nt t keep bad (fuel + 1) r δ y M =
      if bad r δ then ByteArray.empty
      else if keep r δ && gateF ds nt t r y then
        pall (fun D M' => pwalk k s1 m1
            (fun d x M'' => pgo k s1 m1 ds nt t keep bad fuel (r + 1) (δ + d) x M'') (k - 1) D M')
          (sixL (y % ((m1 + 1) / 256) * 4096) (y / (m1 + 1)) (y / ((m1 + 1) / 16) % 16)
            (y / ((m1 + 1) / 256) % 16)) M
      else M := rfl

/-! ### No part of the search leaves a new mark -/

theorem pwalk_sub (k s1 m1 : ℕ) (visit : ℕ → ℕ → ByteArray → ByteArray)
    (hv : ∀ d x M, Sub (visit d x M) M) :
    ∀ (n D : ℕ) (M : ByteArray), Sub (pwalk k s1 m1 visit n D M) M := by
  intro n
  induction n with
  | zero =>
    intro D M
    rw [pwalk_zero]
    exact Sub.refl M
  | succ n ih =>
    intro D M
    rw [pwalk_succ]
    by_cases h0 : M.get! (cidxF k s1 m1 D) = 0
    · rw [if_pos h0]
      by_cases hz : (visit n (excF m1 D) (M.set! (cidxF k s1 m1 D) 1)).size = 0
      · rw [if_pos hz]
        exact sub_of_size_zero hz M
      · rw [if_neg hz]
        exact sub_clear ((ih _ _).trans (hv _ _ _))
    · rw [if_neg h0]
      exact Sub.refl M

theorem pall_sub (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Sub (w D M) M) :
    ∀ (Ds : List ℕ) (M : ByteArray), Sub (pall w Ds M) M
  | [], M => Sub.refl M
  | D :: Ds, M => by
    rw [pall_cons]
    by_cases hz : (w D M).size = 0
    · rw [if_pos hz]
      exact hw D M
    · rw [if_neg hz]
      exact (pall_sub w hw Ds _).trans (hw D M)

theorem pgo_sub (k s1 m1 ds nt t : ℕ) (keep bad : ℕ → ℕ → Bool) :
    ∀ (fuel r δ y : ℕ) (M : ByteArray), Sub (pgo k s1 m1 ds nt t keep bad fuel r δ y M) M := by
  intro fuel
  induction fuel with
  | zero =>
    intro r δ y M
    rw [pgo_zero]
    exact sub_of_size_zero ByteArray.size_empty M
  | succ fuel ih =>
    intro r δ y M
    rw [pgo_succ]
    by_cases hb : bad r δ = true
    · rw [if_pos hb]
      exact sub_of_size_zero ByteArray.size_empty M
    · rw [if_neg hb]
      by_cases hc : (keep r δ && gateF ds nt t r y) = true
      · rw [if_pos hc]
        exact pall_sub _
          (fun D M' => pwalk_sub k s1 m1 _ (fun d x M'' => ih _ _ _ _) _ _ _) _ _
      · rw [if_neg hc]
        exact Sub.refl M

/-! ### The search follows a chain -/

theorem code_doorF {k : ℕ} (hk : 2 ≤ k) (hk15 : k ≤ 15) {a b : List ℕ} (ha : PermW k a)
    (h : DoorEq k a b) :
    doorF (4 * (k - 1)) (16 ^ (k - 1) - 1) (exc k (code a)) = code b := by
  rw [doorF_eq k _ hk]
  exact code_door hk hk15 ha h

/-- The walk that starts at the first block of a piece `v :: R` whose classes are new finds what
the search below the chain extended by that piece finds. -/
theorem pwalk_complete (k : ℕ) (hk : 2 ≤ k) (hk15 : k ≤ 15)
    (visit : ℕ → ℕ → ByteArray → ByteArray) (hsub : ∀ d x M, Sub (visit d x M) M) :
    ∀ (R : List (List ℕ)) (n : ℕ) (v : List ℕ) (M : ByteArray) (used : List (List ℕ)),
      R.length ≤ n → (∀ w ∈ v :: R, PermW k w) → List.IsChain (DoorEq k) (v :: R) →
      MInv k M used → (∀ u ∈ used, PermW k u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      (∀ M', MInv k M' (used ++ v :: R) →
        (visit (n - R.length) (exc k (code ((v :: R).getLast (List.cons_ne_nil v R)))) M').size
          = 0) →
      (pwalk k (4 * (k - 1)) (16 ^ (k - 1) - 1) visit (n + 1) (code v) M).size = 0 := by
  intro R
  induction R with
  | nil =>
    intro n v M used _ hperm _ hM hused hnew _ hfin
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked_of_new (by omega) hk15 hM hused hv
      (fun u hu => hnew u hu v List.mem_cons_self)
    have hf : (visit n (exc k (code v)) (M.set! ci(k, code v) 1)).size = 0 :=
      hfin _ (minv_set hM v)
    rw [pwalk_succ, if_pos h0, excF_eq, if_pos hf]
    exact hf
  | cons v' R' ih =>
    intro n v M used hn hperm hdoor hM hused hnew hpw hfin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := unmarked_of_new (by omega) hk15 hM hused hv
      (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    have hused' : ∀ u ∈ used ++ [v], PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hused u h
      · rw [List.mem_singleton.mp h]
        exact hv
    rw [pwalk_succ, if_pos h0, excF_eq]
    by_cases hz : (visit (m + 1) (exc k (code v)) (M.set! ci(k, code v) 1)).size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz, ByteArray.size_set!, code_doorF hk hk15 hv hdc.1]
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

/-- One of the calls of `pall` is found: then `pall` is found, if the property `P` that this
call needs survives the calls before it. -/
theorem pall_found (w : ℕ → ByteArray → ByteArray) (hw : ∀ D M, Sub (w D M) M)
    (P : ByteArray → Prop) (hP : ∀ M' M, Sub M' M → P M → P M') (D : ℕ)
    (hD : ∀ M, P M → (w D M).size = 0) :
    ∀ (Ds : List ℕ) (M : ByteArray), D ∈ Ds → P M → (pall w Ds M).size = 0
  | [], _, h, _ => by cases h
  | D0 :: Ds, M, h, hM => by
    rw [pall_cons]
    by_cases hz : (w D0 M).size = 0
    · rw [if_pos hz]
      exact hz
    · rw [if_neg hz]
      rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hD
        exact absurd (hD M hM) hz
      · exact pall_found w hw P hP D hD Ds _ h' (hP _ _ (hw D0 M) hM)

/-- What the rule says along the pieces `rest` that continue a chain with `r` pieces, total
deficit `δ` and last entry `last`: the chain and all the chains on the way to the end satisfy
`keep` and pass the gate, and the chain at the end is `bad`. -/
def Along (k : ℕ) (keep bad gate : ℕ → ℕ → Bool) :
    ℕ → ℕ → List ℕ → List (List (List ℕ)) → Prop
  | r, δ, _, [] => bad r δ = true
  | _, _, _, [] :: _ => False
  | r, δ, last, (v :: R) :: rest =>
    keep r δ = true ∧ gate r (exc k (code last)) = true ∧
      Along k keep bad gate (r + 1) (δ + (k - 2 - R.length))
        ((v :: R).getLast (List.cons_ne_nil v R)) rest

theorem pow_div16 (k : ℕ) (hk : 2 ≤ k) : 16 ^ (k - 1) / 16 = 16 ^ (k - 2) := by
  have e : k - 1 = k - 2 + 1 := by omega
  rw [e, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem pow_div256 (k : ℕ) (hk : 3 ≤ k) : 16 ^ (k - 1) / 256 = 16 ^ (k - 3) := by
  have e : k - 1 = k - 3 + 2 := by omega
  have h : (16 : ℕ) ^ 2 = 256 := by norm_num
  rw [e, pow_add, h, Nat.mul_div_cancel _ (by norm_num)]

/-- The search finds the end of a chain of which it has reached a prefix, if the rule holds
along the rest of the chain. -/
theorem pgo_complete (k : ℕ) (hk : 3 ≤ k) (hk15 : k ≤ 15) (ds nt t : ℕ)
    (keep bad : ℕ → ℕ → Bool) :
    ∀ (fuel : ℕ) (rest : List (List (List ℕ))) (r δ : ℕ) (M : ByteArray) (last : List ℕ)
      (used : List (List ℕ)),
      PermW k last → (∀ u ∈ used, PermW k u) → MInv k M used → Cont k last used rest →
      Along k keep bad (gateF ds nt t) r δ last rest →
      (pgo k (4 * (k - 1)) (16 ^ (k - 1) - 1) ds nt t keep bad fuel r δ (exc k (code last))
        M).size = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intros
    rw [pgo_zero]
    exact ByteArray.size_empty
  | succ fuel ih =>
    intro rest r δ M last used hlast hused hM hcont halong
    rw [pgo_succ]
    by_cases hb : bad r δ = true
    · rw [if_pos hb]
      exact ByteArray.size_empty
    · rw [if_neg hb]
      cases rest with
      | nil => exact absurd halong hb
      | cons Q rest' =>
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hseam, hdoor, hnew, hpw, hcont'⟩ := hcont
          obtain ⟨hkeep, hgate, halong'⟩ := halong
          have hc : (keep r δ && gateF ds nt t r (exc k (code last))) = true := by
            rw [hkeep, hgate]
            rfl
          rw [if_pos hc]
          have hx : PermW k (last.rotate (k - 1)) := hlast.rotate _
          have hv : PermW k v := hperm v List.mem_cons_self
          obtain ⟨a, b, c0, Y, t0, t1, t2, hxe, hYl, hve, ht0, ht1, ht2, h01, h02, h12⟩ :=
            seam_cases hk hx hv hseam
          have hy' : exc k (code last) = code (a :: b :: c0 :: Y) := by
            rw [exc_code k last hlast.2.1 (hlast.lt16 hk15) (by omega), hxe]
          have hd : ∀ z ∈ a :: b :: c0 :: Y, z < 16 := by
            rw [← hxe]
            exact hx.lt16 hk15
          obtain ⟨hp0, hp1, hp2, hp3⟩ := six_parts k a b c0 Y hYl hd hk
          simp only [pw_eq] at hp0 hp1 hp2 hp3
          have hcv : code v = code Y * 4096 + (t0 * 256 + t1 * 16 + t2) := by
            rw [hve, code_append3]
          have hused' : ∀ u ∈ used ++ v :: R, PermW k u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          rw [m1_succ, pow_div256 k hk, pow_div16 k (by omega), hy', hp0, hp1, hp2, hp3]
          refine pall_found _
            (fun D M' => pwalk_sub k _ _ _ (fun d x M'' => pgo_sub _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _)
            (fun M' => MInv k M' used) (fun M' M hs hM => hM.sub hs) (code v) ?_ _ _ ?_ hM
          · intro M' hM'
            have h := pwalk_complete k (by omega) hk15
              (fun d x M'' => pgo k (4 * (k - 1)) (16 ^ (k - 1) - 1) ds nt t keep bad fuel
                (r + 1) (δ + d) x M'')
              (fun d x M'' => pgo_sub _ _ _ _ _ _ _ _ _ _ _ _ _) R (k - 2) v M' used hR hperm
              hdoor hM' hused hnew hpw
              (by
                intro M'' hM''
                exact ih rest' _ _ M'' _ (used ++ v :: R) (hperm _ (List.getLast_mem _)) hused'
                  hM'' hcont' halong')
            rw [show k - 2 + 1 = k - 1 from by omega] at h
            exact h
          · rw [hcv]
            rcases ht0 with rfl | rfl | rfl <;> rcases ht1 with rfl | rfl | rfl <;>
              rcases ht2 with rfl | rfl | rfl <;>
              first
                | exact absurd rfl h01
                | exact absurd rfl h02
                | exact absurd rfl h12
                | simp [sixL]

/-! ### From the hypotheses on prefixes to the rule along the chain -/

/-- A chain whose deficits are `pre` followed by those of `rest`: if every non-empty proper
prefix of the list of deficits satisfies `keep` and the whole list is `bad`, the rule holds along
`rest` (with no gate). -/
theorem along_of_prefix (k : ℕ) (keep bad : ℕ → ℕ → Bool) :
    ∀ (rest : List (List (List ℕ))) (pre : List ℕ) (last : List ℕ),
      (∀ Q ∈ rest, Q ≠ []) → pre ≠ [] →
      (∀ u w, pre ++ rest.map (fun Q => k - 1 - Q.length) = u ++ w → u ≠ [] → w ≠ [] →
        keep u.length u.sum = true) →
      bad (pre ++ rest.map (fun Q => k - 1 - Q.length)).length
        (pre ++ rest.map (fun Q => k - 1 - Q.length)).sum = true →
      Along k keep bad (fun _ _ => true) pre.length pre.sum last rest
  | [], pre, last, _, _, _, hbad => by
    simpa [Along] using hbad
  | [] :: rest, pre, last, hne, _, _, _ => absurd rfl (hne [] List.mem_cons_self)
  | (v :: R) :: rest, pre, last, hne, hpre, hkeep, hbad => by
    have hd : k - 1 - (v :: R).length = k - 2 - R.length := by
      simp only [List.length_cons]
      omega
    have e : pre ++ ((v :: R) :: rest).map (fun Q => k - 1 - Q.length) =
        (pre ++ [k - 2 - R.length]) ++ rest.map (fun Q => k - 1 - Q.length) := by
      simp only [List.map_cons, hd, List.append_assoc, List.cons_append, List.nil_append]
    refine ⟨hkeep pre _ rfl hpre (by simp), rfl, ?_⟩
    rw [e] at hkeep hbad
    have h := along_of_prefix k keep bad rest (pre ++ [k - 2 - R.length])
      ((v :: R).getLast (List.cons_ne_nil v R)) (fun Q hQ => hne Q (List.mem_cons_of_mem _ hQ))
      (by simp) hkeep hbad
    simpa using h

theorem gateF_of_ne {ds nt t r y : ℕ} (h : r ≠ ds) : gateF ds nt t r y = true := by
  simp [gateF, h]

theorem gateF_self (ds nt r y : ℕ) : gateF ds nt (y / 16 % nt) r y = true := by
  simp [gateF]

/-- Beyond the depth of the gate every part of the search is the whole search. -/
theorem along_gate_gt (k : ℕ) (keep bad : ℕ → ℕ → Bool) (ds nt t : ℕ) :
    ∀ (rest : List (List (List ℕ))) (r δ : ℕ) (last : List ℕ), ds < r →
      Along k keep bad (fun _ _ => true) r δ last rest →
      Along k keep bad (gateF ds nt t) r δ last rest
  | [], _, _, _, _, h => h
  | [] :: _, _, _, _, _, h => h.elim
  | (v :: R) :: rest, r, δ, _, hr, h =>
    ⟨h.1, gateF_of_ne (by omega), along_gate_gt k keep bad ds nt t rest (r + 1) _ _ (by omega)
      h.2.2⟩

/-- A chain along which the rule holds passes the gate of one of the `nt` parts. -/
theorem along_gate (k : ℕ) (keep bad : ℕ → ℕ → Bool) (ds nt : ℕ) (hnt : 0 < nt) :
    ∀ (rest : List (List (List ℕ))) (r δ : ℕ) (last : List ℕ),
      Along k keep bad (fun _ _ => true) r δ last rest →
      ∃ t, t < nt ∧ Along k keep bad (gateF ds nt t) r δ last rest
  | [], _, _, _, h => ⟨0, hnt, h⟩
  | [] :: _, _, _, _, h => h.elim
  | (v :: R) :: rest, r, δ, last, h => by
    by_cases hr : r = ds
    · exact ⟨exc k (code last) / 16 % nt, Nat.mod_lt _ hnt, h.1, gateF_self _ _ _ _,
        along_gate_gt k keep bad ds nt _ rest (r + 1) _ _ (by omega) h.2.2⟩
    · obtain ⟨t, ht, hA⟩ := along_gate k keep bad ds nt hnt rest (r + 1) _ _ h.2.2
      exact ⟨t, ht, h.1, gateF_of_ne hr, hA⟩

/-! ### The statement for chains of words -/

/-- No chain of words all of whose non-empty proper prefixes satisfy `keep` is `bad`.  The
arguments of `keep` and `bad` are the number of pieces and the total deficit. -/
def PStatement (k : ℕ) (keep bad : ℕ → ℕ → Bool) : Prop :=
  ∀ L : List (List (List ℕ)), IsWChain k L → L ≠ [] →
    (∀ u w, wdef k L = u ++ w → u ≠ [] → w ≠ [] → keep u.length u.sum = true) →
    bad (wdef k L).length (wdef k L).sum = false

theorem pstatement_of_parts {k sz fuel ds nt : ℕ} {keep bad : ℕ → ℕ → Bool} (hk : 3 ≤ k)
    (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ t, t < nt → psearchPart k sz keep bad fuel ds nt t = false) :
    PStatement k keep bad := by
  intro L hL hne hkeep
  by_contra hbad
  have hbad' : bad (wdef k L).length (wdef k L).sum = true := by simpa using hbad
  cases L with
  | nil => exact hne rfl
  | cons Q0 rest =>
    have hQ0 : Q0 ≠ [] := hL.pieces_ne Q0 List.mem_cons_self
    obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    have hv0 : PermW k v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
    have hL' := hL.relabel hv0
    rw [← wdef_relabChain k v0] at hkeep hbad'
    have hshape : relabChain v0 ((v0 :: R0) :: rest) =
        (List.range' 1 k :: R0.map (List.map (relab v0))) :: relabChain v0 rest := by
      simp [relabChain, map_relab_self hv0.1, hv0.2.1]
    rw [hshape] at hL' hkeep hbad'
    generalize R0.map (List.map (relab v0)) = R1 at hL' hkeep hbad'
    generalize relabChain v0 rest = rest1 at hL' hkeep hbad'
    have hperm : ∀ w ∈ List.range' 1 k :: R1, PermW k w := hL'.words _ List.mem_cons_self
    have hcl : List.Pairwise (fun a b => ¬ a ~r b)
        ((List.range' 1 k :: R1) ++ rest1.flatten) := by
      have := hL'.classes
      rw [List.flatten_cons] at this
      exact this
    have hcl' := List.pairwise_append.mp hcl
    have hsz := hL'.size_le _ List.mem_cons_self
    have hdoor := door_chain (by omega) _ hperm (hL'.doors _ List.mem_cons_self) hcl'.1
    have hcont := cont_of_chain (by omega) rest1 (List.range' 1 k :: R1)
      (List.range' 1 k :: R1) (List.cons_ne_nil _ _) hL' hcl'.2.2
    have hd : k - 1 - (List.range' 1 k :: R1).length = k - 2 - R1.length := by
      simp only [List.length_cons]
      omega
    have hwd : wdef k ((List.range' 1 k :: R1) :: rest1) =
        [k - 2 - R1.length] ++ rest1.map (fun Q => k - 1 - Q.length) := by
      simp only [wdef, List.map_cons, hd, List.cons_append, List.nil_append]
    rw [hwd] at hkeep hbad'
    have hA := along_of_prefix k keep bad rest1 [k - 2 - R1.length]
      ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _))
      (fun Q hQ => hL'.pieces_ne Q (List.mem_cons_of_mem _ hQ)) (by simp) hkeep hbad'
    have hA' : Along k keep bad (fun _ _ => true) 1 (k - 2 - R1.length)
        ((List.range' 1 k :: R1).getLast (List.cons_ne_nil _ _)) rest1 := by
      simpa using hA
    obtain ⟨t, ht, hAt⟩ := along_gate k keep bad ds nt hnt rest1 _ _ _ hA'
    have hfound : (pwalk k (4 * (k - 1)) (16 ^ (k - 1) - 1)
        (fun d x M => pgo k (4 * (k - 1)) (16 ^ (k - 1) - 1) ds nt t keep bad fuel 1 d x M)
        (k - 1) (code (List.range' 1 k)) (marks0 sz)).size = 0 := by
      have h := pwalk_complete k (by omega) hk15
        (fun d x M => pgo k (4 * (k - 1)) (16 ^ (k - 1) - 1) ds nt t keep bad fuel 1 d x M)
        (fun d x M => pgo_sub _ _ _ _ _ _ _ _ _ _ _ _ _) R1 (k - 2) (List.range' 1 k) (marks0 sz)
        [] (by simp only [List.length_cons] at hsz; omega) hperm hdoor (minv_marks0 k sz)
        (by simp) (by simp) hcl'.1
        (by
          intro M' hM'
          exact pgo_complete k hk hk15 ds nt t keep bad fuel rest1 1 _ M' _ _
            (hperm _ (List.getLast_mem _)) (by simpa using hperm) hM' (by simpa using hcont) hAt)
      rw [show k - 2 + 1 = k - 1 from by omega] at h
      exact h
    have htrue : psearchPart k sz keep bad fuel ds nt t = true := by
      unfold psearchPart
      rw [idcF_eq, idc_code, hfound]
      rfl
    rw [hs t ht] at htrue
    cases htrue

/-- The parts evaluated as tasks are the parts. -/
theorem psearchPar_false {k sz fuel ds nt : ℕ} {keep bad : ℕ → ℕ → Bool}
    (h : psearchPar k sz keep bad fuel ds nt = false) :
    ∀ t, t < nt → psearchPart k sz keep bad fuel ds nt t = false := by
  intro t ht
  unfold psearchPar at h
  rw [List.any_map, List.any_eq_false] at h
  have h1 := h t (List.mem_range.mpr ht)
  simpa [Task.spawn] using h1

/-- The search proves the prefix statement. -/
theorem pstatement_of_search {k sz fuel ds nt : ℕ} {keep bad : ℕ → ℕ → Bool} (hk : 3 ≤ k)
    (hk15 : k ≤ 15) (hnt : 0 < nt) (hs : psearchPar k sz keep bad fuel ds nt = false) :
    PStatement k keep bad :=
  pstatement_of_parts hk hk15 hnt (psearchPar_false hs)

end S
end SuperpermLowerBounds

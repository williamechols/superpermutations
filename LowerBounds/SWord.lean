import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import LowerBounds.SSearch

/-!
# Words and their codes

The search of `SSearch.lean` works on numbers.  This file relates the numbers to words:

* `code w` reads a word (a list of symbols below 16) as a hexadecimal number, first symbol first;
* the arithmetic of `SSearch.lean` (`rotl`, `exc`, `doorc`, the six numbers of `six`, `idc`) is
  what rotation, the exit, the door, the six words after a seam and the word `1 2 … k` are on
  codes (`rotl_code`, `exc_code`, `doorc_code`, `six_code`, `idc_code`);
* `canon` maps a code to the code of a rotation of the same word, so two words with the same
  `canon` are rotations of each other (`isRotated_of_canon_eq`);
* `PermW k w`: the word `w` is a permutation of `1 … k`; `WLink k d u v`: the overlap of the exit
  of `u` and of `v`;
* what the overlaps leave: the door inside a piece (`door_of_link`) and six words at a seam
  (`seam_cases`);
* relabelling of the symbols (`relab`): every permutation word can be made the word `1 2 … k`.

No permutations as a type, no paths: only lists of natural numbers.
-/

namespace SuperpermLowerBounds
namespace S

/-! ### Codes -/

/-- The word read as hexadecimal digits, first symbol first. -/
def code (w : List ℕ) : ℕ := w.foldl (fun acc a => acc * 16 + a) 0

theorem foldl_code (c : ℕ) (w : List ℕ) :
    w.foldl (fun acc a => acc * 16 + a) c = c * 16 ^ w.length + code w := by
  induction w generalizing c with
  | nil => simp [code]
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons, code]
    rw [ih, ih (0 * 16 + a)]
    ring

theorem code_nil : code [] = 0 := rfl

theorem code_cons (a : ℕ) (t : List ℕ) : code (a :: t) = a * 16 ^ t.length + code t := by
  show List.foldl (fun acc a => acc * 16 + a) (0 * 16 + a) t = _
  rw [foldl_code]
  ring

theorem code_append (u v : List ℕ) : code (u ++ v) = code u * 16 ^ v.length + code v := by
  show List.foldl (fun acc a => acc * 16 + a) 0 (u ++ v) = _
  rw [List.foldl_append, foldl_code]
  rfl

theorem code_singleton (a : ℕ) : code [a] = a := by simp [code]

theorem code_lt (w : List ℕ) (h : ∀ a ∈ w, a < 16) : code w < 16 ^ w.length := by
  induction w with
  | nil => simp [code]
  | cons a t ih =>
    rw [code_cons, List.length_cons, pow_succ]
    have ha := h a List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have h1 : a * 16 ^ t.length ≤ 15 * 16 ^ t.length := Nat.mul_le_mul_right _ (by omega)
    omega

theorem mul_add_div' {x y B : ℕ} (hy : y < B) : (x * B + y) / B = x := by
  have hB : 0 < B := by omega
  rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hy, Nat.add_zero]

theorem mul_add_mod' {x y B : ℕ} (hy : y < B) : (x * B + y) % B = y := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]

/-- Words of the same length with the same code are equal. -/
theorem code_inj : ∀ (u v : List ℕ), u.length = v.length → (∀ a ∈ u, a < 16) →
    (∀ a ∈ v, a < 16) → code u = code v → u = v
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: s, b :: t, h, hu, hv, hc => by
    have hl : s.length = t.length := by simpa using h
    have hus : ∀ x ∈ s, x < 16 := fun x hx => hu x (List.mem_cons_of_mem _ hx)
    have hvt : ∀ x ∈ t, x < 16 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    rw [code_cons, code_cons, hl] at hc
    have hs := code_lt s hus
    have ht := code_lt t hvt
    rw [hl] at hs
    have h1 : a = b := by
      have := congrArg (fun z => z / 16 ^ t.length) hc
      simpa only [mul_add_div' hs, mul_add_div' ht] using this
    have h2 : code s = code t := by
      have := congrArg (fun z => z % 16 ^ t.length) hc
      simpa only [mul_add_mod' hs, mul_add_mod' ht] using this
    rw [h1, code_inj s t hl hus hvt h2]

theorem pw_eq (n : ℕ) : pw n = 16 ^ n := rfl

/-- `rotl` is rotation of words. -/
theorem rotl_code (k : ℕ) (w : List ℕ) (hw : w.length = k) (hd : ∀ a ∈ w, a < 16) (i : ℕ)
    (hi : i ≤ k) : rotl k (code w) i = code (w.rotate i) := by
  have hlt : (w.take i).length = i := by rw [List.length_take]; omega
  have hld : (w.drop i).length = k - i := by rw [List.length_drop]; omega
  have hrot : w.rotate i = w.drop i ++ w.take i := List.rotate_eq_drop_append_take (by omega)
  have hcv : code (w.drop i) < 16 ^ (k - i) := by
    rw [← hld]
    exact code_lt _ (fun a ha => hd a (List.mem_of_mem_drop ha))
  have hc : code w = code (w.take i) * 16 ^ (k - i) + code (w.drop i) := by
    conv_lhs => rw [← List.take_append_drop i w]
    rw [code_append, hld]
  show (code w % 16 ^ (k - i)) * 16 ^ i + code w / 16 ^ (k - i) = _
  rw [hrot, code_append, hlt, hc, mul_add_mod' hcv, mul_add_div' hcv]

theorem exc_eq_rotl (k c : ℕ) (hk : 1 ≤ k) : exc k c = rotl k c (k - 1) := by
  show (c % 16) * 16 ^ (k - 1) + c / 16 =
    (c % 16 ^ (k - (k - 1))) * 16 ^ (k - 1) + c / 16 ^ (k - (k - 1))
  have h1 : k - (k - 1) = 1 := by omega
  rw [h1, pow_one]

/-- `exc` is the exit: rotation by `k - 1`. -/
theorem exc_code (k : ℕ) (w : List ℕ) (hw : w.length = k) (hd : ∀ a ∈ w, a < 16) (hk : 1 ≤ k) :
    exc k (code w) = code (w.rotate (k - 1)) := by
  rw [exc_eq_rotl k _ hk, rotl_code k w hw hd (k - 1) (by omega)]

/-- The door of a word: the first two symbols move to the end, in reverse order (the same
expression as Hunter's `door`). -/
def doorW (x : List ℕ) : List ℕ := x.drop 2 ++ [x.getD 1 0, x.getD 0 0]

theorem doorW_cons (a b : ℕ) (X : List ℕ) : doorW (a :: b :: X) = X ++ [b, a] := rfl

theorem exists_cons_cons {k : ℕ} {x : List ℕ} (hx : x.length = k) (hk : 2 ≤ k) :
    ∃ a b X, x = a :: b :: X ∧ X.length = k - 2 := by
  match x, hx with
  | a :: b :: X, h => exact ⟨a, b, X, rfl, by simp at h; omega⟩
  | [], h => simp at h; omega
  | [_], h => simp at h; omega

theorem exists_cons3 {k : ℕ} {x : List ℕ} (hx : x.length = k) (hk : 3 ≤ k) :
    ∃ a b c X, x = a :: b :: c :: X ∧ X.length = k - 3 := by
  match x, hx with
  | a :: b :: c :: X, h => exact ⟨a, b, c, X, rfl, by simp at h; omega⟩
  | [], h => simp at h; omega
  | [_], h => simp at h; omega
  | [_, _], h => simp at h; omega

/-- `doorc` is the door. -/
theorem doorc_code (k : ℕ) (x : List ℕ) (hx : x.length = k) (hd : ∀ a ∈ x, a < 16) (hk : 2 ≤ k) :
    doorc k (code x) = code (doorW x) := by
  obtain ⟨a, b, X, rfl, hX⟩ := exists_cons_cons hx hk
  have ha : a < 16 := hd a (by simp)
  have hb : b < 16 := hd b (by simp)
  have hcX : code X < 16 ^ (k - 2) := by
    rw [← hX]
    exact code_lt _ (fun c hc => hd c (by simp [hc]))
  have hc : code (a :: b :: X) = (a * 16 + b) * 16 ^ (k - 2) + code X := by
    rw [code_cons, code_cons, List.length_cons, hX, pow_succ]
    ring
  have hp : 16 ^ (k - 1) = 16 ^ (k - 2) * 16 := by
    rw [← pow_succ]
    congr 1
    omega
  show (code (a :: b :: X) % 16 ^ (k - 2)) * 256 + (code (a :: b :: X) / 16 ^ (k - 2) % 16) * 16
    + code (a :: b :: X) / 16 ^ (k - 1) = _
  rw [hp, ← Nat.div_div_eq_div_mul, hc, mul_add_mod' hcX, mul_add_div' hcX, doorW_cons,
    code_append, code_cons, code_singleton]
  have h1 : (a * 16 + b) % 16 = b := by omega
  have h2 : (a * 16 + b) / 16 = a := by omega
  rw [h1, h2]
  simp only [List.length_cons, List.length_nil]
  norm_num
  omega

/-- The parts of the code of a word that the six words after a seam are made of. -/
theorem six_parts (k : ℕ) (a b c : ℕ) (Y : List ℕ) (hY : Y.length = k - 3)
    (hd : ∀ z ∈ a :: b :: c :: Y, z < 16) (hk : 3 ≤ k) :
    code (a :: b :: c :: Y) % pw (k - 3) = code Y ∧ code (a :: b :: c :: Y) / pw (k - 1) = a ∧
      code (a :: b :: c :: Y) / pw (k - 2) % 16 = b ∧
      code (a :: b :: c :: Y) / pw (k - 3) % 16 = c := by
  have ha : a < 16 := hd a (by simp)
  have hb : b < 16 := hd b (by simp)
  have hc' : c < 16 := hd c (by simp)
  have hcY : code Y < 16 ^ (k - 3) := by
    rw [← hY]
    exact code_lt _ (fun z hz => hd z (by simp [hz]))
  have hc : code (a :: b :: c :: Y) = ((a * 16 + b) * 16 + c) * 16 ^ (k - 3) + code Y := by
    rw [code_cons, code_cons, code_cons, List.length_cons, List.length_cons, hY, pow_succ,
      pow_succ]
    ring
  have hp1 : 16 ^ (k - 1) = 16 ^ (k - 3) * 256 := by
    have : k - 1 = k - 3 + 2 := by omega
    rw [this, pow_add]
    norm_num
  have hp2 : 16 ^ (k - 2) = 16 ^ (k - 3) * 16 := by
    have : k - 2 = k - 3 + 1 := by omega
    rw [this, pow_succ]
  simp only [pw_eq]
  rw [hp1, hp2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hc, mul_add_mod' hcY,
    mul_add_div' hcY]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> omega

theorem code_append3 (Y : List ℕ) (p q r : ℕ) :
    code (Y ++ [p, q, r]) = code Y * 4096 + (p * 256 + q * 16 + r) := by
  rw [code_append, code_cons, code_cons, code_singleton]
  simp only [List.length_cons, List.length_nil]
  norm_num
  ring

/-- `idc k` is the code of the word `1 2 … k`. -/
theorem idc_code : ∀ n : ℕ, idc n = code (List.range' 1 n)
  | 0 => rfl
  | n + 1 => by
    rw [idc_succ, idc_code n, List.range'_concat, code_append, code_singleton]
    simp only [List.length_cons, List.length_nil]
    omega

/-- Two words with the same `canon` are rotations of each other. -/
theorem isRotated_of_canon_eq {k : ℕ} {u v : List ℕ} (hu : u.length = k) (hv : v.length = k)
    (hdu : ∀ a ∈ u, a < 16) (hdv : ∀ a ∈ v, a < 16)
    (h : canon k (code u) = canon k (code v)) : u ~r v := by
  unfold canon at h
  rw [rotl_code k u hu hdu _ (by show k - 1 - _ ≤ k; omega),
    rotl_code k v hv hdv _ (by show k - 1 - _ ≤ k; omega)] at h
  have he := code_inj _ _ (by rw [List.length_rotate, List.length_rotate, hu, hv])
    (fun a ha => hdu a (List.mem_rotate.mp ha)) (fun a ha => hdv a (List.mem_rotate.mp ha)) h
  have h1 : u ~r u.rotate (Nat.sub (Nat.sub k 1) (pos k (code u))) := ⟨_, rfl⟩
  have h2 : v ~r v.rotate (Nat.sub (Nat.sub k 1) (pos k (code v))) := ⟨_, rfl⟩
  rw [he] at h1
  exact h1.trans h2.symm

/-! ### Permutation words and overlaps -/

/-- The word `w` is a permutation of `1 … k`. -/
def PermW (k : ℕ) (w : List ℕ) : Prop := w.Nodup ∧ w.length = k ∧ ∀ a, a ∈ w ↔ 1 ≤ a ∧ a ≤ k

theorem PermW.lt16 {k : ℕ} {w : List ℕ} (h : PermW k w) (hk : k ≤ 15) : ∀ a ∈ w, a < 16 := by
  intro a ha
  have := (h.2.2 a).mp ha
  omega

theorem PermW.rotate {k : ℕ} {w : List ℕ} (h : PermW k w) (n : ℕ) : PermW k (w.rotate n) :=
  ⟨List.nodup_rotate.mpr h.1, by rw [List.length_rotate]; exact h.2.1,
    fun a => by rw [List.mem_rotate]; exact h.2.2 a⟩

/-- The exit of the block entered at `u` (the word `u` rotated by `k - 1`) and the word `v`
overlap in `k - d` symbols. -/
def WLink (k d : ℕ) (u v : List ℕ) : Prop := (u.rotate (k - 1)).drop d = v.take (k - d)

theorem list_len2 {l : List ℕ} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t =>
      cases t with
      | nil => exact ⟨a, b, rfl⟩
      | cons c t => simp at h

theorem list_len3 {l : List ℕ} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    obtain ⟨b, c, rfl⟩ := list_len2 (l := t) (by simpa using h)
    exact ⟨a, b, c, rfl⟩

/-- Inside a piece: an overlap of `k - 2` symbols leaves the door of the exit, because the other
word with this overlap is a rotation of `u`. -/
theorem door_of_link {k : ℕ} (hk : 3 ≤ k) {u v : List ℕ} (hu : PermW k u) (hv : PermW k v)
    (h : WLink k 2 u v) (hne : ¬ u ~r v) : v = doorW (u.rotate (k - 1)) := by
  have hxp : PermW k (u.rotate (k - 1)) := hu.rotate _
  obtain ⟨a, b, X, hxe, hXl⟩ := exists_cons_cons hxp.2.1 (by omega)
  unfold WLink at h
  rw [hxe] at h hxp ⊢
  have hX : X = v.take (k - 2) := h
  have hv2 : v = X ++ v.drop (k - 2) := by
    rw [hX]
    exact (List.take_append_drop _ _).symm
  have hlen : (v.drop (k - 2)).length = 2 := by
    rw [List.length_drop, hv.2.1]
    omega
  obtain ⟨t0, t1, ht⟩ := list_len2 hlen
  rw [ht] at hv2
  have hvn : (X ++ [t0, t1]).Nodup := hv2 ▸ hv.1
  have hmem : ∀ t, t ∈ [t0, t1] → t = a ∨ t = b := by
    intro t ht'
    have h1 : t ∈ v := by
      rw [hv2]
      exact List.mem_append_right _ ht'
    have h2 : t ∈ a :: b :: X := (hxp.2.2 t).mpr ((hv.2.2 t).mp h1)
    rcases List.mem_cons.mp h2 with h3 | h3
    · exact Or.inl h3
    · rcases List.mem_cons.mp h3 with h4 | h4
      · exact Or.inr h4
      · exact absurd ht' (fun h5 => List.disjoint_of_nodup_append hvn h4 h5)
  have hn2 : [t0, t1].Nodup := List.Nodup.of_append_right hvn
  have h01 : t0 ≠ t1 := by
    rintro rfl
    simp at hn2
  rcases hmem t0 (by simp) with h0 | h0 <;> rcases hmem t1 (by simp) with h1 | h1
  · exact absurd (h0.trans h1.symm) h01
  · exfalso
    apply hne
    refine ⟨k - 1 + 2, ?_⟩
    rw [← List.rotate_rotate, hxe, hv2, h0, h1]
    simp [List.rotate_cons_succ]
  · rw [hv2, h0, h1]
    rfl
  · exact absurd (h0.trans h1.symm) h01

/-- At a seam: an overlap of `k - 3` symbols leaves the six words made of the rest of the exit
followed by its first three symbols in some order. -/
theorem seam_cases {k : ℕ} (hk : 3 ≤ k) {x v : List ℕ} (hx : PermW k x) (hv : PermW k v)
    (h : x.drop 3 = v.take (k - 3)) :
    ∃ a b c Y t0 t1 t2, x = a :: b :: c :: Y ∧ Y.length = k - 3 ∧ v = Y ++ [t0, t1, t2] ∧
      (t0 = a ∨ t0 = b ∨ t0 = c) ∧ (t1 = a ∨ t1 = b ∨ t1 = c) ∧ (t2 = a ∨ t2 = b ∨ t2 = c) ∧
      t0 ≠ t1 ∧ t0 ≠ t2 ∧ t1 ≠ t2 := by
  obtain ⟨a, b, c, Y, hxe, hYl⟩ := exists_cons3 hx.2.1 hk
  rw [hxe] at h hx
  have hY : Y = v.take (k - 3) := h
  have hv2 : v = Y ++ v.drop (k - 3) := by
    rw [hY]
    exact (List.take_append_drop _ _).symm
  have hlen : (v.drop (k - 3)).length = 3 := by
    rw [List.length_drop, hv.2.1]
    omega
  obtain ⟨t0, t1, t2, ht⟩ := list_len3 hlen
  rw [ht] at hv2
  have hvn : (Y ++ [t0, t1, t2]).Nodup := hv2 ▸ hv.1
  have hmem : ∀ t, t ∈ [t0, t1, t2] → t = a ∨ t = b ∨ t = c := by
    intro t ht'
    have h1 : t ∈ v := by
      rw [hv2]
      exact List.mem_append_right _ ht'
    have h2 : t ∈ a :: b :: c :: Y := (hx.2.2 t).mpr ((hv.2.2 t).mp h1)
    simp only [List.mem_cons] at h2
    rcases h2 with h3 | h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h3)
    · exact absurd ht' (fun h5 => List.disjoint_of_nodup_append hvn h3 h5)
  have hn3 : [t0, t1, t2].Nodup := List.Nodup.of_append_right hvn
  have h01 : t0 ≠ t1 := by
    rintro rfl
    simp at hn3
  have h02 : t0 ≠ t2 := by
    rintro rfl
    simp at hn3
  have h12 : t1 ≠ t2 := by
    rintro rfl
    simp at hn3
  exact ⟨a, b, c, Y, t0, t1, t2, hxe, hYl, hv2, hmem t0 (by simp), hmem t1 (by simp),
    hmem t2 (by simp), h01, h02, h12⟩

/-! ### Relabelling of the symbols -/

/-- The relabelling that turns the word `e` into `1 2 … k`: the symbol at position `i` of `e`
(counted from 0) becomes `i + 1`. -/
def relab (e : List ℕ) (a : ℕ) : ℕ := e.idxOf a + 1

/-- Back: `i + 1` becomes the symbol at position `i` of `e`. -/
def unrelab (e : List ℕ) (b : ℕ) : ℕ := e.getD (b - 1) 0

theorem unrelab_relab {e : List ℕ} {a : ℕ} (ha : a ∈ e) : unrelab e (relab e a) = a := by
  have h := List.idxOf_lt_length_of_mem ha
  show e.getD (e.idxOf a + 1 - 1) 0 = a
  rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    List.getElem_idxOf h]
  rfl

theorem relab_range {e : List ℕ} {a : ℕ} (ha : a ∈ e) : 1 ≤ relab e a ∧ relab e a ≤ e.length := by
  have h := List.idxOf_lt_length_of_mem ha
  unfold relab
  omega

theorem map_unrelab_relab {e w : List ℕ} (hw : ∀ a ∈ w, a ∈ e) :
    (w.map (relab e)).map (unrelab e) = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun a ha => unrelab_relab (hw a ha))

/-- The relabelling turns `e` into the word `1 2 … k`. -/
theorem map_relab_self {e : List ℕ} (he : e.Nodup) : e.map (relab e) = List.range' 1 e.length := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < e.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range', relab]
    rw [he.idxOf_getElem i hi]
    omega

theorem PermW.map_relab {k : ℕ} {e w : List ℕ} (he : PermW k e) (hw : PermW k w) :
    PermW k (w.map (S.relab e)) := by
  have hwe : ∀ a ∈ w, a ∈ e := fun a ha => (he.2.2 a).mpr ((hw.2.2 a).mp ha)
  refine ⟨?_, by rw [List.length_map]; exact hw.2.1, ?_⟩
  · apply List.Nodup.map_on _ hw.1
    intro x hx y hy hxy
    have := congrArg (unrelab e) hxy
    rwa [unrelab_relab (hwe x hx), unrelab_relab (hwe y hy)] at this
  · intro b
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have := relab_range (hwe a ha)
      rw [he.2.1] at this
      exact this
    · intro hb
      have hlt : b - 1 < e.length := by
        rw [he.2.1]
        omega
      refine ⟨e[b - 1], (hw.2.2 _).mpr ((he.2.2 _).mp (List.getElem_mem hlt)), ?_⟩
      show e.idxOf e[b - 1] + 1 = b
      rw [he.1.idxOf_getElem (b - 1) hlt]
      omega

theorem WLink.map {k d : ℕ} {u v : List ℕ} (f : ℕ → ℕ) (h : WLink k d u v) :
    WLink k d (u.map f) (v.map f) := by
  unfold WLink at h ⊢
  rw [← List.map_rotate, ← List.map_drop, ← List.map_take, h]

theorem not_isRotated_map_relab {k : ℕ} {e u v : List ℕ} (he : PermW k e) (hu : PermW k u)
    (hv : PermW k v) (h : ¬ u ~r v) : ¬ (u.map (relab e) ~r v.map (relab e)) := by
  rintro ⟨n, hn⟩
  apply h
  refine ⟨n, ?_⟩
  rw [← List.map_rotate] at hn
  have hue : ∀ a ∈ u.rotate n, a ∈ e :=
    fun a ha => (he.2.2 a).mpr ((hu.2.2 a).mp (List.mem_rotate.mp ha))
  have hve : ∀ a ∈ v, a ∈ e := fun a ha => (he.2.2 a).mpr ((hv.2.2 a).mp ha)
  have := congrArg (List.map (unrelab e)) hn
  rwa [map_unrelab_relab hue, map_unrelab_relab hve] at this

end S
end SuperpermLowerBounds

import LowerBounds.PSeq

/-!
# The two sets of tables of `PSearch.lean` satisfy `Enc`

* `encA`: words as codes, arithmetic (`searchA`).  The arithmetic is that of `DSearch.lean`; what
  is new is the list of all permutation codes (`mem_permCodes`) and the overlap test
  (`ovlF_of_wlink`), which replaces the six successors of `DSearch.lean` and serves for links of
  weight 4 as well.
* `encB`: words as indices into the list of permutation codes, tables (`searchB`).  Every table
  is the arithmetic of set A read at the code of the index, so the proof only looks entries up.

`stmt_of_searchA`, `stmt_of_searchB`: a search that answers `false` proves `PStmt`.  The parts of
a search may be evaluated in several ranges (`pa ≤ tp < pb`).

`look3_tab3`: a tabulated rule is the rule.
-/

namespace SuperpermLowerBounds
namespace PS

open S (PermW WLink DoorEq code)

/-! ### The arithmetic is that of `DSearch.lean` -/

theorem idcF_eq : ∀ n : ℕ, idcF n = S.idcF n
  | 0 => rfl
  | n + 1 => by
    show idcF n * 16 + (n + 1) = S.idcF n * 16 + (n + 1)
    rw [idcF_eq n]

theorem canonF_eq (k s1 m1 : ℕ) : ∀ n c : ℕ, canonF k s1 m1 n c = S.canonF k s1 m1 n c
  | 0, _ => rfl
  | n + 1, c => by
    show (if c >>> s1 == k then c else canonF k s1 m1 n ((c &&& m1) * 16 + (c >>> s1))) =
      (if c >>> s1 == k then c else S.canonF k s1 m1 n ((c &&& m1) * 16 + (c >>> s1)))
    rw [canonF_eq k s1 m1 n]

theorem packF_eq (B : ℕ) : ∀ n c : ℕ, packF B n c = S.packF B n c
  | 0, _ => rfl
  | n + 1, c => by
    show packF B n (c / 16) * B + (c % 16 - 1) = S.packF B n (c / 16) * B + (c % 16 - 1)
    rw [packF_eq B n]

theorem cidxF_eq (k s1 m1 c : ℕ) : cidxF k s1 m1 c = S.cidxF k s1 m1 c := by
  show packF k (k - 1) (canonF k s1 m1 k c) = S.packF k (k - 1) (S.canonF k s1 m1 k c)
  rw [canonF_eq, packF_eq]

theorem nxtF_code {k : ℕ} (hk : 2 ≤ k) (hk15 : k ≤ 15) {a b : List ℕ} (ha : PermW k a)
    (h : DoorEq k a b) : nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1) (code a) = code b := by
  show S.doorF (4 * (k - 1)) (16 ^ (k - 1) - 1) (S.excF (16 ^ (k - 1) - 1) (code a)) = code b
  rw [S.excF_eq]
  exact S.code_doorF hk hk15 ha h

/-! ### The list of permutation codes -/

theorem code_concat (p : List ℕ) (a : ℕ) : code (p ++ [a]) = code p * 16 + a := by
  rw [S.code_append, S.code_singleton]
  simp

theorem occF_code (w : List ℕ) (a : ℕ) (hw : ∀ x ∈ w, x < 16)
    (h : occF w.length (code w) a = true) : a ∈ w := by
  induction w using List.reverseRecOn with
  | nil => simp [occF] at h
  | append_singleton p b ih =>
    have hb : b < 16 := hw b (by simp)
    rw [List.length_append, List.length_singleton, code_concat] at h
    simp only [occF, S.mul_add_mod' hb, S.mul_add_div' hb, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · simp [h]
    · exact List.mem_append_left _ (ih (fun x hx => hw x (by simp [hx])) h)

theorem mem_permCodes (k : ℕ) (hk15 : k ≤ 15) : ∀ w : List ℕ, w.Nodup →
    (∀ a ∈ w, 1 ≤ a ∧ a ≤ k) → code w ∈ permCodes k w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro _ _
    simp [permCodes, S.code_nil]
  | append_singleton p a ih =>
    intro hnd hr
    have ha := hr a (by simp)
    have hp := ih (hnd.sublist (List.sublist_append_left p [a]))
      (fun x hx => hr x (by simp [hx]))
    have hnot : a ∉ p := by
      intro h
      have h2 := List.disjoint_of_nodup_append hnd
      exact h2 h (by simp)
    have hocc : occF p.length (code p) a = false := by
      rw [← Bool.not_eq_true]
      intro h
      exact hnot (occF_code p a (fun x hx => by have := hr x (by simp [hx]); omega) h)
    rw [List.length_append, List.length_singleton, code_concat]
    show code p * 16 + a ∈ (permCodes k p.length).flatMap fun c =>
      ((List.range k).filter fun a => !occF p.length c (a + 1)).map fun a => c * 16 + (a + 1)
    refine List.mem_flatMap.mpr ⟨code p, hp, List.mem_map.mpr ⟨a - 1,
      List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, by omega⟩⟩
    rw [show a - 1 + 1 = a from by omega, hocc]
    rfl

theorem mem_perm {k : ℕ} (hk15 : k ≤ 15) {v : List ℕ} (hv : PermW k v) :
    code v ∈ permCodes k k := by
  have h := mem_permCodes k hk15 v hv.1 (fun a ha => (hv.2.2 a).mp ha)
  rwa [hv.2.1] at h

/-! ### The overlap test -/

theorem ovlF_of_wlink {k d : ℕ} (hk : 1 ≤ k) (hk15 : k ≤ 15) (hd : d ≤ k) {u v : List ℕ}
    (hu : PermW k u) (hv : PermW k v) (h : WLink k d u v) :
    ovlF (16 ^ (k - 1) - 1) (16 ^ (k - d)) (16 ^ d) (code u) (code v) = true := by
  have hx : PermW k (u.rotate (k - 1)) := hu.rotate _
  have e1 : excF (16 ^ (k - 1) - 1) (code u) = code (u.rotate (k - 1)) := by
    show S.excF (16 ^ (k - 1) - 1) (code u) = _
    rw [S.excF_eq, S.exc_code k u hu.2.1 (hu.lt16 hk15) hk]
  have e2 : code (u.rotate (k - 1)) % 16 ^ (k - d) = code ((u.rotate (k - 1)).drop d) := by
    have hl : ((u.rotate (k - 1)).drop d).length = k - d := by rw [List.length_drop, hx.2.1]
    have hlt := S.code_lt ((u.rotate (k - 1)).drop d)
      (fun a ha => hx.lt16 hk15 a (List.mem_of_mem_drop ha))
    rw [hl] at hlt
    have e : code (u.rotate (k - 1)) =
        code ((u.rotate (k - 1)).take d) * 16 ^ (k - d) + code ((u.rotate (k - 1)).drop d) := by
      conv_lhs => rw [← List.take_append_drop d (u.rotate (k - 1))]
      rw [S.code_append, hl]
    rw [e]
    exact S.mul_add_mod' hlt
  have e3 : code v / 16 ^ d = code (v.take (k - d)) := by
    have hl : (v.drop (k - d)).length = d := by
      rw [List.length_drop, hv.2.1]
      omega
    have hlt := S.code_lt (v.drop (k - d)) (fun a ha => hv.lt16 hk15 a (List.mem_of_mem_drop ha))
    rw [hl] at hlt
    have e : code v = code (v.take (k - d)) * 16 ^ d + code (v.drop (k - d)) := by
      conv_lhs => rw [← List.take_append_drop (k - d) v]
      rw [S.code_append, hl]
    rw [e]
    exact S.mul_add_div' hlt
  unfold WLink at h
  unfold ovlF
  rw [e1, e2, e3, h]
  exact beq_self_eq_true _

/-! ### Set A -/

theorem permW_range' (k : ℕ) : PermW k (List.range' 1 k) := by
  refine ⟨List.nodup_range', List.length_range', fun a => ?_⟩
  rw [List.mem_range'_1]
  omega

/-- The arithmetic tables. -/
theorem encA (k : ℕ) (hk : 4 ≤ k) (hk15 : k ≤ 15) :
    Enc k code (cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
      (sdA k 3 (permCodes k k)) (sdA k 4 (permCodes k k)) (permCodes k k) (idcF k) where
  ci_inj := fun u v hu hv h => by
    rw [cidxF_eq, cidxF_eq] at h
    exact S.isRotated_of_ci_eq (by omega) hk15 hu hv h
  nxt_eq := fun a b ha h => nxtF_code (by omega) hk15 ha h
  s3_mem := fun u v hu hv h =>
    List.mem_filter.mpr ⟨mem_perm hk15 hv, ovlF_of_wlink (by omega) hk15 (by omega) hu hv h⟩
  s4_mem := fun u v hu hv h =>
    List.mem_filter.mpr ⟨mem_perm hk15 hv, ovlF_of_wlink (by omega) hk15 hk hu hv h⟩
  jl_mem := fun v hv => mem_perm hk15 hv
  st_eq := by rw [idcF_eq, S.idcF_eq, S.idc_code]

/-! ### Set B -/

theorem tab_get {α : Type} [Inhabited α] (jl : List ℕ) (f : ℕ → α) {c : ℕ} (hc : c ∈ jl) :
    ((jl.map f).toArray)[jl.idxOf c]! = f c := by
  have hi : jl.idxOf c < jl.length := List.idxOf_lt_length_of_mem hc
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  rfl

theorem arr_get (jl : List ℕ) {c : ℕ} (hc : c ∈ jl) : (jl.toArray)[jl.idxOf c]! = c := by
  have hi : jl.idxOf c < jl.length := List.idxOf_lt_length_of_mem hc
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem_idxOf hi]
  rfl

theorem sdTab_eq (k d : ℕ) (jl : List ℕ) : sdTab k d jl =
    (jl.map fun a => (List.range jl.length).filter fun j =>
      ovlF (16 ^ (k - 1) - 1) (16 ^ (k - d)) (16 ^ d) a (jl.toArray)[j]!).toArray := rfl

/-- The index of a word in the list of permutation codes. -/
def encB (k : ℕ) (u : List ℕ) : ℕ := (permCodes k k).idxOf (code u)

theorem sdTab_mem {k d : ℕ} (hk : 1 ≤ k) (hk15 : k ≤ 15) (hd : d ≤ k) {u v : List ℕ}
    (hu : PermW k u) (hv : PermW k v) (h : WLink k d u v) :
    encB k v ∈ (sdTab k d (permCodes k k))[encB k u]! := by
  unfold encB
  rw [sdTab_eq, tab_get _ _ (mem_perm hk15 hu)]
  refine List.mem_filter.mpr ⟨List.mem_range.mpr
    (List.idxOf_lt_length_of_mem (mem_perm hk15 hv)), ?_⟩
  rw [arr_get _ (mem_perm hk15 hv)]
  exact ovlF_of_wlink hk hk15 hd hu hv h

/-- The tables. -/
theorem encB_enc (k : ℕ) (hk : 4 ≤ k) (hk15 : k ≤ 15) :
    Enc k (encB k) (fun i => (ciTab k (permCodes k k))[i]!)
      (fun i => (nxtTab k (permCodes k k))[i]!) (fun i => (sdTab k 3 (permCodes k k))[i]!)
      (fun i => (sdTab k 4 (permCodes k k))[i]!) (List.range (permCodes k k).length)
      ((permCodes k k).idxOf (idcF k)) where
  ci_inj := fun u v hu hv h => by
    have h' : (ciTab k (permCodes k k))[(permCodes k k).idxOf (code u)]! =
        (ciTab k (permCodes k k))[(permCodes k k).idxOf (code v)]! := h
    unfold ciTab at h'
    rw [tab_get _ _ (mem_perm hk15 hu), tab_get _ _ (mem_perm hk15 hv)] at h'
    obtain ⟨i, hi⟩ := S.canonF_rot k (by omega) k u hu.2.1 (hu.lt16 hk15)
    obtain ⟨j, hj⟩ := S.canonF_rot k (by omega) k v hv.2.1 (hv.lt16 hk15)
    rw [canonF_eq, canonF_eq, hi, hj] at h'
    have h2 : code (u.rotate i) = code (v.rotate j) :=
      (List.idxOf_inj (mem_perm hk15 (hu.rotate i))).mp h'
    have h3 := S.code_inj _ _ (by rw [List.length_rotate, List.length_rotate, hu.2.1, hv.2.1])
      ((hu.rotate i).lt16 hk15) ((hv.rotate j).lt16 hk15) h2
    have r1 : u ~r u.rotate i := ⟨i, rfl⟩
    have r2 : v ~r v.rotate j := ⟨j, rfl⟩
    rw [h3] at r1
    exact r1.trans r2.symm
  nxt_eq := fun a b ha h => by
    show (nxtTab k (permCodes k k))[(permCodes k k).idxOf (code a)]! =
      (permCodes k k).idxOf (code b)
    unfold nxtTab
    rw [tab_get _ _ (mem_perm hk15 ha), nxtF_code (by omega) hk15 ha h]
  s3_mem := fun u v hu hv h => sdTab_mem (by omega) hk15 (by omega) hu hv h
  s4_mem := fun u v hu hv h => sdTab_mem (by omega) hk15 hk hu hv h
  jl_mem := fun v hv => List.mem_range.mpr (List.idxOf_lt_length_of_mem (mem_perm hk15 hv))
  st_eq := by
    show (permCodes k k).idxOf (idcF k) = (permCodes k k).idxOf (code (List.range' 1 k))
    rw [idcF_eq, S.idcF_eq, S.idc_code]

/-! ### Tabulated rules -/

/-- A tabulated rule is the rule. -/
theorem look3_tab3 (A B C : ℕ) (f : ℕ → ℕ → ℕ → Bool) : look3 A B C (tab3 A B C f) f = f := by
  funext t r d
  unfold look3
  by_cases h : (decide (t < A) && decide (r < B) && decide (d < C)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ht, hr⟩, hd⟩ := h
    have hi : (t * B + r) * C + d < A * B * C := by
      have h1 : t * B + r + 1 ≤ A * B := by nlinarith
      have h2 : (t * B + r + 1) * C ≤ A * B * C := Nat.mul_le_mul_right _ h1
      nlinarith
    have hsz : (t * B + r) * C + d < (tab3 A B C f).size := by
      unfold tab3
      rw [Array.size_ofFn]
      exact hi
    have e0 : (tab3 A B C f)[(t * B + r) * C + d]! = (tab3 A B C f)[(t * B + r) * C + d]'hsz :=
      getElem!_pos (tab3 A B C f) ((t * B + r) * C + d) hsz
    rw [e0]
    simp only [tab3, Array.getElem_ofFn, S.mul_add_div' hd, S.mul_add_mod' hd,
      S.mul_add_div' hr, S.mul_add_mod' hr]
  · rw [if_neg h]

/-! ### From a search to the statement -/

variable {k : ℕ} {rs : Bool} {bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool} {fuel ds nt : ℕ}

/-- The search with arithmetic tables proves the statement (`4 ≤ k ≤ 15`).  The parts may be
evaluated in several ranges. -/
theorem stmt_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      searchA k rs bad badR keepN keepS keepJ fuel ds nt pa pb = false) :
    PStmt k rs bad badR keepN keepS keepJ :=
  stmt_of_parts (encA k hk hk15) (by omega) hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    unfold searchA at h
    exact searchPar_false h tp h1 h2)

/-- The search with tables proves the statement (`4 ≤ k ≤ 15`). -/
theorem stmt_of_searchB (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      searchB k rs bad badR keepN keepS keepJ fuel ds nt pa pb = false) :
    PStmt k rs bad badR keepN keepS keepJ :=
  stmt_of_parts (encB_enc k hk hk15) (by omega) hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    have h' : searchPar (fun i => (ciTab k (permCodes k k))[i]!)
        (fun i => (nxtTab k (permCodes k k))[i]!) (fun i => (sdTab k 3 (permCodes k k))[i]!)
        (fun i => (sdTab k 4 (permCodes k k))[i]!) (List.range (permCodes k k).length)
        ((permCodes k k).idxOf (idcF k)) (k - 1) rs bad badR keepN keepS keepJ
        (permCodes k k).length fuel (fuel - ds) nt pa pb = false := h
    exact searchPar_false h' tp h1 h2)

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.stmt_of_searchA
#print axioms SuperpermLowerBounds.PS.stmt_of_searchB
#print axioms SuperpermLowerBounds.PS.look3_tab3

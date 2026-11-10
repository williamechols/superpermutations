/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Bounds
import Hunter.Paths

/-!
# The superpermutation ↔ graph bridge: `L*(k) = Ssuper(k)`  (`bridge_Lstar_eq_Ssuper`)

`Lstar k = L k + k` equals the direct superpermutation minimum `Ssuper k`.

Two directions, both self-contained (no Coeff2 `Walk`/`glue`/`ProperStep` machinery):

* **Path → word** (`Ssuper ≤ Lstar`): the overlap-word `wordOf` of a Hamiltonian path's
  vertex list is a superpermutation of length `k + w(P)`.  The `wordOf` machinery is ported
  from `Coeff2/Auxiliary.lean`; it operates on a raw `List (List ℕ)` and needs only
  `IsPermWord` + `wt_spec`, never `ProperStep`.
* **Word → path** (`Lstar ≤ Ssuper`): a superpermutation `w` gives a Hamiltonian *simple*
  path by sorting all vertices by their first-occurrence position `fpos`.  Telescoping the
  overlap-position bound (`wt_le_pos_gap`, ported) shows this path's weight is `≤ |w| − k`.
  This is exactly the "optimum attained by a simple path" argument the spine flagged — it is
  clean here because Hunter's `HPath` has no per-edge constraint.
-/

namespace Hunter

namespace ProofsLstar

open List
open scoped Classical

variable {k : ℕ}

instance instNonemptyVtx : Nonempty (Vtx k) :=
  ⟨⟨(Finset.Icc 1 k).sort (· ≤ ·),
    Finset.sort_nodup _ _, Finset.sort_toFinset _ _⟩⟩

/-! ## Ported overlap machinery (from `Coeff2/Auxiliary.lean`, `wt`/`wt_spec` are Hunter's) -/

/-- The overlap-position bound (Coeff2 `wt_le_pos_gap`): consecutive permutation windows of a
word at positions `p < q` overlap in all but `q − p` symbols. -/
theorem wt_le_pos_gap {w : List ℕ} {p q : ℕ} (hk : 1 ≤ k) (hpq : p < q)
    (_hq : q + k ≤ w.length) (hup : IsPermWord k ((w.drop p).take k)) :
    wt k ((w.drop p).take k) ((w.drop q).take k) ≤ q - p := by
  rcases Nat.lt_or_ge (q - p) k with hlt | hge
  · refine wt_le (by omega) (by omega) ?_
    rw [List.drop_take, List.drop_drop]
    have h1 : p + (q - p) = q := by omega
    rw [h1, List.take_take]
    congr 1
    omega
  · have := (wt_spec (u := (w.drop p).take k) (v := (w.drop q).take k) hk
      (le_of_eq hup.length)).2.1
    omega

/-- The word of a walk (Coeff2 `wordOf`): each vertex contributes the first `wt` symbols of
its word, the final vertex its whole word. -/
noncomputable def wordOf (k : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | [σ] => σ
  | σ :: τ :: rest => σ.take (wt k σ τ) ++ wordOf k (τ :: rest)

/-- Coeff2 `wordOf_length`: `|wordOf l| = k + Σ wt`. -/
theorem wordOf_length (hk : 1 ≤ k) :
    ∀ (l : List (List ℕ)), l ≠ [] → (∀ x ∈ l, IsPermWord k x) →
      (wordOf k l).length = k + (List.zipWith (wt k) l l.tail).sum
  | [], h, _ => absurd rfl h
  | [σ], _, hp => by
    show σ.length = k + (List.zipWith (wt k) [σ] []).sum
    rw [(hp σ (List.mem_singleton_self σ)).length]
    simp
  | σ :: τ :: rest, _, hp => by
    have ih := wordOf_length hk (τ :: rest) (by simp)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hσ := hp σ List.mem_cons_self
    have hwt : wt k σ τ ≤ k :=
      (wt_spec (u := σ) (v := τ) hk (le_of_eq hσ.length)).2.1
    show (σ.take (wt k σ τ) ++ wordOf k (τ :: rest)).length = _
    rw [List.length_append, List.length_take, hσ.length, Nat.min_eq_left hwt, ih]
    show wt k σ τ + (k + (List.zipWith (wt k) (τ :: rest) rest).sum)
      = k + (wt k σ τ + (List.zipWith (wt k) (τ :: rest) rest).sum)
    omega

/-- Coeff2 `word_prefix_wordOf`: the head vertex's word is a prefix of the walk word. -/
theorem word_prefix_wordOf (hk : 1 ≤ k) :
    ∀ (l : List (List ℕ)) (σ : List ℕ), IsPermWord k σ → (∀ x ∈ l, IsPermWord k x) →
      σ <+: wordOf k (σ :: l)
  | [], σ, _, _ => ⟨[], by simp [wordOf]⟩
  | τ :: rest, σ, hσ, hl => by
    obtain ⟨t, ht⟩ := word_prefix_wordOf hk rest τ (hl τ List.mem_cons_self)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    refine ⟨τ.drop (k - wt k σ τ) ++ t, ?_⟩
    have hover : σ.drop (wt k σ τ) = τ.take (k - wt k σ τ) :=
      (wt_spec (u := σ) (v := τ) hk (le_of_eq hσ.length)).2.2
    show σ ++ (τ.drop (k - wt k σ τ) ++ t) = σ.take (wt k σ τ) ++ wordOf k (τ :: rest)
    calc σ ++ (τ.drop (k - wt k σ τ) ++ t)
        = (σ.take (wt k σ τ) ++ σ.drop (wt k σ τ)) ++ (τ.drop (k - wt k σ τ) ++ t) := by
          rw [List.take_append_drop]
      _ = σ.take (wt k σ τ) ++ (τ.take (k - wt k σ τ) ++ (τ.drop (k - wt k σ τ) ++ t)) := by
          rw [hover, List.append_assoc]
      _ = σ.take (wt k σ τ) ++ (τ ++ t) := by
          rw [← List.append_assoc (τ.take (k - wt k σ τ)), List.take_append_drop]
      _ = σ.take (wt k σ τ) ++ wordOf k (τ :: rest) := by rw [ht]

/-- Coeff2 `word_infix_wordOf`: every visited vertex's word is a factor of the walk word. -/
theorem word_infix_wordOf (hk : 1 ≤ k) :
    ∀ (l : List (List ℕ)) (v : List ℕ), v ∈ l → (∀ x ∈ l, IsPermWord k x) →
      v <:+: wordOf k l
  | [], v, hv, _ => absurd hv (List.not_mem_nil)
  | σ :: rest, v, hv, hl => by
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact (word_prefix_wordOf hk rest v (hl v List.mem_cons_self)
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))).isInfix
    · rcases rest with _ | ⟨τ, rest'⟩
      · exact absurd hv' (List.not_mem_nil)
      · have ih := word_infix_wordOf hk (τ :: rest') v hv'
          (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        show v <:+: σ.take (wt k σ τ) ++ wordOf k (τ :: rest')
        exact ih.trans (List.suffix_append _ _).isInfix

/-! ## `zipWith` over mapped vertex lists -/

/-- `zipWith wt` over the underlying words equals `zipWith ew` over the vertices. -/
theorem zipWith_wt_map_val : ∀ (A B : List (Vtx k)),
    List.zipWith (wt k) (A.map Subtype.val) (B.map Subtype.val) = List.zipWith (ew k) A B
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: A, b :: B => by
    simp only [List.map_cons, List.zipWith_cons_cons, ew]
    rw [zipWith_wt_map_val A B]

/-- The overlap-sum over a mapped vertex list is the path weight. -/
theorem zipWith_wt_tail_eq (l : List (Vtx k)) :
    (List.zipWith (wt k) (l.map Subtype.val) (l.map Subtype.val).tail).sum
      = (l.zipWith (ew k) l.tail).sum := by
  have htail : (l.map Subtype.val).tail = l.tail.map Subtype.val := by cases l <;> rfl
  rw [htail, zipWith_wt_map_val]

/-! ## First-occurrence positions -/

/-- `fpos w v` = the least position `p` in `w` at which the length-`k` window equals `v`. -/
noncomputable def fpos (w : List ℕ) (v : Vtx k) : ℕ :=
  sInf {p | (w.drop p).take k = v.1}

theorem fpos_mem_set {w : List ℕ} (hw : IsSuperperm k w) (v : Vtx k) :
    {p | (w.drop p).take k = v.1}.Nonempty := by
  obtain ⟨s, t, hst⟩ := hw v.1 v.2
  refine ⟨s.length, ?_⟩
  have hdrop : w.drop s.length = v.1 ++ t := by
    rw [← hst, List.append_assoc, List.drop_left]
  show (w.drop s.length).take k = v.1
  rw [hdrop, List.take_left' v.2.length]

theorem fpos_spec {w : List ℕ} (hw : IsSuperperm k w) (v : Vtx k) :
    (w.drop (fpos w v)).take k = v.1 :=
  Nat.sInf_mem (fpos_mem_set hw v)

theorem fpos_bound {w : List ℕ} (hk : 1 ≤ k) (hw : IsSuperperm k w) (v : Vtx k) :
    fpos w v + k ≤ w.length := by
  have h := fpos_spec hw v
  have hlen : ((w.drop (fpos w v)).take k).length = k := by rw [h]; exact v.2.length
  rw [List.length_take, List.length_drop] at hlen
  have h2 : k ≤ w.length - fpos w v := min_eq_left_iff.mp hlen
  omega

theorem fpos_injective {w : List ℕ} (hw : IsSuperperm k w) :
    Function.Injective (fpos (k := k) w) := by
  intro a b hab
  apply Subtype.ext
  have ha := fpos_spec hw a
  have hb := fpos_spec hw b
  rw [← ha, ← hb, hab]

/-! ## The telescoping bound -/

/-- Telescoping: along a list of vertices strictly increasing in `fpos`, the total overlap
weight plus the first `fpos` is bounded by the last `fpos`. -/
theorem tele (w : List ℕ) (hk : 1 ≤ k) :
    ∀ (a : Vtx k) (rest : List (Vtx k)),
      (a :: rest).Pairwise (fun x y => fpos w x < fpos w y) →
      (∀ v ∈ a :: rest, (w.drop (fpos w v)).take k = v.1) →
      (∀ v ∈ a :: rest, fpos w v + k ≤ w.length) →
      ((a :: rest).zipWith (ew k) rest).sum + fpos w a
        ≤ fpos w ((a :: rest).getLast (List.cons_ne_nil a rest)) := by
  intro a rest
  induction rest generalizing a with
  | nil =>
    intro _ _ _
    simp
  | cons y rest' ih =>
    intro hpw hwin hbd
    have hpc := List.pairwise_cons.mp hpw
    have hay : fpos w a < fpos w y := hpc.1 y List.mem_cons_self
    have IH := ih y hpc.2
      (fun v hv => hwin v (List.mem_cons_of_mem a hv))
      (fun v hv => hbd v (List.mem_cons_of_mem a hv))
    have hgap : ew k a y ≤ fpos w y - fpos w a := by
      have h1 := wt_le_pos_gap (w := w) hk hay (hbd y (List.mem_cons_of_mem a List.mem_cons_self))
        (by rw [hwin a List.mem_cons_self]; exact a.2)
      rwa [hwin a List.mem_cons_self, hwin y (List.mem_cons_of_mem a List.mem_cons_self)] at h1
    have hgl : (a :: y :: rest').getLast (List.cons_ne_nil _ _)
             = (y :: rest').getLast (List.cons_ne_nil _ _) := List.getLast_cons _
    rw [hgl]
    simp only [List.zipWith_cons_cons, List.sum_cons]
    omega

/-! ## Direction A: word → path, giving `Lstar ≤ Ssuper` -/

theorem dirA {w : List ℕ} (hk : 1 ≤ k) (hw : IsSuperperm k w) : L k + k ≤ w.length := by
  classical
  have hinj : Function.Injective (fpos w) := fpos_injective hw
  letI : DecidableRel (fun a b : Vtx k => fpos w a ≤ fpos w b) := fun a b => Nat.decLe _ _
  haveI : IsTrans (Vtx k) (fun a b : Vtx k => fpos w a ≤ fpos w b) :=
    ⟨fun a b c hab hbc => le_trans hab hbc⟩
  haveI : Std.Antisymm (fun a b : Vtx k => fpos w a ≤ fpos w b) :=
    ⟨fun a b h1 h2 => hinj (le_antisymm h1 h2)⟩
  haveI : Std.Total (fun a b : Vtx k => fpos w a ≤ fpos w b) := ⟨fun a b => le_total _ _⟩
  set xs := Finset.univ.sort (fun a b : Vtx k => fpos w a ≤ fpos w b) with hxs
  have hnd : xs.Nodup := Finset.sort_nodup _ _
  have hmem : ∀ v : Vtx k, v ∈ xs := fun v => (Finset.mem_sort _).mpr (Finset.mem_univ v)
  have hle : xs.Pairwise (fun a b : Vtx k => fpos w a ≤ fpos w b) := Finset.pairwise_sort _ _
  have hstrict : xs.Pairwise (fun a b : Vtx k => fpos w a < fpos w b) :=
    hle.imp₂ (fun a b h1 h2 => lt_of_le_of_ne h1 (fun he => h2 (hinj he))) hnd
  have hxne : xs ≠ [] := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (Vtx k))
    exact List.ne_nil_of_mem (hmem v)
  obtain ⟨a, rest, hcons⟩ := List.exists_cons_of_ne_nil hxne
  -- the Hamiltonian path
  set P : HPath k := ⟨xs, hxne, hnd⟩ with hP
  have hHam : P.IsHamiltonian := hmem
  -- weight bound via telescoping
  have hpw : (a :: rest).Pairwise (fun x y => fpos w x < fpos w y) := hcons ▸ hstrict
  have hwin : ∀ v ∈ a :: rest, (w.drop (fpos w v)).take k = v.1 :=
    fun v _ => fpos_spec hw v
  have hbd : ∀ v ∈ a :: rest, fpos w v + k ≤ w.length := fun v _ => fpos_bound hk hw v
  have htel := tele w hk a rest hpw hwin hbd
  have hgl_bd := fpos_bound hk hw ((a :: rest).getLast (List.cons_ne_nil a rest))
  -- P.wtP equals the telescoped sum
  have hwtP : P.wtP = ((a :: rest).zipWith (ew k) rest).sum := by
    show (xs.zipWith (ew k) xs.tail).sum = _
    rw [hcons]; rfl
  have hPle : P.wtP + k ≤ w.length := by
    rw [hwtP]; omega
  have hLle : L k ≤ P.wtP := Nat.sInf_le ⟨P, hHam, rfl⟩
  omega

/-! ## Direction B: path → word, giving `Ssuper ≤ Lstar` -/

/-- The overlap-word of a Hamiltonian path is a superpermutation of length `w(P) + k`. -/
theorem exists_superperm_of_ham (hk : 1 ≤ k) {P : HPath k} (hHam : P.IsHamiltonian) :
    IsSuperperm k (wordOf k (P.verts.map Subtype.val)) ∧
      (wordOf k (P.verts.map Subtype.val)).length = P.wtP + k := by
  set l := P.verts.map Subtype.val with hl
  have hlne : l ≠ [] := by rw [hl, Ne, List.map_eq_nil_iff]; exact P.ne
  have hlperm : ∀ x ∈ l, IsPermWord k x := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact v.2
  refine ⟨?_, ?_⟩
  · intro u hu
    have hmem : u ∈ l := by
      rw [hl, List.mem_map]
      exact ⟨⟨u, hu⟩, hHam ⟨u, hu⟩, rfl⟩
    exact word_infix_wordOf hk l u hmem hlperm
  · rw [wordOf_length hk l hlne hlperm, hl, zipWith_wt_tail_eq]
    show k + P.wtP = P.wtP + k
    omega

/-! ## Existence of a Hamiltonian path (seed for both `sInf`s being nonempty) -/

theorem exists_ham : ∃ P : HPath k, P.IsHamiltonian := by
  have hne : (Finset.univ : Finset (Vtx k)).toList ≠ [] := by
    have : 0 < (Finset.univ : Finset (Vtx k)).toList.length := by
      rw [Finset.length_toList]; exact Finset.univ_nonempty.card_pos
    exact List.ne_nil_of_length_pos this
  exact ⟨⟨Finset.univ.toList, hne, Finset.nodup_toList _⟩,
    fun v => Finset.mem_toList.mpr (Finset.mem_univ v)⟩

end ProofsLstar

/-! ## The bridge -/

namespace Proved

open ProofsLstar

/-- **bridge: L\*(k) = L(k) + k** — the library's `Lstar := L + k` equals the direct
superpermutation minimum `Ssuper` (Hunter's `L*(k) = k + L(k)`).  Proved outright. -/
theorem bridge_Lstar_eq_Ssuper {k : ℕ} (hk : 1 ≤ k) : Lstar k = Ssuper k := by
  classical
  obtain ⟨P₀, hP₀⟩ := (ProofsLstar.exists_ham : ∃ P : HPath k, P.IsHamiltonian)
  obtain ⟨hsuper₀, hlen₀⟩ := exists_superperm_of_ham hk hP₀
  -- both defining sets are nonempty
  have hLne : {m | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty :=
    ⟨P₀.wtP, P₀, hP₀, rfl⟩
  have hSne : {m | ∃ v : List ℕ, IsSuperperm k v ∧ v.length = m}.Nonempty :=
    ⟨_, _, hsuper₀, rfl⟩
  apply le_antisymm
  · -- Lstar ≤ Ssuper : direction A at the Ssuper-minimizer
    obtain ⟨v, hv, hvlen⟩ := Nat.sInf_mem hSne
    show L k + k ≤ Ssuper k
    calc L k + k ≤ v.length := dirA hk hv
      _ = Ssuper k := hvlen
  · -- Ssuper ≤ Lstar : direction B at the L-minimizer
    obtain ⟨P, hP, hPwt⟩ := Nat.sInf_mem hLne
    obtain ⟨hsuper, hlen⟩ := exists_superperm_of_ham hk hP
    show Ssuper k ≤ L k + k
    have hSle : Ssuper k ≤ (wordOf k (P.verts.map Subtype.val)).length :=
      Nat.sInf_le ⟨_, hsuper, rfl⟩
    rw [hlen] at hSle
    -- hPwt : P.wtP = L k
    have : P.wtP = L k := hPwt
    omega

end Proved

end Hunter

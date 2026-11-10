/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Defs
import Hunter.Appendix

/-!
# Proofs — spine track (bridges, §4 path transformation, §5 structure, Bound 1)

Proofs of the targets assigned to the spine track.  Helper lemmas live in namespace
`Hunter.ProofsSpine`; the targets are proved as `Hunter.Proved.<name>` with the statement
type copied verbatim from `Hunter/Statements.lean`.

See `PROGRESS-spine.md` for the per-target status log, hypotheses taken, and discrepancies.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsSpine

variable {k : ℕ}

/-! ## Helpers for `bridge_wEdges_edges_eq_wtP` -/

/-- `(l.zip l').map (fun e => f e.1 e.2) = l.zipWith f l'`. -/
theorem zip_map_eq_zipWith {α β γ : Type*} (f : α → β → γ) :
    ∀ (l : List α) (l' : List β), (l.zip l').map (fun e => f e.1 e.2) = l.zipWith f l'
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: l' => by
      rw [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, zip_map_eq_zipWith f l l']

/-- The pair-list `verts.zip verts.tail` is duplicate-free when `verts` is. -/
theorem zip_tail_nodup {p : HPath k} : (p.verts.zip p.verts.tail).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.map_snd_zip (by rw [List.length_tail]; omega)]
  exact (p.verts.tail_sublist).nodup p.nodup

/-! ## Helpers for `bridge_compMinto_eq_minto` -/

theorem mem_edges_iff {p : HPath k} {e : Vtx k × Vtx k} :
    e ∈ p.edges ↔ e ∈ p.verts.zip p.verts.tail := List.mem_toFinset

/-- `p.first` is the head of the underlying `verts` list. -/
theorem first_eq {p : HPath k} {a : Vtx k} {t : List (Vtx k)} (hvts : p.verts = a :: t) :
    p.first = a := by
  rw [← p.vert_zero, HPath.vert]
  simp only [hvts, List.getD_cons_zero]

/-- The start vertex of a path is never a tail-position vertex. -/
theorem first_not_mem_tail (p : HPath k) : p.first ∉ p.verts.tail := by
  obtain ⟨a, t, hv⟩ := List.exists_cons_of_ne_nil p.ne
  have hnd : (a :: t).Nodup := hv ▸ p.nodup
  rw [first_eq hv, hv, List.tail_cons]
  exact (List.nodup_cons.mp hnd).1

/-- The target of an edge of `p` lies in the tail vertex list. -/
theorem snd_mem_tail {p : HPath k} {e : Vtx k × Vtx k}
    (h : e ∈ p.verts.zip p.verts.tail) : e.2 ∈ p.verts.tail := by
  have hmem : e.2 ∈ (p.verts.zip p.verts.tail).map Prod.snd := List.mem_map.mpr ⟨e, h, rfl⟩
  rwa [List.map_snd_zip (by rw [List.length_tail]; omega)] at hmem

/-- Every non-start vertex of a path has an in-edge. -/
theorem exists_pred {p : HPath k} {v : Vtx k} (hv : v ∈ p.verts) (hne : v ≠ p.first) :
    ∃ u, (u, v) ∈ p.edges := by
  obtain ⟨a, t, hvts⟩ := List.exists_cons_of_ne_nil p.ne
  have hfirst : p.first = a := first_eq hvts
  have hvt : v ∈ t := by
    rw [hvts, List.mem_cons] at hv
    rcases hv with h | h
    · exact absurd (hfirst ▸ h) hne
    · exact h
  have htail : p.verts.tail = t := by rw [hvts]; rfl
  have hmem : v ∈ (p.verts.zip p.verts.tail).map Prod.snd := by
    rw [List.map_snd_zip (by rw [List.length_tail]; omega), htail]; exact hvt
  obtain ⟨e, he, hesnd⟩ := List.mem_map.mp hmem
  refine ⟨e.1, ?_⟩
  rw [mem_edges_iff]
  have : (e.1, v) = e := by rw [← hesnd]
  rw [this]; exact he

/-- On a path-component `p` of `X`, the (component-)tails are exactly `{p[1]}`. -/
theorem compTails_eq {p : HPath k} {X : Finset (Vtx k × Vtx k)}
    (hp : IsPathComponent p X) : compTails X p.vertsFinset = {p.first} := by
  ext v
  rw [compTails, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hvV, hinto⟩
    by_contra hne
    obtain ⟨u, hu⟩ := exists_pred (HPath.mem_vertsFinset.mp hvV) hne
    have huX : (u, v) ∈ X := hp.1 hu
    have hmem : (u, v) ∈ intoV X v := by
      rw [intoV, mem_into]; exact ⟨huX, Finset.mem_singleton_self v⟩
    rw [hinto] at hmem; exact absurd hmem (Finset.notMem_empty _)
  · rintro rfl
    refine ⟨HPath.mem_vertsFinset.mpr p.first_mem, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro e he
    rw [intoV, mem_into, Finset.mem_singleton] at he
    obtain ⟨heX, he2⟩ := he
    have h2V : e.2 ∈ p.vertsFinset := by rw [he2]; exact HPath.mem_vertsFinset.mpr p.first_mem
    have h1V : e.1 ∈ p.vertsFinset := (hp.2.1 e heX).mpr h2V
    have hee : e ∈ p.edges := hp.2.2 e heX h1V
    rw [mem_edges_iff] at hee
    have hsnd : e.2 ∈ p.verts.tail := snd_mem_tail hee
    rw [he2] at hsnd
    exact first_not_mem_tail p hsnd

/-! ## A simple path has out-degree ≤ 1 and in-degree ≤ 1 (for `clm_degree`) -/

theorem path_out_le_one (P : HPath k) (v : Vtx k) : (outV P.edges v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [outV, mem_out, Finset.mem_singleton, HPath.edges, List.mem_toFinset] at ha hb
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha.1
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb.1
  have hi' : i < P.verts.length := List.lt_length_left_of_zip hi
  have hj' : j < P.verts.length := List.lt_length_left_of_zip hj
  have hai : P.verts[i]'hi' = v := by
    have h := ha.2; rw [← hia] at h; simpa using h
  have hbj : P.verts[j]'hj' = v := by
    have h := hb.2; rw [← hjb] at h; simpa using h
  have hij : i = j := (P.nodup.getElem_inj_iff).mp (hai.trans hbj.symm)
  subst hij
  exact hia.symm.trans hjb

theorem path_into_le_one (P : HPath k) (v : Vtx k) : (intoV P.edges v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [intoV, mem_into, Finset.mem_singleton, HPath.edges, List.mem_toFinset] at ha hb
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha.1
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb.1
  have hi1 : i + 1 < P.verts.length := by
    have h := List.lt_length_right_of_zip hi; rw [List.length_tail] at h; omega
  have hj1 : j + 1 < P.verts.length := by
    have h := List.lt_length_right_of_zip hj; rw [List.length_tail] at h; omega
  have hai : P.verts[i + 1]'hi1 = v := by
    have h := ha.2; rw [← hia] at h; simpa using h
  have hbj : P.verts[j + 1]'hj1 = v := by
    have h := hb.2; rw [← hjb] at h; simpa using h
  have hij : i + 1 = j + 1 := (P.nodup.getElem_inj_iff).mp (hai.trans hbj.symm)
  have hij' : i = j := by omega
  subst hij'
  exact hia.symm.trans hjb

/-! ## Edge weights are `≥ 1` (for `lem_weightrule`) -/

/-- A duplicate-free list over a subsingleton type has length `≤ 1`. -/
theorem length_le_one_of_subsingleton {α : Type*} [Subsingleton α] {l : List α}
    (h : l.Nodup) : l.length ≤ 1 := by
  match l, h with
  | [], _ => simp
  | [_], _ => simp
  | a :: b :: t, h =>
      exact absurd (show b ∈ b :: t from List.mem_cons_self)
        (Subsingleton.elim a b ▸ (List.nodup_cons.mp h).1)

/-- Over the empty alphabet (`k = 0`) the vertex set is a singleton, so any `HPath` has no
edges. -/
theorem edges_eq_empty_zero (P : HPath 0) : P.edges = ∅ := by
  have hsub : Subsingleton (Vtx 0) := ⟨fun x y => Subtype.ext (by
    have hx : x.1 = [] := (List.toFinset_eq_empty_iff x.1).mp
      (x.2.2.trans (Finset.Icc_eq_empty (by omega)))
    have hy : y.1 = [] := (List.toFinset_eq_empty_iff y.1).mp
      (y.2.2.trans (Finset.Icc_eq_empty (by omega)))
    rw [hx, hy])⟩
  have hlen : P.verts.length ≤ 1 := length_le_one_of_subsingleton P.nodup
  rw [HPath.edges, Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [List.mem_toFinset] at he
  have h2 := snd_mem_tail he
  have hpos : 0 < P.verts.tail.length := List.length_pos_of_mem h2
  rw [List.length_tail] at hpos
  omega

/-- Every edge of a path has weight `≥ 1`. -/
theorem one_le_ew_of_mem_edges {P : HPath k} {e : Vtx k × Vtx k}
    (he : e ∈ P.edges) : 1 ≤ ew k e.1 e.2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [edges_eq_empty_zero P] at he; exact absurd he (Finset.notMem_empty _)
  · rw [ew]; exact (wt_spec hk (le_of_eq e.1.2.length)).1

/-! ## Degree bounds for the transformed graph `f(P,S)` (`clm_degree`) -/

theorem sigma_inj : Function.Injective (sigma : Vtx k → Vtx k) := by
  intro a b h
  apply Subtype.ext
  have hval : a.1.rotate 1 = b.1.rotate 1 := congrArg Subtype.val h
  exact List.rotate_injective 1 hval

theorem outV_mono {X Y : Finset (Vtx k × Vtx k)} (h : X ⊆ Y) (v : Vtx k) :
    outV X v ⊆ outV Y v := Finset.filter_subset_filter _ h

theorem intoV_mono {X Y : Finset (Vtx k × Vtx k)} (h : X ⊆ Y) (v : Vtx k) :
    intoV X v ⊆ intoV Y v := Finset.filter_subset_filter _ h

theorem intoV_union (X Y : Finset (Vtx k × Vtx k)) (v : Vtx k) :
    intoV (X ∪ Y) v = intoV X v ∪ intoV Y v := by
  simp only [intoV, into, Finset.filter_union]

/-- At most one added 1-edge points at any given vertex (`σ` is injective). -/
theorem intoV_addedEdges_le_one (S : Finset (Vtx k)) (v : Vtx k) :
    (intoV (addedEdges S) v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he e' he'
  simp only [intoV, mem_into, addedEdges, Finset.mem_image, Finset.mem_singleton] at he he'
  obtain ⟨⟨w, _, hwe⟩, he2⟩ := he
  obtain ⟨⟨w', _, hw'e⟩, he'2⟩ := he'
  rw [← hwe] at he2 ⊢
  rw [← hw'e] at he'2 ⊢
  have hs2 : sigma w = v := he2
  have hs'2 : sigma w' = v := he'2
  have hww : w = w' := sigma_inj (hs2.trans hs'2.symm)
  rw [hww]

/-- Out-degree of the Step-1 graph is `≤ 1`. -/
theorem outV_Xstep1_le_one (P : HPath k) (S : Finset (Vtx k)) (v : Vtx k) :
    (outV (Xstep1 P S) v).card ≤ 1 := by
  by_cases hvS : v ∈ S
  · refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_singleton (v, sigma v)))
    intro e he
    simp only [outV, mem_out, Finset.mem_singleton] at he ⊢
    obtain ⟨heX, he1⟩ := he
    rw [Xstep1, Finset.mem_union] at heX
    rcases heX with hP | hA
    · exfalso
      rw [Finset.mem_sdiff, E1removed, Finset.mem_filter] at hP
      exact hP.2 ⟨hP.1, by rw [he1]; exact hvS⟩
    · rw [addedEdges, Finset.mem_image] at hA
      obtain ⟨w, _, hwe⟩ := hA
      have hwv : w = v := by rw [← hwe] at he1; exact he1
      rw [← hwe, hwv]
  · refine le_trans (Finset.card_le_card ?_) (path_out_le_one P v)
    intro e he
    simp only [outV, mem_out, Finset.mem_singleton] at he ⊢
    obtain ⟨heX, he1⟩ := he
    rw [Xstep1, Finset.mem_union] at heX
    rcases heX with hP | hA
    · rw [Finset.mem_sdiff] at hP
      exact ⟨hP.1, he1⟩
    · exfalso
      rw [addedEdges, Finset.mem_image] at hA
      obtain ⟨w, hwS, hwe⟩ := hA
      have hwv : w = v := by rw [← hwe] at he1; exact he1
      exact hvS (hwv ▸ hwS)

/-- Out-degree of `f(P,S)` is `≤ 1` (Step 1 gives each vertex a unique out-edge). -/
theorem outV_fPS_le_one (P : HPath k) (S : Finset (Vtx k)) (v : Vtx k) :
    (outV (fPS P S) v).card ≤ 1 :=
  le_trans (Finset.card_le_card (outV_mono (fPS_subset_step1 P S) v)) (outV_Xstep1_le_one P S v)

/-- In-degree of `f(P,S)` is `≤ 1` (Step 2 deletes the doubled `P`-in-edge). -/
theorem intoV_fPS_le_one (P : HPath k) (S : Finset (Vtx k)) (_hS : SPrecond P S) (v : Vtx k) :
    (intoV (fPS P S) v).card ≤ 1 := by
  have hAle : (intoV (P.edges \ E1removed P S) v).card ≤ 1 :=
    le_trans (Finset.card_le_card (intoV_mono Finset.sdiff_subset v)) (path_into_le_one P v)
  have hBle : (intoV (addedEdges S) v).card ≤ 1 := intoV_addedEdges_le_one S v
  have hdecomp : intoV (Xstep1 P S) v =
      intoV (P.edges \ E1removed P S) v ∪ intoV (addedEdges S) v := by
    unfold Xstep1; exact intoV_union _ _ v
  have hstep1le2 : (intoV (Xstep1 P S) v).card ≤ 2 := by
    rw [hdecomp]; exact le_trans (Finset.card_union_le _ _) (by omega)
  by_cases hcard : (intoV (Xstep1 P S) v).card ≤ 1
  · exact le_trans (Finset.card_le_card (intoV_mono (fPS_subset_step1 P S) v)) hcard
  · rw [not_le] at hcard
    have hcard2 : (intoV (Xstep1 P S) v).card = 2 := le_antisymm hstep1le2 (by omega)
    have hvd : v ∈ doubles P S := by
      simp only [doubles, Finset.mem_filter]; exact ⟨Finset.mem_univ v, hcard2⟩
    refine le_trans (Finset.card_le_card ?_) hBle
    intro e he
    simp only [intoV, mem_into, Finset.mem_singleton] at he ⊢
    obtain ⟨heF, he2⟩ := he
    rw [fPS, Finset.mem_sdiff] at heF
    obtain ⟨heX1, heE2⟩ := heF
    rw [Xstep1, Finset.mem_union] at heX1
    rcases heX1 with hP | hA
    · exfalso
      apply heE2
      rw [Finset.mem_sdiff] at hP
      simp only [E2removed, Finset.mem_filter]
      exact ⟨hP.1, by rw [he2]; exact hvd⟩
    · exact ⟨hA, he2⟩

/-- If `b` is a Step-2 vertex (a `double`), then in `f(P,S)` it still has an in-edge — the
added 1-edge survives Step 2 (it is not a `P`-edge, by the S-precondition). -/
theorem double_has_surviving_inedge (P : HPath k) (S : Finset (Vtx k)) (hS : SPrecond P S)
    {b : Vtx k} (hb : b ∈ doubles P S) : (intoV (fPS P S) b).Nonempty := by
  simp only [doubles, Finset.mem_filter] at hb
  obtain ⟨-, hb2⟩ := hb
  have hdecomp : intoV (Xstep1 P S) b =
      intoV (P.edges \ E1removed P S) b ∪ intoV (addedEdges S) b := by
    unfold Xstep1; exact intoV_union _ _ b
  have hAle : (intoV (P.edges \ E1removed P S) b).card ≤ 1 :=
    le_trans (Finset.card_le_card (intoV_mono Finset.sdiff_subset b)) (path_into_le_one P b)
  have hBne : (intoV (addedEdges S) b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hB
    rw [hdecomp, hB, Finset.union_empty] at hb2
    omega
  obtain ⟨e, he⟩ := hBne
  simp only [intoV, mem_into, Finset.mem_singleton] at he
  obtain ⟨heA, he2⟩ := he
  refine ⟨e, ?_⟩
  simp only [intoV, mem_into, Finset.mem_singleton]
  refine ⟨?_, he2⟩
  rw [fPS, Finset.mem_sdiff]
  refine ⟨by rw [Xstep1, Finset.mem_union]; exact Or.inr heA, ?_⟩
  intro hcon
  have hmemP : e ∈ P.edges := E2removed_subset P S hcon
  rw [addedEdges, Finset.mem_image] at heA
  obtain ⟨w, hwS, hwe⟩ := heA
  rw [← hwe] at hmemP
  exact hS w hwS hmemP

/-- If `a ∈ S`, its added 1-edge `(a → σa)` survives into `f(P,S)` (S-precondition), so `a`
has an out-edge. -/
theorem outV_fPS_ne_empty_of_mem_S (P : HPath k) (S : Finset (Vtx k)) (hS : SPrecond P S)
    {a : Vtx k} (ha : a ∈ S) : (outV (fPS P S) a).Nonempty := by
  refine ⟨(a, sigma a), ?_⟩
  simp only [outV, mem_out, Finset.mem_singleton]
  refine ⟨?_, trivial⟩
  rw [fPS, Finset.mem_sdiff]
  constructor
  · rw [Xstep1, Finset.mem_union]; right
    rw [addedEdges, Finset.mem_image]; exact ⟨a, ha, rfl⟩
  · intro hcon
    exact hS a ha (E2removed_subset P S hcon)

/-- The bridge behind `clm-e2`: for a `P`-edge `e`, its target is a `double` iff its source
becomes a head (out-degree 0) of `f(P,S)`. -/
theorem key_doubles_iff (P : HPath k) (S : Finset (Vtx k)) (hS : SPrecond P S)
    {e : Vtx k × Vtx k} (heP : e ∈ P.edges) :
    e.2 ∈ doubles P S ↔ outV (fPS P S) e.1 = ∅ := by
  by_cases ha : e.1 ∈ S
  · have hRHS : outV (fPS P S) e.1 ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty]; exact outV_fPS_ne_empty_of_mem_S P S hS ha
    have hLHS : e.2 ∉ doubles P S := by
      intro hd
      simp only [doubles, Finset.mem_filter] at hd
      obtain ⟨-, hd2⟩ := hd
      have hAempty : intoV (P.edges \ E1removed P S) e.2 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [intoV, mem_into, Finset.mem_singleton] at hx
        obtain ⟨hxmem, hx2⟩ := hx
        rw [Finset.mem_sdiff] at hxmem
        have hxe : x = e :=
          Finset.card_le_one.mp (path_into_le_one P e.2) x
            (by simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨hxmem.1, hx2⟩) e
            (by simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨heP, trivial⟩)
        exact hxmem.2 (by rw [hxe, E1removed, Finset.mem_filter]; exact ⟨heP, ha⟩)
      have hdecomp : intoV (Xstep1 P S) e.2 =
          intoV (P.edges \ E1removed P S) e.2 ∪ intoV (addedEdges S) e.2 := by
        unfold Xstep1; exact intoV_union _ _ e.2
      rw [hdecomp, hAempty, Finset.empty_union] at hd2
      have := intoV_addedEdges_le_one S e.2
      omega
    exact ⟨fun h => absurd h hLHS, fun h => absurd h hRHS⟩
  · have heX1 : e ∈ Xstep1 P S := by
      rw [Xstep1, Finset.mem_union]; left; rw [Finset.mem_sdiff]
      exact ⟨heP, fun hc => ha (by rw [E1removed, Finset.mem_filter] at hc; exact hc.2)⟩
    have hStep1out : outV (Xstep1 P S) e.1 = {e} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨heX1, trivial⟩, ?_⟩
      intro x hx
      exact Finset.card_le_one.mp (outV_Xstep1_le_one P S e.1) x hx e
        (by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨heX1, trivial⟩)
    constructor
    · intro hd
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxs : x ∈ outV (Xstep1 P S) e.1 := outV_mono (fPS_subset_step1 P S) e.1 hx
      rw [hStep1out, Finset.mem_singleton] at hxs
      subst hxs
      simp only [outV, mem_out, Finset.mem_singleton] at hx
      obtain ⟨hefps, -⟩ := hx
      rw [fPS, Finset.mem_sdiff] at hefps
      exact hefps.2 (by rw [E2removed, Finset.mem_filter]; exact ⟨heP, hd⟩)
    · intro hne
      by_contra hd
      have hefps : e ∈ fPS P S := by
        rw [fPS, Finset.mem_sdiff]
        exact ⟨heX1, fun hc => hd (by rw [E2removed, Finset.mem_filter] at hc; exact hc.2)⟩
      have hmem : e ∈ outV (fPS P S) e.1 := by
        simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hefps, trivial⟩
      rw [hne] at hmem; exact absurd hmem (Finset.notMem_empty _)

/-! ## Existence of a Hamiltonian path (for `b1`) -/

/-- `Vtx k` is always inhabited: `[1,…,k]` is a permutation word. -/
theorem vtx_nonempty (k : ℕ) : Nonempty (Vtx k) := by
  refine ⟨⟨(List.range k).map (· + 1), ?_, ?_⟩⟩
  · exact (List.nodup_range).map (fun a b h => by omega)
  · ext x
    simp only [List.mem_toFinset, List.mem_map, List.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩

/-- The complete digraph `𝒮_k` has a Hamiltonian path (any ordering of all vertices, since
`HPath` imposes no per-edge constraint). -/
theorem exists_ham (k : ℕ) : ∃ P : HPath k, P.IsHamiltonian := by
  haveI := vtx_nonempty k
  refine ⟨⟨Finset.univ.toList, ?_, Finset.nodup_toList _⟩, ?_⟩
  · rw [Ne, Finset.toList_eq_nil]; exact Finset.univ_nonempty.ne_empty
  · intro v; exact Finset.mem_toList.mpr (Finset.mem_univ v)

end ProofsSpine

namespace Proved

/-- **bridge: w(E(p)) = w(p)**. -/
theorem bridge_wEdges_edges_eq_wtP {k : ℕ} (p : HPath k) : wEdges p.edges = p.wtP := by
  rw [wEdges, HPath.edges, HPath.wtP,
    List.sum_toFinset _ ProofsSpine.zip_tail_nodup,
    ProofsSpine.zip_map_eq_zipWith (ew k)]

/-- **bridge: compMinto agrees with minto** on a path-component. -/
theorem bridge_compMinto_eq_minto {k : ℕ} {p : HPath k} {X : Finset (Vtx k × Vtx k)}
    (hp : IsPathComponent p X) : compMinto X p.vertsFinset = p.minto := by
  rw [compMinto, ProofsSpine.compTails_eq hp, HPath.minto]
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hvC, s, hs, hew⟩
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ⟨v, fun h => hvC (HPath.mem_vertsFinset.mpr h), hew⟩
  · rintro ⟨v, hv, hew⟩
    exact ⟨v, fun h => hv (HPath.mem_vertsFinset.mp h), p.first, Finset.mem_singleton_self _, hew⟩

/-- **clm-degree** — `Comps(f(P,S))` is a set of directed paths and cycles: every vertex has
out-degree `≤ 1` and in-degree `≤ 1` in `X = f(P,S)`.  [PROVED outright]. -/
theorem clm_degree {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    ∀ v : Vtx k, (outV (fPS P S) v).card ≤ 1 ∧ (intoV (fPS P S) v).card ≤ 1 :=
  fun v => ⟨ProofsSpine.outV_fPS_le_one P S v, ProofsSpine.intoV_fPS_le_one P S hS v⟩

/-- **clm-e1** — `into(P, T(X) ∖ T(P)) ⊆ E₁`.  [PROVED outright] — from `clm_degree`'s
Step-2 analysis (a doubled target keeps its added in-edge) and the S-precondition. -/
theorem clm_e1 {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    into P.edges (tails (fPS P S) \ tails P.edges) ⊆ E1removed P S := by
  intro e he
  rw [into, Finset.mem_filter] at he
  obtain ⟨heP, he2⟩ := he
  rw [Finset.mem_sdiff] at he2
  obtain ⟨he2t, -⟩ := he2
  rw [tails, Finset.mem_filter] at he2t
  have hempty : intoV (fPS P S) e.2 = ∅ := he2t.2
  by_contra hcon
  have he1S : e.1 ∉ S := fun hS' => hcon (by rw [E1removed, Finset.mem_filter]; exact ⟨heP, hS'⟩)
  by_cases hd : e.2 ∈ doubles P S
  · obtain ⟨x, hx⟩ := ProofsSpine.double_has_surviving_inedge P S hS hd
    rw [hempty] at hx; exact absurd hx (Finset.notMem_empty _)
  · have hefps : e ∈ fPS P S := by
      rw [fPS, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [Xstep1, Finset.mem_union]; left
        rw [Finset.mem_sdiff]
        exact ⟨heP, fun hc => he1S (by rw [E1removed, Finset.mem_filter] at hc; exact hc.2)⟩
      · exact fun hc => hd (by rw [E2removed, Finset.mem_filter] at hc; exact hc.2)
    have hmem : e ∈ intoV (fPS P S) e.2 := by
      rw [intoV, mem_into]; exact ⟨hefps, Finset.mem_singleton_self _⟩
    rw [hempty] at hmem; exact absurd hmem (Finset.notMem_empty _)

/-- **clm-e2** — `E₂ = out(P, H(X) ∖ H(P))`.  [PROVED outright] — from `clm_degree`
(via `key_doubles_iff`: a `P`-edge's target doubles iff its source becomes a head). -/
theorem clm_e2 {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    E2removed P S = out P.edges (heads (fPS P S) \ heads P.edges) := by
  ext e
  simp only [E2removed, out, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨heP, hd⟩
    refine ⟨heP, ?_, ?_⟩
    · rw [heads, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (ProofsSpine.key_doubles_iff P S hS heP).mp hd⟩
    · rw [heads, Finset.mem_filter, not_and]
      intro _
      exact Finset.nonempty_iff_ne_empty.mp
        ⟨e, by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨heP, trivial⟩⟩
  · rintro ⟨heP, hhead, -⟩
    rw [heads, Finset.mem_filter] at hhead
    exact ⟨heP, (ProofsSpine.key_doubles_iff P S hS heP).mpr hhead.2⟩

/-- **b1** — Bound 1.  Proved taking `prp_wPgivenX` (a §5 target owned by this track but not
yet discharged outright) as an explicit hypothesis `h_wP`. -/
theorem b1 {k : ℕ}
    (h_wP : ∀ (P : HPath k), P.IsHamiltonian →
      P.wtP ≥ (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P)) :
    L k ≥ sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} := by
  obtain ⟨P₁, hHam₁⟩ := ProofsSpine.exists_ham k
  have hne : {m | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty :=
    ⟨P₁.wtP, P₁, hHam₁, rfl⟩
  obtain ⟨P₀, hHam₀, hP₀⟩ := Nat.sInf_mem hne
  rw [ge_iff_le]
  calc sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X}
      ≤ (numComps (F P₀) - 1) + MinThrough (F P₀) + wEdges (F P₀) :=
        Nat.sInf_le ⟨F P₀, ⟨P₀, hHam₀, rfl⟩, rfl⟩
    _ ≤ P₀.wtP := h_wP P₀ hHam₀
    _ = L k := hP₀

/-- **lem-weightrule** — proved from `clm_eqq` (taken as the explicit hypothesis `h_eqq`,
the one §4 weight-bookkeeping target it builds on) plus the proved `clm_e1`, `clm_e2` and
`ew ≥ 1`. -/
theorem lem_weightrule {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S)
    (h_eqq : (P.wtP : ℤ) = (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ E2removed P S, (ew k e.1 e.2 : ℤ)) :
    (P.wtP : ℤ) ≥ (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ into P.edges (tails (fPS P S) \ tails P.edges), ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ out P.edges (heads (fPS P S) \ heads P.edges), (ew k e.1 e.2 : ℤ) := by
  have hmono : ∑ e ∈ into P.edges (tails (fPS P S) \ tails P.edges), ((ew k e.1 e.2 : ℤ) - 1)
      ≤ ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (clm_e1 hS)
    intro e he _
    have h1 : 1 ≤ ew k e.1 e.2 :=
      ProofsSpine.one_le_ew_of_mem_edges (E1removed_subset P S he)
    have : (1 : ℤ) ≤ (ew k e.1 e.2 : ℤ) := by exact_mod_cast h1
    linarith
  rw [h_eqq, ← clm_e2 hS, ge_iff_le]
  linarith [hmono]

end Proved

end Hunter

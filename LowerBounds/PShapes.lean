import LowerBounds.PGlue
import LowerBounds.PFamily

/-!
# The components of a valid configuration (the written proof, sections 4 and 6)

* `RowsOK`: what the rows of a component of a valid configuration satisfy; `seg_num`: value and
  weight of a list of rows against those of its trails.
* `free_geom`, `cost_one_geom`: the geometry of a free attachment and of an attachment of cost 1
  (from `Valid.free_attachment`, `Valid.attachment_cost_one`, `Valid.slot_not_own`), as
  junctions.
* `Caps`: the finite statements F0–F5 and FR; `glue_path_bound`, `glue_ring`,
  `glue_ring_bound`: the bounds of section 6 for rows glued through a junction.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain T5899

/-! ### Rows of a component -/

/-- What the rows of a component of a valid configuration satisfy. -/
structure RowsOK (R : List (NRow 7)) : Prop where
  ne : R ≠ []
  len : ∀ r ∈ R, 1 ≤ r.len
  seams : ∀ w ∈ seamWeights R, 3 ≤ w
  classes : (rowsEntries R).Pairwise (NotRot (k := 7))

/-- The excess of the seam costs over one per heavy seam. -/
noncomputable def epsR (R : List (NRow 7)) : ℕ := rX R + 1 - (cutRows R).length

namespace RowsOK

variable {R : List (NRow 7)}

theorem inv (h : RowsOK R) : CutInv R (cutRows R) := cutRows_spec R h.seams

theorem fam (h : RowsOK R) : TrailFam 7 (cutRows R) :=
  cutRows_trailFam h.seams h.len h.classes

theorem cnt (h : RowsOK R) : (cutRows R).length ≤ rX R + 1 := h.inv.cnt h.ne

theorem pos (h : RowsOK R) : 1 ≤ (cutRows R).length := by
  have hf := h.inv.flat
  cases hS : cutRows R with
  | nil =>
      rw [hS] at hf
      exact absurd hf.symm h.ne
  | cons A S => simp

theorem len_le (h : RowsOK R) : ∀ r ∈ R, r.len ≤ 6 :=
  fun _ hr => len_le_of_rowsEntries_pairwise (by norm_num) h.classes hr

theorem eps_add (h : RowsOK R) : epsR R + (cutRows R).length = rX R + 1 := by
  have := h.cnt
  unfold epsR
  omega

/-- Value and weight of a list of rows with `a` more units of link cost, against its trails. -/
theorem seg_num (h : RowsOK R) (a : ℕ) :
    valR R (rX R + a) + 5 * ((epsR R + a : ℕ) : ℤ) = lE (prs (cutRows R)) + 5 ∧
      lW (prs (cutRows R)) + 6 * (epsR R + a) = wtR R (rX R + a) + 6 := by
  have he := h.eps_add
  rw [lE_prs, lW_prs, h.inv.flat]
  unfold valR wtR
  constructor
  · push_cast
    have he' : (epsR R : ℤ) + ((cutRows R).length : ℤ) = (rX R : ℤ) + 1 := by exact_mod_cast he
    linarith
  · omega

/-- With at least two trails: the first and the last trail and their end rows. -/
theorem decomp2 (h : RowsOK R) (h2 : 2 ≤ (cutRows R).length) :
    ∃ (first last : List (NRow 7)) (mid : List (List (NRow 7))) (r₁ r : NRow 7)
      (A B : List (NRow 7)), cutRows R = first :: (mid ++ [last]) ∧ first = r₁ :: B ∧
        last = A ++ [r] ∧ R.head? = some r₁ ∧ R.getLast? = some r := by
  obtain ⟨first, mid, last, hS⟩ := exists_first_mid_last h2
  have inv := h.inv
  have hfne : first ≠ [] := inv.ne first (by rw [hS]; exact List.mem_cons_self)
  have hlne : last ≠ [] := inv.ne last (by rw [hS]; simp)
  obtain ⟨r₁, B, hf⟩ := List.exists_cons_of_ne_nil hfne
  have hl : last = last.dropLast ++ [last.getLast hlne] :=
    (List.dropLast_concat_getLast hlne).symm
  refine ⟨first, last, mid, r₁, last.getLast hlne, last.dropLast, B, hS, hf, hl, ?_, ?_⟩
  · rw [← inv.flat, hS, hf]
    rfl
  · rw [← inv.flat, hS]
    have e : (first :: (mid ++ [last])).flatten =
        (first ++ mid.flatten ++ last.dropLast) ++ [last.getLast hlne] := by
      rw [List.flatten_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc, List.append_assoc, ← hl]
    rw [e, List.getLast?_concat]

/-- With one trail: the rows are that trail and no seam is heavy. -/
theorem single (h : RowsOK R) (h1 : (cutRows R).length = 1) :
    cutRows R = [R] ∧ Trail 7 R ∧ rX R = 0 := by
  obtain ⟨X, hX⟩ := List.length_eq_one_iff.mp h1
  have hf := h.inv.flat
  rw [hX, List.flatten_cons, List.flatten_nil, List.append_nil] at hf
  subst hf
  exact ⟨hX, h.fam.trails X (by rw [hX]; exact List.mem_singleton_self _), h.inv.single h1⟩

end RowsOK

/-! ### The finite statements F0–F5, FR -/

/-- The chain caps, the caps for sequences with 1 to 5 links of weight 4, and the ring caps. -/
structure Caps : Prop where
  chain : ChainCap Mf 84
  path : ∀ s, 1 ≤ s → s ≤ 5 → PathCap s (Pf s) (84 - 6 * s)
  ring : RingCap PRf 77

/-- The caps for a list of trails joined by links of weight 4 (`s = 0`: one trail). -/
theorem Caps.rows_path (hC : Caps) {S : List (List (NRow 7))} (h : TrailFam 7 S)
    (hl : S.IsChain (RowLink 7 4)) {s : ℕ} (hn : S.length = s + 1) (hs : s ≤ 5)
    (hG : rowsHoles 7 S.flatten + 6 * s ≤ 84) :
    S.flatten.length ≤ Pf s (rowsHoles 7 S.flatten) := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · obtain ⟨A, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hG ⊢
    rw [Pf_zero]
    have hcl := h.classes
    rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hcl
    exact chain_cap_rows hC.chain (h.trails A (List.mem_singleton_self _)) hcl (by omega)
  · exact path_cap_rows (hC.path s hpos hs) h hl hn (by omega)

/-! ### Attachments as junctions -/

variable {c : NConfig 7} {H : NHanging 7}

theorem hanging_entries_sublist (hH : H ∈ c.hanging) :
    (rowsEntries H.rows).Sublist c.entries := by
  unfold NConfig.entries
  refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
  rw [List.flatMap_def]
  exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩)

theorem hanging_ok (hv : c.Valid) (hH : H ∈ c.hanging) : RowsOK H.rows :=
  ⟨hv.hanging_ne H hH, hv.hanging_len H hH, hv.hanging_seams H hH,
    hv.distinct.sublist (hanging_entries_sublist hH)⟩

theorem kernel_ok (hv : c.Valid) : RowsOK c.kernel :=
  ⟨hv.kernel_ne, hv.kernel_len, hv.kernel_seams,
    hv.distinct.sublist (List.sublist_append_left _ _)⟩

theorem mem_of_getLast?_eq {α : Type*} {l : List α} {a : α} (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_getLast? h

theorem mem_of_head?_eq {α : Type*} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l :=
  List.mem_of_head? h

/-- **A free attachment** as a junction (the two end rows and the class between them merge),
with the link of weight 3 from the last row to the first one. -/
theorem free_geom (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 0) {r r₁ : NRow 7}
    (hr : H.rows.getLast? = some r) (hr₁ : H.rows.head? = some r₁) :
    Junction 7 r r₁ (tau2V r.lastEntry) [mergeRow r r₁] ∧ SLink 7 3 r.lastEntry r₁.entry ∧
      ∀ e ∈ rowsEntries H.rows, NotRot (tau2V r.lastEntry) e := by
  have g0 := hv.w0_ge H hH
  have g1 := hv.w1_ge H hH
  have h0 : H.w0 = 2 := by unfold NHanging.att at ha; omega
  have h1 : H.w1 = 2 := by unfold NHanging.att at ha; omega
  obtain ⟨hs, he, _⟩ := hv.free_attachment (by norm_num) hH hr hr₁ h0 h1
  have hok := hanging_ok hv hH
  refine ⟨junction_merge (hok.len r (mem_of_getLast?_eq hr)) (hok.len r₁ (mem_of_head?_eq hr₁)) he,
    ?_, ?_⟩
  · rw [he]
    exact sLink_three_tau2V_tau2V (by norm_num) r.lastEntry
  · intro e hem hrot
    apply hv.slot_not_own hH e hem
    rw [hs]
    have h2 : ((tau2V r.lastEntry : Vtx 7) : List ℕ) ~r
        ((sigmaInv (tau2V r.lastEntry) : Vtx 7) : List ℕ) := ⟨7 - 1, rfl⟩
    exact h2.symm.trans hrot

/-- **An attachment of cost 1** as a junction: one block more at the end of the last row or in
front of the first row. -/
theorem cost_one_geom (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 1) {r r₁ : NRow 7}
    (hr : H.rows.getLast? = some r) (hr₁ : H.rows.head? = some r₁) :
    (Junction 7 r r₁ (tau2V r.lastEntry) [extLast r, r₁] ∧
        ∀ e ∈ rowsEntries H.rows, NotRot (tau2V r.lastEntry) e) ∨
      ∃ y, Junction 7 r r₁ y [r, extFirst y r₁] ∧ ∀ e ∈ rowsEntries H.rows, NotRot y e := by
  have hok := hanging_ok hv hH
  have hrl := hok.len r (mem_of_getLast?_eq hr)
  have hr₁l := hok.len r₁ (mem_of_head?_eq hr₁)
  have hslot : ((H.slot : Vtx 7) : List ℕ) ~r ((sigma H.slot : Vtx 7) : List ℕ) := ⟨1, rfl⟩
  rcases hv.attachment_cost_one (by norm_num) hH hr hr₁ ha with ⟨hs, _, hw⟩ | ⟨he, hw⟩
  · left
    constructor
    · refine junction_extLast hrl hr₁l ?_
      apply sLink_three_of_ew
      rw [← hs, sigmaInv_sigma (by norm_num)]
      exact hw
    · intro e hem hrot
      apply hv.slot_not_own hH e hem
      rw [← hs] at hrot
      exact hslot.trans hrot
  · right
    refine ⟨sigma H.slot, junction_extFirst hrl hr₁l ?_ (sLink_three_of_ew hw), ?_⟩
    · rw [he]
      unfold tau2V
      rw [sigmaInv_sigma (by norm_num)]
    · intro e hem hrot
      exact hv.slot_not_own hH e hem (hslot.trans hrot)

/-! ### The bounds of section 6 -/

/-- Rows whose last row is glued to the first one through a junction, with at least two trails:
the bound for sequences with links of weight 4. -/
theorem glue_path_bound (hC : Caps) {R : List (NRow 7)} (hok : RowsOK R)
    (hlinks : rX R + 1 = (cutRows R).length) (h2 : 2 ≤ (cutRows R).length)
    (h7 : (cutRows R).length ≤ 7) {r r₁ : NRow 7} (hr : R.getLast? = some r)
    (hr₁ : R.head? = some r₁) {x : Vtx 7} {J : List (NRow 7)} (hJ : Junction 7 r r₁ x J)
    (hx : ∀ e ∈ rowsEntries R, NotRot x e) {δ : ℕ}
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁])
    (hG : rowsHoles 7 R + 6 * ((cutRows R).length - 2) ≤ 84 + δ) :
    δ ≤ rowsHoles 7 R ∧
      R.length + J.length ≤ Pf ((cutRows R).length - 2) (rowsHoles 7 R - δ) + 2 := by
  obtain ⟨first, last, mid, r₁', r', A, B, hS, hf, hl, hh, hg⟩ := hok.decomp2 h2
  rw [hr₁] at hh
  rw [hr] at hg
  obtain rfl := Option.some.inj hh
  obtain rfl := Option.some.inj hg
  have inv := hok.inv
  have hflat : (first :: (mid ++ [last])).flatten = R := by rw [← hS]; exact inv.flat
  have hfam : TrailFam 7 (first :: (mid ++ [last])) := by rw [← hS]; exact hok.fam
  have hch : (first :: (mid ++ [last])).IsChain (RowLink 7 4) := by
    rw [← hS]
    exact inv.eq4 hlinks
  have G := path_glue hfam hf hl hJ (by rw [hflat]; exact hx)
  have Glinks := path_glue_links (B := B) hch hl hJ
  have hLen := path_glue_length (J := J) (mid := mid) hf hl
  have hHol := path_glue_holes (J := J) (mid := mid) hf hl
  rw [hflat] at hLen hHol
  have hJlen : ∀ j ∈ J, j.len ≤ 6 := by
    intro j hj
    refine len_le_of_rowsEntries_pairwise (by norm_num) G.classes ?_
    refine List.mem_flatten.mpr ⟨glue A J B, by simp, ?_⟩
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  have hh' := hholes hJlen
  have hSlen : (cutRows R).length = mid.length + 2 := by
    rw [hS]
    simp
  have hn : (mid ++ [glue A J B]).length = ((cutRows R).length - 2) + 1 := by
    rw [hSlen]
    simp
  have hcap := hC.rows_path G Glinks hn (by omega) (by omega)
  have e : rowsHoles 7 (mid ++ [glue A J B]).flatten = rowsHoles 7 R - δ := by omega
  rw [e] at hcap
  exact ⟨by omega, by omega⟩

/-- Rows that form one trail, glued through a junction: the last row to the first row.  The
glued list is a trail that closes at weight 3 with pairwise different classes. -/
theorem glue_ring {R : List (NRow 7)} (hok : RowsOK R) (h1 : (cutRows R).length = 1)
    (hm : 2 ≤ R.length)
    {r r₁ : NRow 7} (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) {x : Vtx 7}
    {J : List (NRow 7)} (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) :
    ∃ T : List (NRow 7), Trail 7 T ∧ (rowsEntries T).Pairwise (NotRot (k := 7)) ∧
      RowLink 7 3 T T ∧ T.length + 2 = R.length + J.length ∧ (∀ j ∈ J, j ∈ T) ∧
      rowsHoles 7 T + rowsHoles 7 [r, r₁] = rowsHoles 7 R + rowsHoles 7 J := by
  obtain ⟨_, hT, _⟩ := hok.single h1
  obtain ⟨r₁', A, r', hR⟩ := exists_first_mid_last hm
  have hh : R.head? = some r₁' := by rw [hR]; rfl
  have hg : R.getLast? = some r' := by
    rw [hR, ← List.cons_append, List.getLast?_concat]
  rw [hr₁] at hh
  rw [hr] at hg
  obtain rfl := Option.some.inj hh
  obtain rfl := Option.some.inj hg
  rw [hR] at hT hx
  have hcl := hok.classes
  rw [hR] at hcl
  obtain ⟨g1, g2, g3⟩ := ring_glue hT hcl hJ hx
  refine ⟨glue A J [], g1, g2, g3, ?_, ?_, ?_⟩
  · rw [ring_glue_length, hR]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  · intro j hj
    unfold glue
    exact List.mem_append_right _ (List.mem_append_left _ hj)
  · rw [hR]
    exact ring_glue_holes A J r r₁

/-- The bound for rings. -/
theorem glue_ring_bound (hC : Caps) {R : List (NRow 7)} (hok : RowsOK R)
    (h1 : (cutRows R).length = 1) (hm : 2 ≤ R.length) {r r₁ : NRow 7}
    (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) {x : Vtx 7} {J : List (NRow 7)}
    (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) {δ : ℕ}
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + δ = rowsHoles 7 [r, r₁])
    (hlen : 4 ≤ R.length + J.length) (hG : rowsHoles 7 R ≤ 77 + δ) :
    δ ≤ rowsHoles 7 R ∧ R.length + J.length ≤ PRf (rowsHoles 7 R - δ) + 2 := by
  obtain ⟨T, hT, hcl, hclose, hTl, hJT, hTh⟩ := glue_ring hok h1 hm hr hr₁ hJ hx
  have hh' := hholes
    (fun j hj => len_le_of_rowsEntries_pairwise (by norm_num) hcl (hJT j hj))
  have hcap := ring_cap_rows hC.ring hT hcl (by omega) hclose (by omega)
  have e : rowsHoles 7 T = rowsHoles 7 R - δ := by omega
  rw [e] at hcap
  exact ⟨by omega, by omega⟩

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.free_geom
#print axioms SuperpermLowerBounds.cost_one_geom
#print axioms SuperpermLowerBounds.glue_path_bound
#print axioms SuperpermLowerBounds.glue_ring_bound

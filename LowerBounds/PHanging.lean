import LowerBounds.PShapes

/-!
# Hanging components (the written proof, sections 4, 6 and 7)

* `famH H`: the trails that a hanging component contributes to the family of the configuration:
  its trails (paid attachment); its trails with the last one glued to the first (free
  attachment, at least one heavy seam); its inner rows (closed chain of at least 3 rows);
  nothing otherwise.
* `epsH H`: the excess of its link costs over 1 per link.
* `famH_spec` (Lemma FAM): these are trails with blocks among those of `H`, and
  `vH H + 5 epsH H ≤ Σ (rows - holes - 5)`, `Σ (holes + 6) + 6 epsH H ≤ wH H`.
* `hanging_item`: if `epsH H = 0` and `H` contributes at most 5 trails, the value of `H` is at
  most the item table at its weight (given the caps).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain T5899

variable {c : NConfig 7} {H : NHanging 7}

/-- The trails of a hanging component in the family of the configuration. -/
noncomputable def famH (H : NHanging 7) : List (List (NRow 7)) :=
  if H.att = 0 then
    if 2 ≤ (cutRows H.rows).length then rotSegs (cutRows H.rows)
    else if 3 ≤ H.rows.length then [H.rows.tail.dropLast] else []
  else cutRows H.rows

/-- The excess of the link costs of a hanging component. -/
noncomputable def epsH (H : NHanging 7) : ℕ := epsR H.rows + (H.att - 1)

theorem rotSegs_length {S : List (List (NRow 7))} (h : 2 ≤ S.length) :
    (rotSegs S).length + 1 = S.length := by
  obtain ⟨first, mid, last, rfl⟩ := exists_first_mid_last h
  rw [rotSegs_eq]
  simp

theorem prs_rot (first last : List (NRow 7)) (mid : List (List (NRow 7))) :
    lE (prs (mid ++ [last ++ first])) = lE (prs (first :: (mid ++ [last]))) + 5 ∧
      lW (prs (mid ++ [last ++ first])) + 6 = lW (prs (first :: (mid ++ [last]))) := by
  rw [lE_prs, lE_prs, lW_prs, lW_prs, length_flatten_rot, rowsHoles_flatten_rot]
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · push_cast
    ring
  · omega

theorem head?_getLast?_of_eq {R A : List (NRow 7)} {r₁ r : NRow 7} (hR : R = r₁ :: (A ++ [r])) :
    R.head? = some r₁ ∧ R.getLast? = some r := by
  subst hR
  exact ⟨rfl, by rw [← List.cons_append, List.getLast?_concat]⟩

/-- A closed chain: its first and its last row have at most 5 blocks together. -/
theorem free_single_len (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 0)
    (h1 : (cutRows H.rows).length = 1) {r₁ r : NRow 7} {A : List (NRow 7)}
    (hR : H.rows = r₁ :: (A ++ [r])) : r.len + (r₁.len + 1) ≤ 6 := by
  have hok := hanging_ok hv hH
  obtain ⟨hr₁, hr⟩ := head?_getLast?_of_eq hR
  obtain ⟨hJ, _, hx⟩ := free_geom hv hH ha hr hr₁
  have hm : 2 ≤ H.rows.length := by
    rw [hR]
    simp
  obtain ⟨T, _, hcl, _, _, hJT, _⟩ := glue_ring hok h1 hm hr hr₁ hJ hx
  exact len_le_of_rowsEntries_pairwise (by norm_num) hcl (hJT _ (List.mem_singleton_self _))

/-- A loop has at most 5 blocks. -/
theorem free_one_len (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 0) {r : NRow 7}
    (hR : H.rows = [r]) : r.len ≤ 5 := by
  have hok := hanging_ok hv hH
  have hmem : r ∈ H.rows := by rw [hR]; exact List.mem_singleton_self _
  have h6 := hok.len_le r hmem
  have h1 := hok.len r hmem
  by_contra hcon
  have h66 : r.len = 6 := by omega
  have hr : H.rows.getLast? = some r := by rw [hR]; rfl
  have hr₁ : H.rows.head? = some r := by rw [hR]; rfl
  obtain ⟨_, _, hx⟩ := free_geom hv hH ha hr hr₁
  have hem : r.entry ∈ rowsEntries H.rows := by
    rw [hR, rowsEntries_cons]
    exact List.mem_append_left _ (NRow.entry_mem r h1)
  have ht : tau2V r.lastEntry = r.entry := by
    rw [NRow.tau2V_lastEntry h1, h66]
    exact tau2V_period (k := 7) (by norm_num) r.entry
  have := hx r.entry hem
  rw [ht] at this
  exact this (List.IsRotated.refl _)

/-- A free attachment with one or two rows and no heavy seam has value at most 0. -/
theorem free_small (hv : c.Valid) (hH : H ∈ c.hanging) (ha : H.att = 0)
    (h1 : (cutRows H.rows).length = 1) (hm : H.rows.length ≤ 2) : vH H ≤ 0 := by
  have hok := hanging_ok hv hH
  obtain ⟨_, _, hX⟩ := hok.single h1
  unfold vH valR
  rw [hX, ha]
  rcases hrows : H.rows with _ | ⟨r₁, _ | ⟨r, _ | ⟨r', rest⟩⟩⟩
  · exact absurd hrows hok.ne
  · have h5 := free_one_len hv hH ha hrows
    simp only [List.length_cons, List.length_nil, rowsHoles_cons, rowsHoles_nil]
    push_cast
    omega
  · have hR : H.rows = r₁ :: ([] ++ [r]) := hrows
    have h5 := free_single_len hv hH ha h1 hR
    simp only [List.length_cons, List.length_nil, rowsHoles_cons, rowsHoles_nil]
    push_cast
    omega
  · rw [hrows] at hm
    simp at hm

/-- **Lemma FAM for a hanging component.** -/
theorem famH_spec (hv : c.Valid) (hH : H ∈ c.hanging) :
    (∀ A ∈ famH H, Trail 7 A) ∧ (rowsEntries (famH H).flatten).Subperm (rowsEntries H.rows) ∧
      vH H + 5 * (epsH H : ℤ) ≤ lE (prs (famH H)) ∧ lW (prs (famH H)) + 6 * epsH H ≤ wH H := by
  have hok := hanging_ok hv hH
  have inv := hok.inv
  by_cases ha : H.att = 0
  · -- free attachment
    have heps : epsH H = epsR H.rows := by
      unfold epsH
      omega
    obtain ⟨n1, n2⟩ := hok.seg_num 0
    simp only [Nat.add_zero] at n1 n2
    have hv0 : vH H = valR H.rows (rX H.rows) := by
      unfold vH
      rw [ha, Nat.add_zero]
    have hw0 : wH H = wtR H.rows (rX H.rows) := by
      unfold wH
      rw [ha, Nat.add_zero]
    by_cases h2 : 2 ≤ (cutRows H.rows).length
    · obtain ⟨first, last, mid, r₁, r, A, B, hS, hf, hl, hh, hg⟩ := hok.decomp2 h2
      obtain ⟨_, hlink, _⟩ := free_geom hv hH ha hg hh
      have hfam : famH H = mid ++ [last ++ first] := by
        unfold famH
        rw [if_pos ha, if_pos h2, hS, rotSegs_eq]
      have hc : RowLink 7 3 last first := by
        rw [rowLink_iff]
        intro a ha' b hb
        rw [hl, List.getLast?_concat] at ha'
        rw [hf] at hb
        simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha' hb
        subst ha'
        subst hb
        exact hlink
      have hF : TrailFam 7 (first :: (mid ++ [last])) := by
        rw [← hS]
        exact hok.fam
      have hflat : (first :: (mid ++ [last])).flatten = H.rows := by
        rw [← hS]
        exact inv.flat
      obtain ⟨p1, p2⟩ := prs_rot first last mid
      rw [hS] at n1 n2
      rw [hfam, hv0, hw0, heps]
      refine ⟨(hF.rot hc).trails, ?_, ?_, ?_⟩
      · have := (rot_entries_perm first last mid).subperm
        rwa [hflat] at this
      · linarith
      · omega
    · have h1 : (cutRows H.rows).length = 1 := by
        have := hok.pos
        omega
      obtain ⟨hS, hT, hX⟩ := hok.single h1
      have he0 : epsR H.rows = 0 := by
        unfold epsR
        rw [hX, h1]
      by_cases h3 : 3 ≤ H.rows.length
      · obtain ⟨r₁, A, r, hR⟩ := exists_first_mid_last (by omega : 2 ≤ H.rows.length)
        have hfam : famH H = [A] := by
          unfold famH
          rw [if_pos ha, if_neg h2, if_pos h3, hR]
          simp
        have hlen := free_single_len hv hH ha h1 hR
        have hL : H.rows.length = A.length + 2 := by
          rw [hR]
          simp
        have hAne : A ≠ [] := by
          rintro rfl
          rw [hL] at h3
          simp at h3
        have hHo : rowsHoles 7 H.rows = (7 - 1 - r₁.len) + rowsHoles 7 A + (7 - 1 - r.len) := by
          rw [hR, rowsHoles_cons, rowsHoles_append, rowsHoles_singleton]
          omega
        have hT' := hT
        rw [hR] at hT'
        have hTA : Trail 7 A :=
          ⟨hAne, fun x hx => hT'.len x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)),
            (List.isChain_cons.mp hT'.seams).2.left_of_append⟩
        have hr₁l := hok.len r₁ (by rw [hR]; exact List.mem_cons_self)
        have hrl := hok.len r (by rw [hR]; simp)
        rw [hfam, hv0, hw0, heps, he0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro X hX'
          rw [List.mem_singleton.mp hX']
          exact hTA
        · rw [List.flatten_cons, List.flatten_nil, List.append_nil]
          refine (rowsEntries_sublist ?_).subperm
          rw [hR]
          exact (List.sublist_append_left A [r]).cons r₁
        · simp only [prs_cons, prs_nil, lE_cons, lE_nil]
          unfold valR
          rw [hX, hL, hHo]
          push_cast
          omega
        · simp only [prs_cons, prs_nil, lW_cons, lW_nil]
          unfold wtR
          rw [hX, hHo]
          omega
      · have hfam : famH H = [] := by
          unfold famH
          rw [if_pos ha, if_neg h2, if_neg h3]
        have hs := free_small hv hH ha h1 (by omega)
        rw [hfam, heps, he0]
        refine ⟨fun A hA => absurd hA (List.not_mem_nil), List.nil_subperm, ?_, ?_⟩
        · simp only [prs_nil, lE_nil]
          push_cast
          linarith
        · simp [prs_nil, lW_nil]
  · -- paid attachment
    have hfam : famH H = cutRows H.rows := by
      unfold famH
      rw [if_neg ha]
    obtain ⟨n1, n2⟩ := hok.seg_num H.att
    rw [hfam]
    refine ⟨hok.fam.trails, ?_, ?_, ?_⟩
    · rw [inv.flat]
    · unfold vH epsH
      omega
    · unfold wH epsH
      omega

/-- The bound for a component with an attachment of cost 1, from its junction. -/
theorem paid_bound (hC : Caps) {R : List (NRow 7)} (hok : RowsOK R)
    (hlinks : rX R + 1 = (cutRows R).length) (h5 : (cutRows R).length ≤ 5) {r r₁ : NRow 7}
    (hr : R.getLast? = some r) (hr₁ : R.head? = some r₁) {x : Vtx 7} {J : List (NRow 7)}
    (hJ : Junction 7 r r₁ x J) (hx : ∀ e ∈ rowsEntries R, NotRot x e) (hJ2 : J.length = 2)
    (hholes : (∀ j ∈ J, j.len ≤ 6) → rowsHoles 7 J + 1 = rowsHoles 7 [r, r₁])
    (hw : wtR R (rX R + 1) ≤ 84) : valR R (rX R + 1) ≤ (hvf (wtR R (rX R + 1)) : ℤ) := by
  have hnonneg : (0 : ℤ) ≤ (hvf (wtR R (rX R + 1)) : ℤ) := Int.natCast_nonneg _
  have hw' := hw
  unfold wtR at hw'
  by_cases h2 : 2 ≤ (cutRows R).length
  · obtain ⟨b1, b2⟩ := glue_path_bound hC hok hlinks h2 (by omega) hr hr₁ hJ hx hholes
      (by omega)
    have hit := item_A (cutRows R).length (by omega) h2 (rowsHoles 7 R) (by omega) b1 (by omega)
    have ew : wtR R (rX R + 1) = rowsHoles 7 R + 6 * (cutRows R).length := by
      unfold wtR
      omega
    rw [ew]
    unfold valR
    omega
  · have h1 : (cutRows R).length = 1 := by
      have := hok.pos
      omega
    have hX : rX R = 0 := by omega
    have ew : wtR R (rX R + 1) = rowsHoles 7 R + 6 := by
      unfold wtR
      omega
    by_cases hm : 2 ≤ R.length
    · obtain ⟨b1, b2⟩ := glue_ring_bound hC hok h1 hm hr hr₁ hJ hx hholes (by omega) (by omega)
      have hit := item_A1 (rowsHoles 7 R) (by omega) b1
      rw [ew]
      unfold valR
      omega
    · unfold valR
      omega

/-- **The value of a hanging component is at most the item table at its weight**, when its link
costs have no excess and it contributes at most 5 trails. -/
theorem hanging_item (hC : Caps) (hv : c.Valid) (hH : H ∈ c.hanging) (he : epsH H = 0)
    (hn : (famH H).length ≤ 5) (hw : wH H ≤ 84) : vH H ≤ (hvf (wH H) : ℤ) := by
  have hok := hanging_ok hv hH
  have heR : epsR H.rows = 0 := by
    unfold epsH at he
    omega
  have ha1 : H.att ≤ 1 := by
    unfold epsH at he
    omega
  have hlinks : rX H.rows + 1 = (cutRows H.rows).length := by
    have := hok.eps_add
    omega
  have hpos := hok.pos
  have hnonneg : (0 : ℤ) ≤ (hvf (wH H) : ℤ) := Int.natCast_nonneg _
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, H.rows.head? = some r₁ := by
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hok.ne
    exact ⟨a, by rw [hl]; rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, H.rows.getLast? = some r :=
    ⟨H.rows.getLast hok.ne, List.getLast?_eq_some_getLast hok.ne⟩
  by_cases ha : H.att = 0
  · obtain ⟨hJ, _, hx⟩ := free_geom hv hH ha hr hr₁
    have hholes : (∀ j ∈ [mergeRow r r₁], j.len ≤ 6) →
        rowsHoles 7 [mergeRow r r₁] + 7 = rowsHoles 7 [r, r₁] :=
      fun hj => holes_merge (hj _ (List.mem_singleton_self _))
    have hv0 : vH H = valR H.rows (rX H.rows) := by
      unfold vH
      rw [ha, Nat.add_zero]
    have hw0 : wH H = wtR H.rows (rX H.rows) := by
      unfold wH
      rw [ha, Nat.add_zero]
    have hw' := hw
    rw [hw0] at hw'
    unfold wtR at hw'
    by_cases h2 : 2 ≤ (cutRows H.rows).length
    · have hfl : (famH H).length + 1 = (cutRows H.rows).length := by
        unfold famH
        rw [if_pos ha, if_pos h2]
        exact rotSegs_length h2
      obtain ⟨b1, b2⟩ := glue_path_bound hC hok hlinks h2 (by omega) hr hr₁ hJ hx hholes
        (by omega)
      have hit := item_B ((cutRows H.rows).length - 1) (by omega) (by omega) (rowsHoles 7 H.rows)
        (by omega) b1 (by omega)
      have e : (cutRows H.rows).length - 1 - 1 = (cutRows H.rows).length - 2 := by omega
      rw [e] at hit
      have ew : wH H = rowsHoles 7 H.rows + 6 * ((cutRows H.rows).length - 1) := by
        rw [hw0]
        unfold wtR
        omega
      rw [ew, hv0]
      unfold valR
      simp only [List.length_singleton] at b2
      omega
    · have h1 : (cutRows H.rows).length = 1 := by omega
      have hX : rX H.rows = 0 := by omega
      by_cases h3 : 3 ≤ H.rows.length
      · obtain ⟨b1, b2⟩ := glue_ring_bound hC hok h1 (by omega) hr hr₁ hJ hx hholes
          (by simp only [List.length_singleton]; omega) (by omega)
        have hit := item_Z (rowsHoles 7 H.rows) (by omega) b1
        have ew : wH H = rowsHoles 7 H.rows := by
          rw [hw0]
          unfold wtR
          omega
        rw [ew, hv0]
        unfold valR
        simp only [List.length_singleton] at b2
        omega
      · have := free_small hv hH ha h1 (by omega)
        linarith
  · have ha' : H.att = 1 := by omega
    have hfam : famH H = cutRows H.rows := by
      unfold famH
      rw [if_neg ha]
    rw [hfam] at hn
    have hv1 : vH H = valR H.rows (rX H.rows + 1) := by
      unfold vH
      rw [ha']
    have hw1 : wH H = wtR H.rows (rX H.rows + 1) := by
      unfold wH
      rw [ha']
    rw [hv1, hw1]
    rw [hw1] at hw
    rcases cost_one_geom hv hH ha' hr hr₁ with ⟨hJ, hx⟩ | ⟨y, hJ, hx⟩
    · exact paid_bound hC hok hlinks hn hr hr₁ hJ hx rfl
        (fun hj => holes_extLast (hj (extLast r) (by simp))) hw
    · exact paid_bound hC hok hlinks hn hr hr₁ hJ hx rfl
        (fun hj => holes_extFirst (hj (extFirst y r₁) (by simp))) hw

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.famH_spec
#print axioms SuperpermLowerBounds.hanging_item

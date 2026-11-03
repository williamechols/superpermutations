import LowerBounds.PJunction

/-!
# Gluing through a junction (the written proof, section 6)

* `path_glue`, `path_glue_links`, `path_glue_length`, `path_glue_holes`: in a list of trails
  `first, mid…, last` the last trail is glued to the first one through a junction; the result
  `mid…, glue` is a list of trails with one trail less, the same links, and the rows and holes
  of the junction in place of the two rows it replaces.
* `ring_glue`: a trail `r₁, A…, r` whose last row is glued to its first row through a junction
  is a trail that closes at overlap weight 3.
* `rot_entries_perm`, `rot_length`, `rot_holes`: the same list of trails glued without a
  junction (`rotSegs`).
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

theorem rowsHoles_flatten_rot (first last : List (NRow k)) (mid : List (List (NRow k))) :
    rowsHoles k (mid ++ [last ++ first]).flatten =
      rowsHoles k (first :: (mid ++ [last])).flatten := by
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    rowsHoles_append]
  omega

theorem length_flatten_rot (first last : List (NRow k)) (mid : List (List (NRow k))) :
    (mid ++ [last ++ first]).flatten.length = (first :: (mid ++ [last])).flatten.length := by
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append]
  omega

theorem rot_entries_perm (first last : List (NRow k)) (mid : List (List (NRow k))) :
    (rowsEntries (mid ++ [last ++ first]).flatten).Perm
      (rowsEntries (first :: (mid ++ [last])).flatten) := by
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    rowsEntries_append]
  rw [← List.append_assoc]
  exact List.perm_append_comm

section path

variable {first last A B J : List (NRow k)} {mid : List (List (NRow k))} {r r₁ : NRow k}
  {x : Vtx k}

/-- The blocks after gluing: those before and `x`. -/
theorem path_glue_entries (hf : first = r₁ :: B) (hl : last = A ++ [r])
    (hJ : Junction k r r₁ x J) :
    (rowsEntries (mid ++ [glue A J B]).flatten).Perm
      (x :: rowsEntries (first :: (mid ++ [last])).flatten) := by
  subst hf
  subst hl
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [rowsEntries_append, rowsEntries_append (r₁ :: B), rowsEntries_append mid.flatten]
  have h1 : (rowsEntries mid.flatten ++ rowsEntries (glue A J B)).Perm
      (rowsEntries mid.flatten ++ (x :: (rowsEntries (A ++ [r]) ++ rowsEntries (r₁ :: B)))) :=
    List.Perm.append_left _ hJ.entries_glue
  refine h1.trans (List.perm_middle.trans (List.Perm.cons x ?_))
  rw [← List.append_assoc]
  exact List.perm_append_comm

/-- **Gluing the last trail to the first one.** -/
theorem path_glue (h : TrailFam k (first :: (mid ++ [last]))) (hf : first = r₁ :: B)
    (hl : last = A ++ [r]) (hJ : Junction k r r₁ x J)
    (hx : ∀ e ∈ rowsEntries (first :: (mid ++ [last])).flatten, NotRot x e) :
    TrailFam k (mid ++ [glue A J B]) where
  trails := by
    intro X hX
    rcases List.mem_append.mp hX with h1 | h1
    · exact h.trails X (List.mem_cons_of_mem _ (List.mem_append_left _ h1))
    · rw [List.mem_singleton.mp h1]
      refine hJ.trail_glue ?_ ?_
      · rw [← hl]
        exact h.trails last (by simp)
      · rw [← hf]
        exact h.trails first List.mem_cons_self
  classes := pairwise_of_perm_cons h.classes hx (path_glue_entries hf hl hJ)

theorem path_glue_links {d : ℕ} (hc : (first :: (mid ++ [last])).IsChain (RowLink k d))
    (hl : last = A ++ [r]) (hJ : Junction k r r₁ x J) :
    (mid ++ [glue A J B]).IsChain (RowLink k d) := by
  have h1 := hc.tail
  rw [List.tail_cons, List.isChain_append] at h1
  rw [List.isChain_append]
  refine ⟨h1.1, List.isChain_singleton _, ?_⟩
  intro X hX Y hY
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hY
  subst hY
  have h2 := h1.2.2 X hX last rfl
  unfold RowLink at h2 ⊢
  rw [hJ.rowsFirst_glue, ← hl]
  exact h2

theorem path_glue_length (hf : first = r₁ :: B) (hl : last = A ++ [r]) :
    (mid ++ [glue A J B]).flatten.length + 2 =
      (first :: (mid ++ [last])).flatten.length + J.length := by
  subst hf
  subst hl
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append, List.length_cons, List.length_nil, Junction.length_glue]
  omega

theorem path_glue_holes (hf : first = r₁ :: B) (hl : last = A ++ [r]) :
    rowsHoles k (mid ++ [glue A J B]).flatten + rowsHoles k [r, r₁] =
      rowsHoles k (first :: (mid ++ [last])).flatten + rowsHoles k J := by
  subst hf
  subst hl
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    rowsHoles_append, rowsHoles_cons, rowsHoles_nil, Junction.holes_glue]
  omega

end path

section ring

variable {A J : List (NRow k)} {r r₁ : NRow k} {x : Vtx k}

theorem ring_glue_entries (hJ : Junction k r r₁ x J) :
    (rowsEntries (glue A J [])).Perm (x :: rowsEntries (r₁ :: (A ++ [r]))) := by
  refine hJ.entries_glue.trans (List.Perm.cons x ?_)
  rw [rowsEntries_cons r₁ [], rowsEntries_nil, List.append_nil, rowsEntries_cons r₁ (A ++ [r])]
  exact List.perm_append_comm

/-- **Gluing the last row of a trail to its first row.** -/
theorem ring_glue (hT : Trail k (r₁ :: (A ++ [r])))
    (hcl : (rowsEntries (r₁ :: (A ++ [r]))).Pairwise (NotRot (k := k)))
    (hJ : Junction k r r₁ x J) (hx : ∀ e ∈ rowsEntries (r₁ :: (A ++ [r])), NotRot x e) :
    Trail k (glue A J []) ∧ (rowsEntries (glue A J [])).Pairwise (NotRot (k := k)) ∧
      RowLink k 3 (glue A J []) (glue A J []) := by
  have hc := List.isChain_cons.mp hT.seams
  have hL : Trail k (A ++ [r]) :=
    ⟨by simp, fun y hy => hT.len y (List.mem_cons_of_mem _ hy), hc.2⟩
  have hF : Trail k [r₁] :=
    ⟨by simp, fun y hy => hT.len y (by rw [List.mem_singleton.mp hy]; exact List.mem_cons_self),
      List.isChain_singleton _⟩
  refine ⟨hJ.trail_glue hL hF, pairwise_of_perm_cons hcl hx (ring_glue_entries hJ), ?_⟩
  unfold RowLink
  rw [hJ.rowsLast_glue, hJ.rowsFirst_glue]
  intro u hu v hv
  rw [rowsLast_singleton] at hu
  rw [Option.mem_def, Option.some.injEq] at hu
  subst hu
  unfold rowsFirst at hv
  obtain ⟨y, hy, rfl⟩ := Option.mem_map.mp hv
  exact hc.1 y hy

theorem ring_glue_length (A J : List (NRow k)) : (glue A J []).length = A.length + J.length := by
  rw [Junction.length_glue]
  simp

theorem ring_glue_holes (A J : List (NRow k)) (r r₁ : NRow k) :
    rowsHoles k (glue A J []) + rowsHoles k [r, r₁] =
      rowsHoles k (r₁ :: (A ++ [r])) + rowsHoles k J := by
  simp only [Junction.holes_glue, rowsHoles_append, rowsHoles_cons, rowsHoles_nil]
  omega

end ring

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.path_glue
#print axioms SuperpermLowerBounds.path_glue_links
#print axioms SuperpermLowerBounds.ring_glue

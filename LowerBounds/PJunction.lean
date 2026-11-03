import LowerBounds.PGeom

/-!
# Junctions (the written proof, section 2, (G4) and (G5), in one form)

A trail that ends with the row `r` and a trail that begins with the row `r₁` are glued through a
*junction* `J`: a short trail that begins like `r`, ends like `r₁` and whose blocks are those of
`r` and `r₁` and one more class `x`.  Three junctions occur:

* `junction_extLast`: `[extLast r, r₁]` (the block `x = τ₂ g` added at the end of `r`, when the
  exit of that block overlaps `r₁` at weight 3);
* `junction_extFirst`: `[r, extFirst y r₁]` (the block `y` added in front of `r₁`);
* `junction_merge`: `[mergeRow r r₁]` (the two rows and the class between them as one row).

`glue A J B = A ++ (J ++ B)` is the glued trail; `Junction.trail_glue`, `rowsFirst_glue`,
`rowsLast_glue`, `entries_glue`, `holes_glue` are its properties.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- `J` joins a trail that ends with `r` to a trail that begins with `r₁`, using the class of
`x`. -/
structure Junction (k : ℕ) (r r₁ : NRow k) (x : Vtx k) (J : List (NRow k)) : Prop where
  trail : Trail k J
  first : rowsFirst J = some r.entry
  last : rowsLast J = some r₁.lastEntry
  entries : (rowsEntries J).Perm (x :: (r.entries ++ r₁.entries))

/-- The glued list of rows. -/
def glue (A J B : List (NRow k)) : List (NRow k) := A ++ (J ++ B)

theorem rowsEntries_nil : rowsEntries ([] : List (NRow k)) = [] := rfl

theorem rowsFirst_cons (r : NRow k) (A : List (NRow k)) : rowsFirst (r :: A) = some r.entry := rfl

theorem rowsLast_concat (A : List (NRow k)) (r : NRow k) :
    rowsLast (A ++ [r]) = some r.lastEntry := by
  unfold rowsLast
  rw [List.getLast?_concat]
  rfl

theorem rowsLast_singleton (r : NRow k) : rowsLast [r] = some r.lastEntry := rfl

namespace Junction

variable {r r₁ : NRow k} {x : Vtx k} {J A B : List (NRow k)}

theorem head_entry (h : Junction k r r₁ x J) : ∀ j ∈ J.head?, j.entry = r.entry := by
  intro j hj
  have h1 := h.first
  unfold rowsFirst at h1
  rw [Option.mem_def.mp hj] at h1
  exact Option.some.inj h1

theorem last_lastEntry (h : Junction k r r₁ x J) :
    ∀ j ∈ J.getLast?, j.lastEntry = r₁.lastEntry := by
  intro j hj
  have h1 := h.last
  unfold rowsLast at h1
  rw [Option.mem_def.mp hj] at h1
  exact Option.some.inj h1

/-- The glued list is a trail. -/
theorem trail_glue (h : Junction k r r₁ x J) (hL : Trail k (A ++ [r])) (hF : Trail k (r₁ :: B)) :
    Trail k (glue A J B) where
  ne := by
    unfold glue
    intro e
    exact h.trail.ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).2).1
  len := by
    unfold glue
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact hL.len y (List.mem_append_left _ h1)
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact h.trail.len y h2
      · exact hF.len y (List.mem_cons_of_mem _ h2)
  seams := by
    unfold glue
    have hA := List.isChain_append.mp hL.seams
    have hB := List.isChain_cons.mp hF.seams
    refine List.isChain_append.mpr ⟨hA.1, List.isChain_append.mpr ⟨h.trail.seams, hB.2, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [h.last_lastEntry a ha]
      exact hB.1 b hb
    · intro a ha b hb
      rw [List.head?_append_of_ne_nil _ h.trail.ne] at hb
      rw [h.head_entry b hb]
      exact hA.2.2 a ha r rfl

theorem rowsFirst_glue (h : Junction k r r₁ x J) :
    rowsFirst (glue A J B) = rowsFirst (A ++ [r]) := by
  unfold glue
  cases A with
  | nil =>
      rw [List.nil_append, List.nil_append, rowsFirst_append h.trail.ne, h.first]
      rfl
  | cons a A' => rfl

theorem rowsLast_glue (h : Junction k r r₁ x J) :
    rowsLast (glue A J B) = rowsLast (r₁ :: B) := by
  unfold glue
  rw [← List.append_assoc]
  rcases List.eq_nil_or_concat B with rfl | ⟨B', b, rfl⟩
  · rw [List.append_nil, rowsLast_append h.trail.ne, h.last]
    rfl
  · rw [List.concat_eq_append, ← List.append_assoc, rowsLast_concat]
    exact (rowsLast_concat (r₁ :: B') b).symm

/-- The blocks of the glued list: those of the two trails and `x`. -/
theorem entries_glue (h : Junction k r r₁ x J) :
    (rowsEntries (glue A J B)).Perm
      (x :: (rowsEntries (A ++ [r]) ++ rowsEntries (r₁ :: B))) := by
  unfold glue
  rw [rowsEntries_append, rowsEntries_append, rowsEntries_append, rowsEntries_cons r,
    rowsEntries_cons r₁, rowsEntries_nil, List.append_nil]
  have h1 : (rowsEntries A ++ (rowsEntries J ++ rowsEntries B)).Perm
      (rowsEntries A ++ ((x :: (r.entries ++ r₁.entries)) ++ rowsEntries B)) :=
    List.Perm.append_left _ (List.Perm.append_right _ h.entries)
  refine h1.trans ?_
  rw [List.cons_append]
  refine List.perm_middle.trans ?_
  rw [List.append_assoc, List.append_assoc]

theorem length_glue (A J B : List (NRow k)) :
    (glue A J B).length = A.length + J.length + B.length := by
  unfold glue
  rw [List.length_append, List.length_append]
  omega

theorem holes_glue (A J B : List (NRow k)) :
    rowsHoles k (glue A J B) = rowsHoles k A + rowsHoles k J + rowsHoles k B := by
  unfold glue
  rw [rowsHoles_append, rowsHoles_append]
  omega

end Junction

/-! ### The three junctions -/

/-- (G4), case (i): the block `τ₂ g` at the end of `r`. -/
theorem junction_extLast {r r₁ : NRow k} (hr : 1 ≤ r.len) (hr₁ : 1 ≤ r₁.len)
    (hl : SLink k 3 (tau2V r.lastEntry) r₁.entry) :
    Junction k r r₁ (tau2V r.lastEntry) [extLast r, r₁] where
  trail := by
    refine ⟨by simp, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · show 1 ≤ r.len + 1
        omega
      · exact hr₁
    · rw [List.isChain_cons_cons, extLast_lastEntry hr]
      exact ⟨hl, List.isChain_singleton _⟩
  first := rfl
  last := rfl
  entries := by
    rw [rowsEntries_cons, rowsEntries_cons, rowsEntries, extLast_entries hr]
    simp only [List.flatMap_nil, List.append_nil]
    rw [List.append_assoc]
    exact List.perm_middle

/-- (G4), case (ii): the block `y` in front of `r₁`. -/
theorem junction_extFirst {r r₁ : NRow k} {y : Vtx k} (hr : 1 ≤ r.len) (hr₁ : 1 ≤ r₁.len)
    (hy : r₁.entry = tau2V y) (hl : SLink k 3 r.lastEntry y) :
    Junction k r r₁ y [r, extFirst y r₁] where
  trail := by
    refine ⟨by simp, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hr
      · show 1 ≤ r₁.len + 1
        omega
    · rw [List.isChain_cons_cons]
      exact ⟨hl, List.isChain_singleton _⟩
  first := rfl
  last := by
    show some (extFirst y r₁).lastEntry = _
    rw [extFirst_lastEntry hy hr₁]
  entries := by
    rw [rowsEntries_cons, rowsEntries_cons, rowsEntries, extFirst_entries hy]
    simp only [List.flatMap_nil, List.append_nil]
    exact List.perm_middle

/-- (G5): the two rows and the class between them as one row. -/
theorem junction_merge {r r₁ : NRow k} (hr : 1 ≤ r.len) (hr₁ : 1 ≤ r₁.len)
    (h : r₁.entry = tau2V (tau2V r.lastEntry)) :
    Junction k r r₁ (tau2V r.lastEntry) [mergeRow r r₁] where
  trail := by
    refine ⟨by simp, ?_, List.isChain_singleton _⟩
    intro z hz
    rw [List.mem_singleton.mp hz]
    show 1 ≤ r.len + (r₁.len + 1)
    omega
  first := rfl
  last := by
    show some (mergeRow r r₁).lastEntry = _
    rw [mergeRow_lastEntry hr hr₁ h]
  entries := by
    rw [rowsEntries_cons, rowsEntries, mergeRow_entries hr h]
    simp only [List.flatMap_nil, List.append_nil]
    exact List.perm_middle

/-! ### Holes of the junctions (7 symbols) -/

theorem holes_extLast {r r₁ : NRow 7} (h : r.len + 1 ≤ 6) :
    rowsHoles 7 [extLast r, r₁] + 1 = rowsHoles 7 [r, r₁] := by
  simp only [rowsHoles_cons, rowsHoles_nil, extLast]
  omega

theorem holes_extFirst {r r₁ : NRow 7} {y : Vtx 7} (h₁ : r₁.len + 1 ≤ 6) :
    rowsHoles 7 [r, extFirst y r₁] + 1 = rowsHoles 7 [r, r₁] := by
  simp only [rowsHoles_cons, rowsHoles_nil, extFirst]
  omega

theorem holes_merge {r r₁ : NRow 7} (h : r.len + (r₁.len + 1) ≤ 6) :
    rowsHoles 7 [mergeRow r r₁] + 7 = rowsHoles 7 [r, r₁] := by
  simp only [rowsHoles_cons, rowsHoles_nil, mergeRow]
  omega

/-- A row of a list with pairwise different classes has at most `k - 1` blocks. -/
theorem len_le_of_rowsEntries_pairwise (hk : 2 ≤ k) {R : List (NRow k)}
    (h : (rowsEntries R).Pairwise (NotRot (k := k))) {r : NRow k} (hr : r ∈ R) :
    r.len ≤ k - 1 := by
  unfold rowsEntries at h
  rw [List.pairwise_flatMap] at h
  exact NRow.len_le_of_pairwise hk r (h.1 r hr)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Junction.trail_glue
#print axioms SuperpermLowerBounds.Junction.entries_glue
#print axioms SuperpermLowerBounds.junction_extLast
#print axioms SuperpermLowerBounds.junction_extFirst
#print axioms SuperpermLowerBounds.junction_merge

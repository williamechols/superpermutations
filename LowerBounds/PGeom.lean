import LowerBounds.PModel

/-!
# Geometry of rows for 5,899 (the written proof, section 2)

Statements about words, rows and lists of rows; no configuration occurs.

* `sLink_three_tau2V_tau2V` (G1): the exit of the block entered at `g` and `τ₂² g` overlap in
  `k - 3` symbols.
* rows: `NRow.entries_add`; the row extended by one block at its end (`extLast`) or at its
  beginning (`extFirst`); two rows of one 2-cycle with one class between them merged into one
  row (`mergeRow`).
* trails: `Trail.append`, `Trail.replace`, `Trail.merge`.
* lists of trails: `rotSegs` (the first trail is glued behind the last one), `TrailFam.rot`,
  `rot_links`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### (G1) -/

theorem exists_two_mid_last {l : List ℕ} (h : 3 ≤ l.length) :
    ∃ x y M m, l = x :: y :: (M ++ [m]) ∧ M.length + 3 = l.length := by
  match l, h with
  | x :: y :: z :: t, _ =>
      refine ⟨x, y, (z :: t).dropLast, (z :: t).getLast (List.cons_ne_nil _ _), ?_, ?_⟩
      · rw [List.dropLast_concat_getLast]
      · simp [List.length_dropLast]

/-- **(G1).**  The exit of the block entered at `g` overlaps `τ₂² g` in `k - 3` symbols. -/
theorem sLink_three_tau2V_tau2V (hk : 3 ≤ k) (g : Vtx k) : SLink k 3 g (tau2V (tau2V g)) := by
  have hlen : (g : List ℕ).length = k := g.2.length
  obtain ⟨x, y, M, m, hg, hM⟩ := exists_two_mid_last (l := (g : List ℕ)) (by omega)
  have h1 : ((tau2V g : Vtx k) : List ℕ) = (y :: M) ++ [x, m] :=
    tau2V_cons_append (by omega) g x (y :: M) m (by rw [hg]; rfl)
  have h2 : ((tau2V (tau2V g) : Vtx k) : List ℕ) = (M ++ [x]) ++ [y, m] :=
    tau2V_cons_append (by omega) (tau2V g) y (M ++ [x]) m (by rw [h1]; simp)
  unfold SLink
  rw [h2, hg]
  have e : x :: y :: (M ++ [m]) = (x :: y :: M) ++ [m] := rfl
  have hk1 : k - 1 = (x :: y :: M).length := by
    simp only [List.length_cons]
    omega
  have e3 : k - 3 = M.length := by omega
  rw [e, hk1, List.rotate_append_length_eq, e3, List.append_assoc, List.take_left' rfl]
  rfl

/-! ### Rows -/

theorem NRow.entries_zero (e : Vtx k) : NRow.entries ⟨e, 0⟩ = [] := rfl

theorem NRow.entries_add (a b : ℕ) : ∀ e : Vtx k,
    NRow.entries ⟨e, a + b⟩ = NRow.entries ⟨e, a⟩ ++ NRow.entries ⟨tau2V^[a] e, b⟩ := by
  induction a with
  | zero =>
      intro e
      rw [Nat.zero_add, NRow.entries_zero]
      rfl
  | succ a ih =>
      intro e
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h, NRow.entries_succ, NRow.entries_succ, ih (tau2V e), List.cons_append]
      rfl

theorem NRow.lastEntry_mk (e : Vtx k) (n : ℕ) :
    (NRow.lastEntry ⟨e, n + 1⟩ : Vtx k) = tau2V^[n] e := rfl

theorem NRow.tau2V_lastEntry {r : NRow k} (h : 1 ≤ r.len) :
    tau2V r.lastEntry = tau2V^[r.len] r.entry := by
  unfold NRow.lastEntry
  rw [← Function.iterate_succ_apply' tau2V]
  congr 1
  omega

/-- The row with one more block at its end. -/
def extLast (r : NRow k) : NRow k := ⟨r.entry, r.len + 1⟩

theorem extLast_entries {r : NRow k} (h : 1 ≤ r.len) :
    (extLast r).entries = r.entries ++ [tau2V r.lastEntry] := by
  obtain ⟨e, l⟩ := r
  unfold extLast
  rw [NRow.entries_concat, NRow.tau2V_lastEntry h]

theorem extLast_lastEntry {r : NRow k} (h : 1 ≤ r.len) :
    (extLast r).lastEntry = tau2V r.lastEntry := by
  rw [NRow.tau2V_lastEntry h]
  rfl

/-- The row with one more block, entered at `y`, at its beginning. -/
def extFirst (y : Vtx k) (r : NRow k) : NRow k := ⟨y, r.len + 1⟩

theorem extFirst_entries {r : NRow k} {y : Vtx k} (hy : r.entry = tau2V y) :
    (extFirst y r).entries = y :: r.entries := by
  obtain ⟨e, l⟩ := r
  simp only at hy
  unfold extFirst
  rw [NRow.entries_succ, hy]

theorem extFirst_lastEntry {r : NRow k} {y : Vtx k} (hy : r.entry = tau2V y) (h : 1 ≤ r.len) :
    (extFirst y r).lastEntry = r.lastEntry := by
  obtain ⟨e, l⟩ := r
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by simp only at h; omega⟩
  simp only at hy
  show tau2V^[n + 1] y = tau2V^[n] e
  rw [Function.iterate_succ_apply, hy]

/-- Two rows of one 2-cycle with one class between them, as one row. -/
def mergeRow (r₁ r₂ : NRow k) : NRow k := ⟨r₁.entry, r₁.len + (r₂.len + 1)⟩

theorem mergeRow_entries {r₁ r₂ : NRow k} (h1 : 1 ≤ r₁.len)
    (h : r₂.entry = tau2V (tau2V r₁.lastEntry)) :
    (mergeRow r₁ r₂).entries = r₁.entries ++ tau2V r₁.lastEntry :: r₂.entries := by
  obtain ⟨e₁, a⟩ := r₁
  obtain ⟨e₂, b⟩ := r₂
  simp only at h h1
  unfold mergeRow
  simp only
  rw [NRow.entries_add, NRow.entries_succ]
  have ht : tau2V^[a] e₁ = tau2V (NRow.lastEntry ⟨e₁, a⟩) := (NRow.tau2V_lastEntry (r := ⟨e₁, a⟩) h1).symm
  rw [ht, ← h]

theorem mergeRow_lastEntry {r₁ r₂ : NRow k} (h1 : 1 ≤ r₁.len) (h2 : 1 ≤ r₂.len)
    (h : r₂.entry = tau2V (tau2V r₁.lastEntry)) :
    (mergeRow r₁ r₂).lastEntry = r₂.lastEntry := by
  obtain ⟨e₁, a⟩ := r₁
  obtain ⟨e₂, b⟩ := r₂
  simp only at h h1 h2
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have ht : tau2V^[a] e₁ = tau2V (NRow.lastEntry ⟨e₁, a⟩) := (NRow.tau2V_lastEntry (r := ⟨e₁, a⟩) h1).symm
  show tau2V^[a + (n + 1 + 1) - 1] e₁ = tau2V^[n] e₂
  have e : a + (n + 1 + 1) - 1 = n + 1 + a := by omega
  rw [e, Function.iterate_add_apply, ht, Function.iterate_succ_apply, ← h]

/-! ### Holes -/

theorem rowsHoles_nil : rowsHoles k [] = 0 := rfl

theorem rowsHoles_cons (r : NRow k) (A : List (NRow k)) :
    rowsHoles k (r :: A) = (k - 1 - r.len) + rowsHoles k A := by
  unfold rowsHoles
  rw [List.map_cons, List.sum_cons]

theorem rowsHoles_singleton (r : NRow k) : rowsHoles k [r] = k - 1 - r.len := by
  rw [rowsHoles_cons, rowsHoles_nil, Nat.add_zero]

/-- Blocks plus holes: every row has `k - 1` places. -/
theorem rowsEntries_length_add_holes : ∀ {R : List (NRow k)}, (∀ r ∈ R, r.len ≤ k - 1) →
    (rowsEntries R).length + rowsHoles k R = (k - 1) * R.length
  | [], _ => by simp [rowsEntries, rowsHoles]
  | r :: R, h => by
      have ih := rowsEntries_length_add_holes (R := R) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hr := h r List.mem_cons_self
      rw [rowsEntries_cons, List.length_append, NRow.entries_length, rowsHoles_cons,
        List.length_cons, Nat.mul_succ]
      omega

/-! ### Classes -/

theorem pairwise_of_perm_cons {l l' : List (Vtx k)} {x : Vtx k}
    (h : l.Pairwise (NotRot (k := k))) (hx : ∀ e ∈ l, NotRot x e) (hp : l'.Perm (x :: l)) :
    l'.Pairwise (NotRot (k := k)) :=
  (hp.pairwise_iff (fun h => NotRot.symm h)).mpr (List.pairwise_cons.mpr ⟨hx, h⟩)

theorem pairwise_of_perm {l l' : List (Vtx k)} (h : l.Pairwise (NotRot (k := k)))
    (hp : l'.Perm l) : l'.Pairwise (NotRot (k := k)) :=
  (hp.pairwise_iff (fun h => NotRot.symm h)).mpr h

/-! ### Links between lists of rows -/

theorem rowLink_iff {d : ℕ} {A B : List (NRow k)} :
    RowLink k d A B ↔ ∀ r ∈ A.getLast?, ∀ r' ∈ B.head?, SLink k d r.lastEntry r'.entry := by
  unfold RowLink rowsLast rowsFirst
  constructor
  · intro h r hr r' hr'
    exact h _ (Option.mem_map_of_mem _ hr) _ (Option.mem_map_of_mem _ hr')
  · intro h u hu v hv
    obtain ⟨r, hr, rfl⟩ := Option.mem_map.mp hu
    obtain ⟨r', hr', rfl⟩ := Option.mem_map.mp hv
    exact h r hr r' hr'

theorem rowsFirst_append {A : List (NRow k)} (hA : A ≠ []) (B : List (NRow k)) :
    rowsFirst (A ++ B) = rowsFirst A := by
  unfold rowsFirst
  rw [List.head?_append_of_ne_nil _ hA]

theorem rowsLast_append {B : List (NRow k)} (hB : B ≠ []) (A : List (NRow k)) :
    rowsLast (A ++ B) = rowsLast B := by
  unfold rowsLast
  rw [List.getLast?_append_of_ne_nil _ hB]

theorem RowLink.append_right {d : ℕ} {X A : List (NRow k)} (h : RowLink k d X A) (hA : A ≠ [])
    (B : List (NRow k)) : RowLink k d X (A ++ B) := by
  unfold RowLink at h ⊢
  rw [rowsFirst_append hA]
  exact h

theorem RowLink.append_left {d : ℕ} {B X : List (NRow k)} (h : RowLink k d B X) (hB : B ≠ [])
    (A : List (NRow k)) : RowLink k d (A ++ B) X := by
  unfold RowLink at h ⊢
  rw [rowsLast_append hB]
  exact h

/-! ### Trails -/

theorem Trail.append {A B : List (NRow k)} (hA : Trail k A) (hB : Trail k B)
    (h : RowLink k 3 A B) : Trail k (A ++ B) where
  ne := by
    intro e
    exact hA.ne (List.append_eq_nil_iff.mp e).1
  len := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h1
    · exact hA.len r h1
    · exact hB.len r h1
  seams := List.isChain_append.mpr ⟨hA.seams, hB.seams, rowLink_iff.mp h⟩

/-- A relation that only looks at the last block of the left row and the first block of the
right row: the middle row of a chain can be replaced by a row with the same first and last
block. -/
theorem isChain_replace {α : Type*} {R : α → α → Prop} {A B : List α} {a c : α}
    (h : (A ++ a :: B).IsChain R) (hin : ∀ x, R x a → R x c) (hout : ∀ y, R a y → R c y) :
    (A ++ c :: B).IsChain R := by
  rw [List.isChain_append] at h ⊢
  obtain ⟨hA, haB, hl⟩ := h
  refine ⟨hA, ?_, ?_⟩
  · rw [List.isChain_cons] at haB ⊢
    exact ⟨fun y hy => hout y (haB.1 y hy), haB.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hin x (hl x hx a rfl)

/-- Two consecutive elements of a chain replaced by one that has the incoming relations of the
first and the outgoing relations of the second. -/
theorem isChain_merge {α : Type*} {R : α → α → Prop} {A B : List α} {a b c : α}
    (h : (A ++ a :: b :: B).IsChain R) (hin : ∀ x, R x a → R x c) (hout : ∀ y, R b y → R c y) :
    (A ++ c :: B).IsChain R := by
  rw [List.isChain_append] at h ⊢
  obtain ⟨hA, haB, hl⟩ := h
  rw [List.isChain_cons_cons] at haB
  refine ⟨hA, ?_, ?_⟩
  · have hb := haB.2
    rw [List.isChain_cons] at hb ⊢
    exact ⟨fun y hy => hout y (hb.1 y hy), hb.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hin x (hl x hx a rfl)

/-- A row of a trail replaced by a row with the same first and last block. -/
theorem Trail.replace {A B : List (NRow k)} {r r' : NRow k} (h : Trail k (A ++ r :: B))
    (he : r'.entry = r.entry) (hl : r'.lastEntry = r.lastEntry) (hlen : 1 ≤ r'.len) :
    Trail k (A ++ r' :: B) where
  ne := by simp
  len := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.len x (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hlen
      · exact h.len x (List.mem_append_right _ (List.mem_cons_of_mem _ h2))
  seams := isChain_replace h.seams (fun x hx => by rw [he]; exact hx)
    (fun y hy => by rw [hl]; exact hy)

/-- Two consecutive rows of a trail replaced by a row that begins like the first and ends like
the second. -/
theorem Trail.merge {A B : List (NRow k)} {r₁ r₂ r' : NRow k}
    (h : Trail k (A ++ r₁ :: r₂ :: B)) (he : r'.entry = r₁.entry)
    (hl : r'.lastEntry = r₂.lastEntry) (hlen : 1 ≤ r'.len) : Trail k (A ++ r' :: B) where
  ne := by simp
  len := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.len x (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hlen
      · exact h.len x (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)))
  seams := isChain_merge h.seams (fun x hx => by rw [he]; exact hx)
    (fun y hy => by rw [hl]; exact hy)

/-! ### Lists of trails: the first trail glued behind the last one -/

/-- The list of trails read cyclically from the second trail: the first trail is glued behind
the last one. -/
def rotSegs (S : List (List (NRow k))) : List (List (NRow k)) :=
  S.tail.dropLast ++ [S.getLast?.getD [] ++ S.head?.getD []]

theorem rotSegs_eq (first last : List (NRow k)) (mid : List (List (NRow k))) :
    rotSegs (first :: (mid ++ [last])) = mid ++ [last ++ first] := by
  unfold rotSegs
  have h : (first :: (mid ++ [last])).getLast? = some last := by
    rw [← List.cons_append, List.getLast?_concat]
  rw [h]
  simp

theorem exists_first_mid_last {α : Type*} {S : List α} (h : 2 ≤ S.length) :
    ∃ first mid last, S = first :: (mid ++ [last]) := by
  match S, h with
  | a :: b :: t, _ =>
      exact ⟨a, (b :: t).dropLast, (b :: t).getLast (List.cons_ne_nil _ _),
        by rw [List.dropLast_concat_getLast]⟩

theorem TrailFam.rot {first last : List (NRow k)} {mid : List (List (NRow k))}
    (h : TrailFam k (first :: (mid ++ [last]))) (hc : RowLink k 3 last first) :
    TrailFam k (mid ++ [last ++ first]) where
  trails := by
    intro A hA
    rcases List.mem_append.mp hA with h1 | h1
    · exact h.trails A (List.mem_cons_of_mem _ (List.mem_append_left _ h1))
    · rw [List.mem_singleton.mp h1]
      exact (h.trails last (by simp)).append (h.trails first List.mem_cons_self) hc
  classes := by
    refine pairwise_of_perm h.classes ?_
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      rowsEntries_append]
    rw [← List.append_assoc]
    exact List.perm_append_comm

theorem rot_links {d : ℕ} {first last : List (NRow k)} {mid : List (List (NRow k))}
    (hlast : last ≠ []) (hl : (first :: (mid ++ [last])).IsChain (RowLink k d)) :
    (mid ++ [last ++ first]).IsChain (RowLink k d) := by
  have h1 := hl.tail
  rw [List.tail_cons, List.isChain_append] at h1
  rw [List.isChain_append]
  refine ⟨h1.1, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact (h1.2.2 x hx last rfl).append_right hlast first

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.sLink_three_tau2V_tau2V
#print axioms SuperpermLowerBounds.mergeRow_entries
#print axioms SuperpermLowerBounds.mergeRow_lastEntry
#print axioms SuperpermLowerBounds.Trail.merge
#print axioms SuperpermLowerBounds.TrailFam.rot
#print axioms SuperpermLowerBounds.rot_links

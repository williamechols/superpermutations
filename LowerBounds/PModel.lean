import LowerBounds.NRules
import LowerBounds.SBridge

/-!
# Objects of the finite statements for 5,899 (the written proof, section 1)

* `IsFamily k F`: a list of model chains (`IsModelChain`, `SModelDef.lean`) whose blocks lie in
  pairwise different rotation classes.
* `IsPath k F`: a family in which the last block of every chain and the first block of the next
  chain overlap in `k - 4` symbols (a link of weight 4).
* `IsRing k C`: a chain with at least two rows whose last block and first block overlap in
  `k - 3` symbols.
* the four kinds of finite statements: `ChainCap`, `PathCap`, `RingCap`, `NoProfile`.

The second half translates lists of rows (`NRow`) into these objects: `TrailFam` is a list of
trails (lists of rows joined at overlap weight 3) with pairwise different classes, and
`chain_cap_rows`, `path_cap_rows`, `ring_cap_rows`, `noProfile_rows` are the finite statements
read on rows.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- Two vertices in different rotation classes. -/
abbrev NotRot (a b : Vtx k) : Prop := ¬ ((a : List ℕ) ~r (b : List ℕ))

theorem NotRot.symm {a b : Vtx k} (h : NotRot a b) : NotRot b a := fun hr => h hr.symm

instance : Std.Symm (NotRot (k := k)) := ⟨fun _ _ h => h.symm⟩

/-! ### Chains, families, paths, rings -/

/-- The number of holes of a chain: the sum of the deficits of its pieces. -/
def holesL (k : ℕ) (C : List (List (Vtx k))) : ℕ := (modelDeficits k C).sum

/-- The first block entry of a chain. -/
def chainFirst (C : List (List (Vtx k))) : Option (Vtx k) := C.head?.bind List.head?

/-- The last block entry of a chain. -/
def chainLast (C : List (List (Vtx k))) : Option (Vtx k) := C.getLast?.bind List.getLast?

/-- The last block of `A` and the first block of `B` overlap in `k - d` symbols. -/
def ChainLink (k d : ℕ) (A B : List (List (Vtx k))) : Prop :=
  ∀ u ∈ chainLast A, ∀ v ∈ chainFirst B, SLink k d u v

/-- The number of rows of a list of chains. -/
def famRows (F : List (List (List (Vtx k)))) : ℕ := (F.map List.length).sum

/-- The number of holes of a list of chains. -/
def famHoles (k : ℕ) (F : List (List (List (Vtx k)))) : ℕ := (F.map (holesL k)).sum

/-- A family: non-empty chains with pairwise different classes. -/
structure IsFamily (k : ℕ) (F : List (List (List (Vtx k)))) : Prop where
  chains : ∀ C ∈ F, IsModelChain k C
  ne : ∀ C ∈ F, C ≠ []
  classes : F.flatten.flatten.Pairwise (NotRot (k := k))

/-- A sequence with links of weight 4: a family whose consecutive chains are joined at overlap
weight 4.  The number of links is `F.length - 1`. -/
structure IsPath (k : ℕ) (F : List (List (List (Vtx k)))) : Prop extends IsFamily k F where
  links : F.IsChain (ChainLink k 4)

/-- A ring: a chain with at least two rows that closes at overlap weight 3. -/
structure IsRing (k : ℕ) (C : List (List (Vtx k))) : Prop where
  chain : IsModelChain k C
  two : 2 ≤ C.length
  closes : ChainLink k 3 C C

/-! ### The finite statements (7 symbols) -/

/-- F0: a chain with `x ≤ G` holes has at most `M x` rows. -/
def ChainCap (M : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ C : List (List (Vtx 7)), IsModelChain 7 C → holesL 7 C ≤ G → C.length ≤ M (holesL 7 C)

/-- F_s: a sequence with exactly `s` links of weight 4 and `x ≤ G` holes has at most `P x`
rows. -/
def PathCap (s : ℕ) (P : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ F : List (List (List (Vtx 7))), IsPath 7 F → F.length = s + 1 → famHoles 7 F ≤ G →
    famRows F ≤ P (famHoles 7 F)

/-- FR: a ring with `x ≤ G` holes has at most `PR x` rows. -/
def RingCap (PR : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ C : List (List (Vtx 7)), IsRing 7 C → holesL 7 C ≤ G → C.length ≤ PR (holesL 7 C)

/-- FF: there is no family whose chains, in order, have at least `t.1` rows and at most `t.2`
holes for the targets `t` of the list. -/
def NoProfile (ts : List (ℕ × ℕ)) : Prop :=
  ¬ ∃ F : List (List (List (Vtx 7))), IsFamily 7 F ∧
    List.Forall₂ (fun C t => t.1 ≤ C.length ∧ holesL 7 C ≤ t.2) F ts

/-! ### Rows -/

theorem NRow.entries_length (r : NRow k) : r.entries.length = r.len := by
  unfold NRow.entries
  rw [List.length_map, List.length_range]

theorem NRow.entries_ne_nil {r : NRow k} (h : 1 ≤ r.len) : r.entries ≠ [] := by
  intro e
  have := NRow.entries_length r
  rw [e] at this
  simp at this
  omega

theorem NRow.entries_head? {r : NRow k} (h : 1 ≤ r.len) : r.entries.head? = some r.entry := by
  obtain ⟨e, l⟩ := r
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by simp only at h; omega⟩
  rw [NRow.entries_succ]
  rfl

theorem NRow.entries_concat (e : Vtx k) (n : ℕ) :
    NRow.entries ⟨e, n + 1⟩ = NRow.entries ⟨e, n⟩ ++ [tau2V^[n] e] := by
  unfold NRow.entries
  simp only
  rw [List.range_succ, List.map_append]
  rfl

theorem NRow.entries_getLast? {r : NRow k} (h : 1 ≤ r.len) :
    r.entries.getLast? = some r.lastEntry := by
  obtain ⟨e, l⟩ := r
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by simp only at h; omega⟩
  rw [NRow.entries_concat, List.getLast?_append]
  rfl

/-- The blocks of a row are joined by doors. -/
theorem NRow.entries_isChain (hk : 2 ≤ k) : ∀ (n : ℕ) (e : Vtx k),
    (NRow.entries ⟨e, n⟩).IsChain (SLink k 2)
  | 0, _ => by
      unfold NRow.entries
      simp
  | 1, e => by
      rw [NRow.entries_one]
      exact List.isChain_singleton _
  | n + 2, e => by
      rw [NRow.entries_succ, NRow.entries_succ, List.isChain_cons_cons]
      refine ⟨sLink_two_tau2V hk e, ?_⟩
      have h := NRow.entries_isChain hk (n + 1) (tau2V e)
      rwa [NRow.entries_succ] at h

/-- The number of holes of a list of rows. -/
def rowsHoles (k : ℕ) (R : List (NRow k)) : ℕ := (R.map fun r => k - 1 - r.len).sum

theorem modelDeficits_rows (R : List (NRow k)) :
    modelDeficits k (R.map NRow.entries) = R.map fun r => k - 1 - r.len := by
  unfold modelDeficits
  rw [List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp, NRow.entries_length]

theorem holesL_rows (R : List (NRow k)) : holesL k (R.map NRow.entries) = rowsHoles k R := by
  unfold holesL rowsHoles
  rw [modelDeficits_rows]

theorem rowsEntries_eq (R : List (NRow k)) : (R.map NRow.entries).flatten = rowsEntries R := by
  unfold rowsEntries
  rw [List.flatMap_def]

theorem rowsEntries_append (A B : List (NRow k)) :
    rowsEntries (A ++ B) = rowsEntries A ++ rowsEntries B := by
  unfold rowsEntries
  rw [List.flatMap_append]

theorem rowsEntries_cons (r : NRow k) (A : List (NRow k)) :
    rowsEntries (r :: A) = r.entries ++ rowsEntries A := by
  unfold rowsEntries
  rw [List.flatMap_cons]

/-- The first entry of a list of rows. -/
def rowsFirst (R : List (NRow k)) : Option (Vtx k) := R.head?.map NRow.entry

/-- The last block entry of a list of rows. -/
noncomputable def rowsLast (R : List (NRow k)) : Option (Vtx k) := R.getLast?.map NRow.lastEntry

theorem chainFirst_rows {R : List (NRow k)} (hlen : ∀ r ∈ R, 1 ≤ r.len) :
    chainFirst (R.map NRow.entries) = rowsFirst R := by
  unfold chainFirst rowsFirst
  cases R with
  | nil => rfl
  | cons r rest =>
      simp only [List.map_cons, List.head?_cons, Option.bind_some, Option.map_some]
      exact NRow.entries_head? (hlen r List.mem_cons_self)

theorem chainLast_rows {R : List (NRow k)} (hlen : ∀ r ∈ R, 1 ≤ r.len) :
    chainLast (R.map NRow.entries) = rowsLast R := by
  unfold chainLast rowsLast
  rw [List.getLast?_map]
  cases h : R.getLast? with
  | none => rfl
  | some r =>
      simp only [Option.map_some, Option.bind_some]
      exact NRow.entries_getLast? (hlen r (List.mem_of_getLast? h))

/-- The last block of `A` and the first block of `B` overlap in `k - d` symbols. -/
def RowLink (k d : ℕ) (A B : List (NRow k)) : Prop :=
  ∀ u ∈ rowsLast A, ∀ v ∈ rowsFirst B, SLink k d u v

theorem chainLink_rows {d : ℕ} {A B : List (NRow k)} (hA : ∀ r ∈ A, 1 ≤ r.len)
    (hB : ∀ r ∈ B, 1 ≤ r.len) (h : RowLink k d A B) :
    ChainLink k d (A.map NRow.entries) (B.map NRow.entries) := by
  unfold ChainLink
  rw [chainLast_rows hA, chainFirst_rows hB]
  exact h

/-- A trail: a non-empty list of rows of positive length, consecutive rows joined at overlap
weight 3.  (No condition on classes.) -/
structure Trail (k : ℕ) (A : List (NRow k)) : Prop where
  ne : A ≠ []
  len : ∀ r ∈ A, 1 ≤ r.len
  seams : A.IsChain (fun r r' => SLink k 3 r.lastEntry r'.entry)

/-- A trail with pairwise different classes is a model chain. -/
theorem Trail.isModelChain (hk : 2 ≤ k) {A : List (NRow k)} (h : Trail k A)
    (hcl : (rowsEntries A).Pairwise (NotRot (k := k))) : IsModelChain k (A.map NRow.entries) where
  pieces_ne := by
    intro P hP
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hP
    exact NRow.entries_ne_nil (h.len r hr)
  size_le := by
    intro P hP
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hP
    rw [NRow.entries_length]
    have h1 := hcl
    unfold rowsEntries at h1
    rw [List.pairwise_flatMap] at h1
    exact NRow.len_le_of_pairwise hk r (h1.1 r hr)
  doors := by
    intro P hP
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hP
    exact NRow.entries_isChain hk r.len r.entry
  seams := by
    rw [List.isChain_map]
    have hs := h.seams
    have hl := h.len
    clear h hcl
    induction A with
    | nil => exact List.isChain_nil
    | cons r rest ih =>
        cases rest with
        | nil => exact List.isChain_singleton _
        | cons r' rest' =>
            rw [List.isChain_cons_cons] at hs ⊢
            refine ⟨?_, ih hs.2 (fun x hx => hl x (List.mem_cons_of_mem _ hx))⟩
            intro hP hQ
            have e1 : r.entries.getLast hP = r.lastEntry := by
              have := NRow.entries_getLast? (hl r List.mem_cons_self)
              rw [List.getLast?_eq_some_getLast hP] at this
              exact Option.some.inj this
            have e2 : r'.entries.head hQ = r'.entry := by
              have := NRow.entries_head? (hl r' (List.mem_cons_of_mem _ List.mem_cons_self))
              rw [List.head?_eq_some_head hQ] at this
              exact Option.some.inj this
            rw [e1, e2]
            exact hs.1
  classes := by
    rw [rowsEntries_eq]
    exact hcl

/-- A list of trails with pairwise different classes. -/
structure TrailFam (k : ℕ) (segs : List (List (NRow k))) : Prop where
  trails : ∀ A ∈ segs, Trail k A
  classes : (rowsEntries segs.flatten).Pairwise (NotRot (k := k))

/-- The chains of a list of trails. -/
noncomputable def toFam (segs : List (List (NRow k))) : List (List (List (Vtx k))) :=
  segs.map fun A => A.map NRow.entries

theorem toFam_flatten (segs : List (List (NRow k))) :
    (toFam segs).flatten.flatten = rowsEntries segs.flatten := by
  unfold toFam
  induction segs with
  | nil => rfl
  | cons A rest ih =>
      rw [List.map_cons, List.flatten_cons, List.flatten_append, ih, List.flatten_cons,
        rowsEntries_append, rowsEntries_eq]

theorem famRows_toFam (segs : List (List (NRow k))) :
    famRows (toFam segs) = segs.flatten.length := by
  unfold famRows toFam
  rw [List.map_map, List.length_flatten]
  congr 1
  apply List.map_congr_left
  intro A _
  simp only [Function.comp, List.length_map]

theorem rowsHoles_append (A B : List (NRow k)) :
    rowsHoles k (A ++ B) = rowsHoles k A + rowsHoles k B := by
  unfold rowsHoles
  rw [List.map_append, List.sum_append]

theorem famHoles_toFam (segs : List (List (NRow k))) :
    famHoles k (toFam segs) = rowsHoles k segs.flatten := by
  unfold famHoles toFam
  induction segs with
  | nil => rfl
  | cons A rest ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.flatten_cons, rowsHoles_append,
        holesL_rows]

theorem toFam_length (segs : List (List (NRow k))) : (toFam segs).length = segs.length := by
  unfold toFam
  rw [List.length_map]

theorem rowsEntries_sublist_flatten {A : List (NRow k)} {segs : List (List (NRow k))}
    (hA : A ∈ segs) : (rowsEntries A).Sublist (rowsEntries segs.flatten) := by
  rw [← rowsEntries_eq, ← rowsEntries_eq]
  exact ((List.sublist_flatten_of_mem hA).map NRow.entries).flatten

theorem TrailFam.isFamily (hk : 2 ≤ k) {segs : List (List (NRow k))} (h : TrailFam k segs) :
    IsFamily k (toFam segs) where
  chains := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact (h.trails A hA).isModelChain hk (h.classes.sublist (rowsEntries_sublist_flatten hA))
  ne := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    intro e
    exact (h.trails A hA).ne (List.map_eq_nil_iff.mp e)
  classes := by
    rw [toFam_flatten]
    exact h.classes

theorem chainLink_chain_rows {d : ℕ} : ∀ {segs : List (List (NRow k))},
    (∀ A ∈ segs, ∀ r ∈ A, 1 ≤ r.len) → segs.IsChain (RowLink k d) →
    segs.IsChain (fun A B => ChainLink k d (A.map NRow.entries) (B.map NRow.entries))
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | A :: B :: rest, ht, hl => by
      rw [List.isChain_cons_cons] at hl ⊢
      exact ⟨chainLink_rows (ht A List.mem_cons_self)
        (ht B (List.mem_cons_of_mem _ List.mem_cons_self)) hl.1,
        chainLink_chain_rows (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hl.2⟩

theorem TrailFam.isPath (hk : 2 ≤ k) {segs : List (List (NRow k))} (h : TrailFam k segs)
    (hl : segs.IsChain (RowLink k 4)) : IsPath k (toFam segs) where
  toIsFamily := h.isFamily hk
  links := by
    unfold toFam
    rw [List.isChain_map]
    exact chainLink_chain_rows (fun A hA => (h.trails A hA).len) hl

/-! ### The finite statements on rows -/

theorem chain_cap_rows {M : ℕ → ℕ} {G : ℕ} (h0 : ChainCap M G) {A : List (NRow 7)}
    (hA : Trail 7 A) (hcl : (rowsEntries A).Pairwise (NotRot (k := 7)))
    (hG : rowsHoles 7 A ≤ G) : A.length ≤ M (rowsHoles 7 A) := by
  have h := h0 _ (hA.isModelChain (by norm_num) hcl) (by rw [holesL_rows]; exact hG)
  rwa [List.length_map, holesL_rows] at h

theorem path_cap_rows {s : ℕ} {P : ℕ → ℕ} {G : ℕ} (hs : PathCap s P G)
    {segs : List (List (NRow 7))} (h : TrailFam 7 segs) (hl : segs.IsChain (RowLink 7 4))
    (hn : segs.length = s + 1) (hG : rowsHoles 7 segs.flatten ≤ G) :
    segs.flatten.length ≤ P (rowsHoles 7 segs.flatten) := by
  have h1 := hs _ (h.isPath (by norm_num) hl) (by rw [toFam_length]; exact hn)
    (by rw [famHoles_toFam]; exact hG)
  rwa [famRows_toFam, famHoles_toFam] at h1

theorem ring_cap_rows {PR : ℕ → ℕ} {G : ℕ} (hR : RingCap PR G) {A : List (NRow 7)}
    (hA : Trail 7 A) (hcl : (rowsEntries A).Pairwise (NotRot (k := 7))) (h2 : 2 ≤ A.length)
    (hc : RowLink 7 3 A A) (hG : rowsHoles 7 A ≤ G) : A.length ≤ PR (rowsHoles 7 A) := by
  have hring : IsRing 7 (A.map NRow.entries) :=
    ⟨hA.isModelChain (by norm_num) hcl, by rw [List.length_map]; exact h2,
      chainLink_rows hA.len hA.len hc⟩
  have h := hR _ hring (by rw [holesL_rows]; exact hG)
  rwa [List.length_map, holesL_rows] at h

theorem noProfile_rows {ts : List (ℕ × ℕ)} (hF : NoProfile ts) {segs : List (List (NRow 7))}
    (h : TrailFam 7 segs)
    (ht : List.Forall₂ (fun (A : List (NRow 7)) t => t.1 ≤ A.length ∧ rowsHoles 7 A ≤ t.2)
      segs ts) : False := by
  apply hF
  refine ⟨toFam segs, h.isFamily (by norm_num), ?_⟩
  unfold toFam
  rw [List.forall₂_map_left_iff]
  refine ht.imp ?_
  intro A t hAt
  rw [List.length_map, holesL_rows]
  exact hAt

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.chain_cap_rows
#print axioms SuperpermLowerBounds.path_cap_rows
#print axioms SuperpermLowerBounds.ring_cap_rows
#print axioms SuperpermLowerBounds.noProfile_rows

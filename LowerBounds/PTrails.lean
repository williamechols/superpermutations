import LowerBounds.PGeom
import LowerBounds.NUpper

/-!
# Trails of a list of rows, and the accounting (the written proof, sections 3 and 4)

* `cutRows R`: the list of rows `R` cut at its seams of weight other than 3; `cutRows_spec`:
  the pieces are trails, there are at most `rX R + 1` of them (`rX` = the seam excess
  `Σ (w - 3)`), and if there are exactly `rX R + 1` then consecutive pieces are joined at overlap
  weight 4.
* `entries_length_ge`: a valid configuration on 7 symbols has at least 720 blocks.
* `valR`, `wtR`: value `rows - holes - 5 x` and weight `holes + 6 x` of a list of rows with link
  cost `x`; `acc_value`, `acc_weight` (Lemma ACC): for a valid configuration of cost at most
  134 the values add up to at least 50 and the weights to at most 84.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### Cutting at the heavy seams -/

/-- The seam excess `Σ (w - 3)` of a list of rows. -/
noncomputable def rX (R : List (NRow k)) : ℕ := ((seamWeights R).map (fun w => w - 3)).sum

theorem rowsCost_eq (R : List (NRow k)) : rowsCost R = R.length + rX R := rfl

theorem rX_cons_cons (r r' : NRow k) (rest : List (NRow k)) :
    rX (r :: r' :: rest) = (ew k r.exit r'.entry - 3) + rX (r' :: rest) := by
  unfold rX
  simp only [seamWeights, List.map_cons, List.sum_cons]

/-- A list of rows cut at its seams of weight other than 3. -/
noncomputable def cutRows : List (NRow k) → List (List (NRow k))
  | [] => []
  | [r] => [[r]]
  | r :: r' :: rest =>
      if ew k r.exit r'.entry = 3 then
        match cutRows (r' :: rest) with
        | [] => [[r]]
        | A :: S => (r :: A) :: S
      else [r] :: cutRows (r' :: rest)

/-- What `cutRows` produces. -/
structure CutInv (R : List (NRow k)) (S : List (List (NRow k))) : Prop where
  flat : S.flatten = R
  ne : ∀ A ∈ S, A ≠ []
  inner : ∀ A ∈ S, A.IsChain (fun r r' => SLink k 3 r.lastEntry r'.entry)
  head : S.head?.bind List.head? = R.head?
  cnt : R ≠ [] → S.length ≤ rX R + 1
  single : S.length = 1 → rX R = 0
  eq4 : rX R + 1 = S.length → S.IsChain (RowLink k 4)

theorem cutRows_spec : ∀ R : List (NRow k), (∀ w ∈ seamWeights R, 3 ≤ w) →
    CutInv R (cutRows R)
  | [], _ => by
      refine ⟨rfl, ?_, ?_, rfl, fun h => absurd rfl h, ?_, fun _ => List.isChain_nil⟩
      · intro A hA
        simp [cutRows] at hA
      · intro A hA
        simp [cutRows] at hA
      · intro h
        simp [cutRows] at h
  | [r], _ => by
      refine ⟨rfl, ?_, ?_, rfl, fun _ => ?_, fun _ => rfl, fun _ => List.isChain_singleton _⟩
      · intro A hA
        simp only [cutRows, List.mem_singleton] at hA
        rw [hA]
        simp
      · intro A hA
        simp only [cutRows, List.mem_singleton] at hA
        rw [hA]
        exact List.isChain_singleton _
      · simp [cutRows]
  | r :: r' :: rest, hs => by
      have hw : 3 ≤ ew k r.exit r'.entry := hs _ (by simp [seamWeights])
      have hs' : ∀ w ∈ seamWeights (r' :: rest), 3 ≤ w :=
        fun w hw' => hs w (by simp only [seamWeights, List.mem_cons]; exact Or.inr hw')
      have ih := cutRows_spec (r' :: rest) hs'
      obtain ⟨S', hS'⟩ : ∃ S', S' = cutRows (r' :: rest) := ⟨_, rfl⟩
      rw [← hS'] at ih
      obtain ⟨ihF, ihN, ihI, ihH, ihC, ihS, ihE⟩ := ih
      -- the first piece of `S'` starts at `r'`
      rcases S' with _ | ⟨A, S₀⟩
      · simp at ihF
      have hAne : A ≠ [] := ihN A List.mem_cons_self
      have hAh : A.head? = some r' := by
        simpa using ihH
      obtain ⟨A', rfl⟩ : ∃ A', A = r' :: A' := by
        cases A with
        | nil => exact absurd rfl hAne
        | cons a A' =>
            simp only [List.head?_cons, Option.some.injEq] at hAh
            exact ⟨A', by rw [hAh]⟩
      have ihC' := ihC (List.cons_ne_nil _ _)
      have hX := rX_cons_cons r r' rest
      by_cases h3 : ew k r.exit r'.entry = 3
      · -- the row joins the first piece
        have hc : cutRows (r :: r' :: rest) = (r :: r' :: A') :: S₀ := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_pos h3, ← hS']
        rw [hc]
        have hXe : rX (r :: r' :: rest) = rX (r' :: rest) := by
          rw [hX, h3]
          omega
        refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · rw [List.flatten_cons, List.cons_append, List.cons_append, ← List.cons_append,
            ← List.flatten_cons, ihF]
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB
          · simp
          · exact ihN B (List.mem_cons_of_mem _ hB)
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB
          · rw [List.isChain_cons_cons]
            exact ⟨sLink_three_of_ew h3, ihI _ List.mem_cons_self⟩
          · exact ihI B (List.mem_cons_of_mem _ hB)
        · intro _
          rw [hXe]
          exact ihC'
        · intro h1
          rw [hXe]
          exact ihS h1
        · intro h1
          rw [hXe] at h1
          have hch := ihE h1
          rw [List.isChain_cons] at hch ⊢
          refine ⟨fun B hB => ?_, hch.2⟩
          exact (hch.1 B hB).append_left (List.cons_ne_nil _ _) [r]
      · -- the row is a piece of its own
        have hc : cutRows (r :: r' :: rest) = [r] :: (r' :: A') :: S₀ := by
          show (if ew k r.exit r'.entry = 3 then
              (match cutRows (r' :: rest) with
              | [] => [[r]]
              | A :: S => (r :: A) :: S)
            else [r] :: cutRows (r' :: rest)) = _
          rw [if_neg h3, ← hS']
        rw [hc]
        refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · rw [List.flatten_cons, ihF]
          rfl
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB
          · simp
          · exact ihN B hB
        · intro B hB
          rcases List.mem_cons.mp hB with rfl | hB
          · exact List.isChain_singleton _
          · exact ihI B hB
        · intro _
          rw [hX]
          simp only [List.length_cons] at ihC' ⊢
          omega
        · intro h1
          simp at h1
        · intro h1
          rw [hX] at h1
          simp only [List.length_cons] at ihC' h1
          have h4 : ew k r.exit r'.entry = 4 := by omega
          have h1' : rX (r' :: rest) + 1 = ((r' :: A') :: S₀).length := by
            simp only [List.length_cons]
            omega
          rw [List.isChain_cons_cons]
          refine ⟨?_, ihE h1'⟩
          rw [rowLink_iff]
          intro a ha b hb
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ha
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst ha
          subst hb
          exact sLink_of_ew (x := sigmaInv r.lastEntry) rfl (by omega) h4

/-- The pieces of a list of rows with pairwise different classes form a family of trails. -/
theorem cutRows_trailFam {R : List (NRow k)} (hs : ∀ w ∈ seamWeights R, 3 ≤ w)
    (hlen : ∀ r ∈ R, 1 ≤ r.len) (hcl : (rowsEntries R).Pairwise (NotRot (k := k))) :
    TrailFam k (cutRows R) := by
  have inv := cutRows_spec R hs
  refine ⟨fun A hA => ⟨inv.ne A hA, fun r hr => hlen r ?_, inv.inner A hA⟩, ?_⟩
  · rw [← inv.flat]
    exact List.mem_flatten.mpr ⟨A, hA, hr⟩
  · rw [inv.flat]
    exact hcl

/-! ### The number of blocks -/

/-- A valid configuration on 7 symbols has at least 720 blocks. -/
theorem entries_length_ge {c : NConfig 7} (hv : c.Valid) : 720 ≤ c.entries.length := by
  have hall : ∀ v : Vtx 7, v ∈ lineWalk c.entries :=
    fun v => (mem_lineWalk (by norm_num)).mpr (hv.cover v)
  have h1 : Fintype.card (Vtx 7) ≤ (lineWalk c.entries).length := by
    calc Fintype.card (Vtx 7) = (Finset.univ : Finset (Vtx 7)).card := Finset.card_univ.symm
      _ ≤ (lineWalk c.entries).toFinset.card :=
          Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ ≤ (lineWalk c.entries).length := List.toFinset_card_le _
  rw [Hunter.ProofsRecursion.card_Vtx, length_lineWalk] at h1
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

/-! ### Value and weight -/

/-- The value `rows - holes - 5 x` of a list of rows with link cost `x`. -/
def valR (R : List (NRow 7)) (x : ℕ) : ℤ := (R.length : ℤ) - (rowsHoles 7 R : ℤ) - 5 * (x : ℤ)

/-- The weight `holes + 6 x` of a list of rows with link cost `x`. -/
def wtR (R : List (NRow 7)) (x : ℕ) : ℕ := rowsHoles 7 R + 6 * x

/-- The cost of the attachment of a hanging component. -/
noncomputable def NHanging.att (H : NHanging k) : ℕ := H.w0 + H.w1 - 4

theorem NHanging.cost_eq (H : NHanging k) : H.cost = H.rows.length + rX H.rows + H.att := rfl

/-- The value of a hanging component. -/
noncomputable def vH (H : NHanging 7) : ℤ := valR H.rows (rX H.rows + H.att)

/-- The weight of a hanging component. -/
noncomputable def wH (H : NHanging 7) : ℕ := wtR H.rows (rX H.rows + H.att)

theorem valR_eq {R : List (NRow 7)} (hl : ∀ r ∈ R, r.len ≤ 6) (x : ℕ) :
    valR R x = ((rowsEntries R).length : ℤ) - 5 * ((R.length + x : ℕ) : ℤ) := by
  have h := rowsEntries_length_add_holes (k := 7) hl
  unfold valR
  push_cast
  have h' : ((rowsEntries R).length : ℤ) + (rowsHoles 7 R : ℤ) = 6 * (R.length : ℤ) := by
    exact_mod_cast h
  linarith

theorem wtR_eq {R : List (NRow 7)} (hl : ∀ r ∈ R, r.len ≤ 6) (x : ℕ) :
    (wtR R x : ℤ) = 6 * ((R.length + x : ℕ) : ℤ) - ((rowsEntries R).length : ℤ) := by
  have h := rowsEntries_length_add_holes (k := 7) hl
  unfold wtR
  push_cast
  have h' : ((rowsEntries R).length : ℤ) + (rowsHoles 7 R : ℤ) = 6 * (R.length : ℤ) := by
    exact_mod_cast h
  linarith

theorem sum_vH : ∀ Hs : List (NHanging 7), (∀ H ∈ Hs, ∀ r ∈ H.rows, r.len ≤ 6) →
    (Hs.map vH).sum = (((Hs.flatMap fun H => rowsEntries H.rows).length : ℕ) : ℤ) -
      5 * (((Hs.map NHanging.cost).sum : ℕ) : ℤ)
  | [], _ => by simp
  | H :: Hs, h => by
      have ih := sum_vH Hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
      have h1 := valR_eq (h H List.mem_cons_self) (rX H.rows + H.att)
      rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, ih]
      unfold vH
      rw [h1, NHanging.cost_eq]
      push_cast
      ring

theorem sum_wH : ∀ Hs : List (NHanging 7), (∀ H ∈ Hs, ∀ r ∈ H.rows, r.len ≤ 6) →
    (((Hs.map wH).sum : ℕ) : ℤ) = 6 * (((Hs.map NHanging.cost).sum : ℕ) : ℤ) -
      (((Hs.flatMap fun H => rowsEntries H.rows).length : ℕ) : ℤ)
  | [], _ => by simp
  | H :: Hs, h => by
      have ih := sum_wH Hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
      have h1 := wtR_eq (h H List.mem_cons_self) (rX H.rows + H.att)
      rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons, Nat.cast_add, Nat.cast_add, Nat.cast_add, ih]
      unfold wH
      rw [h1, NHanging.cost_eq]
      simp only [Nat.cast_add]
      ring

/-- **Lemma ACC, values.** -/
theorem acc_value {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 134) :
    50 ≤ valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  rw [valR_eq hlen.1, sum_vH c.hanging hlen.2]
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 134 := by
    exact_mod_cast (hC ▸ hc)
  linarith

/-- **Lemma ACC, weights.** -/
theorem acc_weight {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 134) :
    wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum ≤ 84 := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  have h0 := wtR_eq hlen.1 (rX c.kernel)
  have h3 := sum_wH c.hanging hlen.2
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 134 := by
    exact_mod_cast (hC ▸ hc)
  have : ((wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum : ℕ) : ℤ) ≤ 84 := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast this

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.cutRows_spec
#print axioms SuperpermLowerBounds.entries_length_ge
#print axioms SuperpermLowerBounds.acc_value
#print axioms SuperpermLowerBounds.acc_weight

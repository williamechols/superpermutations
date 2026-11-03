import LowerBounds.NConfig

/-!
# Rules that hold in every standard configuration (the written model, sections 4 and 5)

Consequences of `NConfig.Valid`; no Hamiltonian path occurs.

* `Valid.len_le`: a row has at most `k - 1` blocks (`τ₂` has period `k - 1`, `tau2V_period`).
* `Valid.slot_not_own` (part of A2, A3): the vertex `v_H` of a hanging component lies in no
  block of that component.  More generally the forest condition is `Valid.forest` itself.
* `Valid.w0_two`: if the first edge of the attachment has weight 2, then `σ v_H = τ₂ g` for the
  last entry `g` of the component, and `τ₂ g` is not a block entry (**A1, the marker rule**: the
  class after the last row, in its 2-cycle, is entered with another marker).
* `Valid.w1_two`: if the second edge has weight 2, the first entry is `τ v_H`.
* `Valid.free_attachment`: a free attachment (`w₀ = w₁ = 2`): `v_H = σ⁻¹ τ₂ g`, the component
  starts at `τ₂² g`, and `τ₂ g` is not a block entry.
* `Valid.attachment_cost_one` (**A3 for cost 1**): an attachment of cost 1 has weights `(2, 3)`
  or `(3, 2)`; in the first case `v_H = σ⁻¹ τ₂ g`, the class of `τ₂ g` is outside the component
  and the first entry is a successor of weight 3 of `v_H`; in the second case the first entry
  is `τ v_H = τ₂ (σ v_H)`, the class of `σ v_H` is outside the component and `σ v_H` is a
  successor of weight 3 of the last exit.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### `τ₂` has period `k - 1` -/

theorem tau2V_iterate_val (hk : 2 ≤ k) (v : Vtx k) (base : List ℕ) (m : ℕ)
    (hv : (v : List ℕ) = base ++ [m]) (i : ℕ) :
    ((tau2V^[i] v : Vtx k) : List ℕ) = base.rotate i ++ [m] := by
  have hlen : base.length = k - 1 := by
    have h := v.2.length
    rw [hv] at h
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  induction i with
  | zero => simpa using hv
  | succ i ih =>
      rw [Function.iterate_succ_apply', tau2V_val hk, ih]
      exact Hunter.ProofsRigidity2.tau2_step hk hlen m i

theorem tau2V_period (hk : 2 ≤ k) (v : Vtx k) : tau2V^[k - 1] v = v := by
  have hne : (v : List ℕ) ≠ [] := by
    intro h
    have hl := v.2.length
    rw [h] at hl
    simp at hl
    omega
  have hv : (v : List ℕ) = (v : List ℕ).dropLast ++ [(v : List ℕ).getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hlen : (v : List ℕ).dropLast.length = k - 1 := by
    rw [List.length_dropLast, v.2.length]
  apply Subtype.ext
  rw [tau2V_iterate_val hk v _ _ hv (k - 1)]
  conv_rhs => rw [hv]
  rw [← hlen, List.rotate_length]

/-- Different blocks: not the same rotation class. -/
def IdxRel (e : Vtx k) (i j : ℕ) : Prop :=
  ¬ (((tau2V^[i] e : Vtx k) : List ℕ) ~r ((tau2V^[j] e : Vtx k) : List ℕ))

instance (e : Vtx k) : Std.Symm (IdxRel e) := ⟨fun _ _ h hr => h hr.symm⟩

/-- A row whose blocks are pairwise different classes has at most `k - 1` blocks. -/
theorem NRow.len_le_of_pairwise (hk : 2 ≤ k) (r : NRow k)
    (h : r.entries.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))) :
    r.len ≤ k - 1 := by
  by_contra hlt
  unfold NRow.entries at h
  rw [List.pairwise_map] at h
  have h' : (List.range r.len).Pairwise (IdxRel r.entry) := h
  have h0 := h'.forall (a := 0) (List.mem_range.mpr (by omega)) (b := k - 1)
    (List.mem_range.mpr (by omega)) (by omega)
  apply h0
  show ((tau2V^[0] r.entry : Vtx k) : List ℕ) ~r ((tau2V^[k - 1] r.entry : Vtx k) : List ℕ)
  rw [tau2V_period hk]
  exact List.IsRotated.refl _

/-! ### Blocks of a valid configuration -/

/-- The last block entry of a row. -/
noncomputable def NRow.lastEntry (r : NRow k) : Vtx k := tau2V^[r.len - 1] r.entry

theorem NRow.exit_eq (r : NRow k) : r.exit = sigmaInv r.lastEntry := rfl

theorem NRow.entry_mem (r : NRow k) (h : 1 ≤ r.len) : r.entry ∈ r.entries :=
  List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩

theorem NRow.lastEntry_mem (r : NRow k) (h : 1 ≤ r.len) : r.lastEntry ∈ r.entries :=
  List.mem_map.mpr ⟨r.len - 1, List.mem_range.mpr (by omega), rfl⟩

theorem rowsEntries_ne_nil {rows : List (NRow k)} (hne : rows ≠ [])
    (hlen : ∀ r ∈ rows, 1 ≤ r.len) : rowsEntries rows ≠ [] := by
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hmem := NRow.entry_mem r (hlen r List.mem_cons_self)
  intro h
  have h1 : r.entry ∈ rowsEntries (r :: rs) :=
    List.mem_flatMap.mpr ⟨r, List.mem_cons_self, hmem⟩
  rw [h] at h1
  simp at h1

/-- Two hanging components have no rotation class in common. -/
def DisjointRows (A B : NHanging k) : Prop :=
  ∀ x ∈ rowsEntries A.rows, ∀ y ∈ rowsEntries B.rows, ¬ ((x : List ℕ) ~r (y : List ℕ))

instance : Std.Symm (DisjointRows (k := k)) :=
  ⟨fun _ _ h x hx y hy hr => h y hy x hx hr.symm⟩

namespace NConfig

variable {c : NConfig k}

theorem Valid.kernel_hanging_disjoint (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging) :
    ∀ a ∈ rowsEntries c.kernel, ∀ b ∈ rowsEntries H.rows,
      ¬ ((a : List ℕ) ~r (b : List ℕ)) := by
  have h := hv.distinct
  unfold NConfig.entries at h
  rw [List.pairwise_append] at h
  intro a ha b hb
  exact h.2.2 a ha b (List.mem_flatMap.mpr ⟨H, hH, hb⟩)

theorem Valid.hanging_disjoint (hv : c.Valid) {H H' : NHanging k} (hH : H ∈ c.hanging)
    (hH' : H' ∈ c.hanging) (hne : H ≠ H') : DisjointRows H H' := by
  have h := hv.distinct
  unfold NConfig.entries at h
  rw [List.pairwise_append, List.pairwise_flatMap] at h
  have hp : c.hanging.Pairwise DisjointRows := h.2.1.2
  exact hp.forall hH hH' hne

/-- Hanging components with the same rows are the same component. -/
theorem Valid.eq_of_rows_eq (hv : c.Valid) {H H' : NHanging k} (hH : H ∈ c.hanging)
    (hH' : H' ∈ c.hanging) (h : H.rows = H'.rows) : H = H' := by
  by_contra hne
  have hd := hv.hanging_disjoint hH hH' hne
  have hne' := rowsEntries_ne_nil (hv.hanging_ne H hH) (hv.hanging_len H hH)
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hne'
  have hmem : e ∈ rowsEntries H.rows := by
    rw [he]
    exact List.mem_cons_self
  have hmem' : e ∈ rowsEntries H'.rows := by
    rw [← h]
    exact hmem
  exact hd e hmem e hmem' (List.IsRotated.refl _)

/-- **Every row has at most `k - 1` blocks.** -/
theorem Valid.len_le (hk : 2 ≤ k) (hv : c.Valid) :
    (∀ r ∈ c.kernel, r.len ≤ k - 1) ∧ ∀ H ∈ c.hanging, ∀ r ∈ H.rows, r.len ≤ k - 1 := by
  have h := hv.distinct
  unfold NConfig.entries at h
  rw [List.pairwise_append] at h
  constructor
  · intro r hr
    have h1 := h.1
    unfold rowsEntries at h1
    rw [List.pairwise_flatMap] at h1
    exact NRow.len_le_of_pairwise hk r (h1.1 r hr)
  · intro H hH r hr
    have h1 := h.2.1
    rw [List.pairwise_flatMap] at h1
    have h2 := h1.1 H hH
    unfold rowsEntries at h2
    rw [List.pairwise_flatMap] at h2
    exact NRow.len_le_of_pairwise hk r (h2.1 r hr)

/-- **The vertex of a hanging component lies in no block of that component** (the component
does not hang on itself; from the forest condition). -/
theorem Valid.slot_not_own (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging) :
    ∀ e ∈ rowsEntries H.rows, ¬ (((H.slot : Vtx k) : List ℕ) ~r (e : List ℕ)) := by
  intro e₀ he₀ hrot₀
  have key : ∀ R : List (NRow k), Relation.TransGen c.HangsOn R c.kernel → R ≠ H.rows := by
    intro R hR
    refine Relation.TransGen.head_induction_on (motive := fun R _ => R ≠ H.rows) hR ?_ ?_
    · intro R h hRH
      obtain ⟨H', hH', hrows, e', he', hrot'⟩ := h
      have hEq : H' = H := hv.eq_of_rows_eq hH' hH (hrows.trans hRH)
      rw [hEq] at hrot'
      exact hv.kernel_hanging_disjoint hH e' he' e₀ he₀ (hrot'.symm.trans hrot₀)
    · intro R R' h' h ih hRH
      obtain ⟨H', hH', hrows, e', he', hrot'⟩ := h'
      have hEq : H' = H := hv.eq_of_rows_eq hH' hH (hrows.trans hRH)
      rw [hEq] at hrot'
      obtain ⟨_, ⟨H'', hH'', hrows'', _⟩, _⟩ := Relation.TransGen.head'_iff.mp h
      apply ih
      by_cases hE : H'' = H
      · rw [← hrows'', hE]
      · exfalso
        rw [← hrows''] at he'
        exact hv.hanging_disjoint hH'' hH hE e' he' e₀ he₀ (hrot'.symm.trans hrot₀)
  exact key H.rows (hv.forest H hH) rfl

/-! ### Attachments -/

/-- **A1, the marker rule.**  If the first edge of the attachment of `H` has weight 2, then
`σ v_H = τ₂ g` for the last block entry `g` of `H`, and `τ₂ g` is not a block entry of the
configuration. -/
theorem Valid.w0_two (hk : 2 ≤ k) (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging)
    {r : NRow k} (hr : H.rows.getLast? = some r) (h0 : H.w0 = 2) :
    sigma H.slot = tau2V r.lastEntry ∧ tau2V r.lastEntry ∉ c.entries := by
  have hw0 : H.w0 = ew k r.exit (sigma H.slot) := by
    simp only [NHanging.w0, hr]
  have hw : ew k (sigmaInv r.lastEntry) (sigma H.slot) = 2 := by
    rw [← NRow.exit_eq, ← hw0]
    exact h0
  have hrmem : r ∈ H.rows := by
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hr
    rw [hys]
    simp
  have hlen := hv.hanging_len H hH r hrmem
  have hlast : r.lastEntry ∈ rowsEntries H.rows :=
    List.mem_flatMap.mpr ⟨r, hrmem, NRow.lastEntry_mem r hlen⟩
  have hsig : sigma H.slot = tau2V r.lastEntry := by
    rcases weight_two_successors hk hw with hs | ht
    · exfalso
      have h1 : sigma H.slot = sigma r.lastEntry := by
        rw [hs]
        show sigma (sigma (sigmaInv r.lastEntry)) = _
        rw [Hunter.ProofsStructure.sigma_sigmaInv]
      have h2 : H.slot = r.lastEntry := Hunter.ProofsSpine.sigma_inj h1
      apply hv.slot_not_own hH _ hlast
      rw [h2]
    · exact ht
  refine ⟨hsig, ?_⟩
  rw [← hsig]
  exact hv.slot H hH

/-- If the second edge of the attachment of `H` has weight 2, the first entry of `H` is
`τ v_H`, that is `τ₂ (σ v_H)`. -/
theorem Valid.w1_two (hk : 2 ≤ k) (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging)
    {r : NRow k} (hr : H.rows.head? = some r) (h1 : H.w1 = 2) : r.entry = tau H.slot := by
  have hw1 : H.w1 = ew k H.slot r.entry := by
    simp only [NHanging.w1, hr]
  have hw : ew k H.slot r.entry = 2 := by
    rw [← hw1]
    exact h1
  have hrmem : r ∈ H.rows := by
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hr
    rw [hys]
    exact List.mem_cons_self
  have hlen := hv.hanging_len H hH r hrmem
  have hfirst : r.entry ∈ rowsEntries H.rows :=
    List.mem_flatMap.mpr ⟨r, hrmem, NRow.entry_mem r hlen⟩
  rcases weight_two_successors hk hw with hs | ht
  · exfalso
    apply hv.slot_not_own hH _ hfirst
    rw [hs]
    refine ⟨2, ?_⟩
    show ((H.slot : Vtx k) : List ℕ).rotate 2 = (((H.slot : Vtx k) : List ℕ).rotate 1).rotate 1
    rw [List.rotate_rotate]
  · exact ht

/-- **A free attachment** (`w₀ = w₁ = 2`): `v_H = σ⁻¹ τ₂ g`, the component starts at `τ₂² g`
(two places after its own end in the 2-cycle of its last row), and the skipped class is not
entered at `τ₂ g`. -/
theorem Valid.free_attachment (hk : 2 ≤ k) (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging)
    {r r' : NRow k} (hr : H.rows.getLast? = some r) (hr' : H.rows.head? = some r')
    (h0 : H.w0 = 2) (h1 : H.w1 = 2) :
    H.slot = sigmaInv (tau2V r.lastEntry) ∧ r'.entry = tau2V (tau2V r.lastEntry) ∧
      tau2V r.lastEntry ∉ c.entries := by
  obtain ⟨hs, hno⟩ := hv.w0_two hk hH hr h0
  have ht := hv.w1_two hk hH hr' h1
  have hslot : H.slot = sigmaInv (tau2V r.lastEntry) := by
    rw [← hs, sigmaInv_sigma (by omega)]
  refine ⟨hslot, ?_, hno⟩
  rw [ht, hslot]
  rfl

/-- **A3 for an attachment of cost 1.**  The weights are `(2, 3)` or `(3, 2)`.

`(2, 3)`: `σ v_H = τ₂ g` for the last entry `g`; `τ₂ g` is not a block entry; the first entry
is a successor of weight 3 of `v_H`.

`(3, 2)`: the first entry is `τ v_H`; `σ v_H` is a successor of weight 3 of the last exit.

In both cases `v_H` lies in no block of `H` (`Valid.slot_not_own`) and `σ v_H` is not a block
entry (`Valid.slot`). -/
theorem Valid.attachment_cost_one (hk : 2 ≤ k) (hv : c.Valid) {H : NHanging k}
    (hH : H ∈ c.hanging) {r r' : NRow k} (hr : H.rows.getLast? = some r)
    (hr' : H.rows.head? = some r') (h : H.w0 + H.w1 - 4 = 1) :
    (sigma H.slot = tau2V r.lastEntry ∧ tau2V r.lastEntry ∉ c.entries ∧
        ew k H.slot r'.entry = 3) ∨
      (r'.entry = tau H.slot ∧ ew k (sigmaInv r.lastEntry) (sigma H.slot) = 3) := by
  have hw0 : H.w0 = ew k r.exit (sigma H.slot) := by
    simp only [NHanging.w0, hr]
  have hw1 : H.w1 = ew k H.slot r'.entry := by
    simp only [NHanging.w1, hr']
  have g0 := hv.w0_ge H hH
  have g1 := hv.w1_ge H hH
  by_cases h2 : H.w0 = 2
  · left
    obtain ⟨hs, hno⟩ := hv.w0_two hk hH hr h2
    refine ⟨hs, hno, ?_⟩
    rw [← hw1]
    omega
  · right
    have h3 : H.w1 = 2 := by omega
    refine ⟨hv.w1_two hk hH hr' h3, ?_⟩
    rw [← NRow.exit_eq, ← hw0]
    omega

end NConfig

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.tau2V_period
#print axioms SuperpermLowerBounds.NConfig.Valid.len_le
#print axioms SuperpermLowerBounds.NConfig.Valid.slot_not_own
#print axioms SuperpermLowerBounds.NConfig.Valid.w0_two
#print axioms SuperpermLowerBounds.NConfig.Valid.free_attachment
#print axioms SuperpermLowerBounds.NConfig.Valid.attachment_cost_one

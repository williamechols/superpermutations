import LowerBounds.NT4

/-!
# Lemma T4 of the written model as a statement about standard configurations

`NConfig.Valid.exists_noT4` (`k ≥ 3`): every valid standard configuration can be changed into a
valid standard configuration without seams of type T4 whose cost is not larger.  This is the
lemma as the paper states it; no Hamiltonian path occurs.

The proof passes through block configurations: `NConfig.toB` writes a standard configuration as
a block configuration (the rows are expanded into their blocks, and the rank of a hanging
component is its distance to the kernel in the forest), `Valid.toB_valid` and `Valid.toB_cost`
say that nothing is lost, and `exists_valid_noT4` (`NT4.lean`) does the surgery.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

/-! ### The blocks of rows -/

/-- Inside a row all links are doors. -/
theorem lsum_entries (hk : 2 ≤ k) : ∀ (n : ℕ) (e : Vtx k),
    lsum (costLink k) (NRow.entries ⟨e, n⟩) = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, e => by
      have ih := lsum_entries hk (n + 1) (tau2V e)
      rw [NRow.entries_succ] at ih
      rw [NRow.entries_succ, NRow.entries_succ]
      show costLink k e (tau2V e) +
        lsum (costLink k) (tau2V e :: NRow.entries ⟨tau2V (tau2V e), n⟩) = 0
      rw [costLink_door hk, ih]

theorem entries_head? (r : NRow k) (h : 1 ≤ r.len) : r.entries.head? = some r.entry := by
  obtain ⟨e, n⟩ := r
  have h' : 1 ≤ n := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [NRow.entries_succ]
  rfl

theorem entries_getLast? (r : NRow k) (h : 1 ≤ r.len) : r.entries.getLast? = some r.lastEntry := by
  unfold NRow.entries NRow.lastEntry
  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
  rfl

theorem entries_ne_nil (r : NRow k) (h : 1 ≤ r.len) : r.entries ≠ [] := by
  intro h0
  have h1 := entries_head? r h
  rw [h0] at h1
  simp at h1

theorem rowsEntries_head? {r : NRow k} {rest : List (NRow k)} (h : 1 ≤ r.len) :
    (rowsEntries (r :: rest)).head? = some r.entry := by
  unfold rowsEntries
  rw [List.flatMap_cons, List.head?_append, entries_head? r h]
  rfl

theorem rowsEntries_getLast? {rows : List (NRow k)} {r : NRow k} (hr : rows.getLast? = some r)
    (h : 1 ≤ r.len) : (rowsEntries rows).getLast? = some r.lastEntry := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hr
  rw [hys]
  unfold rowsEntries
  rw [List.flatMap_append, List.flatMap_singleton, getLast?_append_of_ne_nil (entries_ne_nil r h),
    entries_getLast? r h]

/-- The cost of the line of blocks of a sequence of rows is rows plus seam excess. -/
theorem lineCost_rowsEntries (hk : 2 ≤ k) : ∀ rows : List (NRow k), rows ≠ [] →
    (∀ r ∈ rows, 1 ≤ r.len) → (∀ w ∈ seamWeights rows, 3 ≤ w) →
    lineCost (rowsEntries rows) = rowsCost rows
  | [], h, _, _ => absurd rfl h
  | [r], _, _, _ => by
      have e0 : rowsEntries [r] = r.entries := by
        unfold rowsEntries
        rw [List.flatMap_singleton]
      have e2 : lsum (costLink k) r.entries = 0 := by
        obtain ⟨e, n⟩ := r
        exact lsum_entries hk n e
      unfold lineCost
      rw [linkSum_eq_lsum, e0, e2]
      rfl
  | r :: r' :: rest, _, hlen, hs => by
      have ih := lineCost_rowsEntries hk (r' :: rest) (List.cons_ne_nil _ _)
        (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
        (fun w hw => hs w (by
          simp only [seamWeights, List.mem_cons]
          exact Or.inr hw))
      have hr := hlen r List.mem_cons_self
      have hr' := hlen r' (List.mem_cons_of_mem _ List.mem_cons_self)
      have hw : 3 ≤ ew k r.exit r'.entry := hs _ (by
        rw [seamWeights]
        exact List.mem_cons_self)
      have e1 : rowsEntries (r :: r' :: rest) = r.entries ++ rowsEntries (r' :: rest) := by
        unfold rowsEntries
        rw [List.flatMap_cons]
      have e2 : lsum (costLink k) r.entries = 0 := by
        obtain ⟨e, n⟩ := r
        exact lsum_entries hk n e
      have e3 : costLink k r.lastEntry r'.entry = ew k r.exit r'.entry - 2 := rfl
      have e4 : rowsCost (r :: r' :: rest) =
          rowsCost (r' :: rest) + 1 + (ew k r.exit r'.entry - 3) := by
        unfold rowsCost
        simp only [seamWeights, List.length_cons, List.map_cons, List.sum_cons]
        omega
      unfold lineCost at ih ⊢
      rw [linkSum_eq_lsum] at ih ⊢
      rw [e1, lsum_append (costLink k) _ _ r.lastEntry r'.entry (entries_getLast? r hr)
        (rowsEntries_head? hr'), e2, e3, e4]
      omega

/-! ### The forest with ranks -/

/-- The kernel is reached from the sequence of rows `R` in exactly `n` steps of `HangsOn`. -/
def Reach (c : NConfig k) : ℕ → List (NRow k) → Prop
  | 0, R => R = c.kernel
  | n + 1, R => ∃ R', c.HangsOn R R' ∧ Reach c n R'

theorem exists_reach (c : NConfig k) {R : List (NRow k)}
    (h : Relation.TransGen c.HangsOn R c.kernel) : ∃ n, Reach c (n + 1) R := by
  refine Relation.TransGen.head_induction_on (motive := fun R _ => ∃ n, Reach c (n + 1) R) h ?_ ?_
  · intro R h
    exact ⟨0, c.kernel, h, rfl⟩
  · intro R R' h' _ ih
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, R', h', hn⟩

/-- The distance of a component to the kernel. -/
noncomputable def depth (c : NConfig k) (R : List (NRow k)) : ℕ := sInf {n | Reach c n R}

/-- A standard configuration as a block configuration. -/
noncomputable def NConfig.toB (c : NConfig k) : List (BComp k) :=
  ⟨rowsEntries c.kernel, none, 0⟩ ::
    c.hanging.map (fun H => ⟨rowsEntries H.rows, some H.slot, depth c H.rows⟩)

namespace NConfig

variable {c : NConfig k}

theorem Valid.depth_spec (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging) :
    Reach c (depth c H.rows) H.rows ∧ 1 ≤ depth c H.rows := by
  obtain ⟨n, hn⟩ := exists_reach c (hv.forest H hH)
  have hmem : depth c H.rows ∈ {n | Reach c n H.rows} := Nat.sInf_mem ⟨n + 1, hn⟩
  refine ⟨hmem, ?_⟩
  by_contra hlt
  have h0 : depth c H.rows = 0 := by omega
  have hr : Reach c (depth c H.rows) H.rows := hmem
  rw [h0] at hr
  have hk : H.rows = c.kernel := hr
  have hne := rowsEntries_ne_nil (hv.hanging_ne H hH) (hv.hanging_len H hH)
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hne
  have hmemH : e ∈ rowsEntries H.rows := by
    rw [he]
    exact List.mem_cons_self
  have hmemK : e ∈ rowsEntries c.kernel := by
    rw [← hk]
    exact hmemH
  exact hv.kernel_hanging_disjoint hH e hmemK e hmemH (List.IsRotated.refl _)

/-- The component that contains the vertex of `H` is nearer to the kernel. -/
theorem Valid.depth_lt (hv : c.Valid) {H H₂ : NHanging k} (hH : H ∈ c.hanging)
    (hH₂ : H₂ ∈ c.hanging) {e : Vtx k} (he : e ∈ rowsEntries H₂.rows)
    (hrot : ((H.slot : Vtx k) : List ℕ) ~r (e : List ℕ)) :
    depth c H₂.rows < depth c H.rows := by
  obtain ⟨hr, hd1⟩ := hv.depth_spec hH
  obtain ⟨m, hm⟩ : ∃ m, depth c H.rows = m + 1 := ⟨depth c H.rows - 1, by omega⟩
  rw [hm] at hr ⊢
  have hr' : ∃ R', c.HangsOn H.rows R' ∧ Reach c m R' := hr
  obtain ⟨R', ⟨H', hH', hrows, e', he', hrot'⟩, hR'⟩ := hr'
  have hEq : H' = H := hv.eq_of_rows_eq hH' hH hrows
  rw [hEq] at hrot'
  have hee : (e' : List ℕ) ~r (e : List ℕ) := hrot'.symm.trans hrot
  cases m with
  | zero =>
      exfalso
      have hk : R' = c.kernel := hR'
      rw [hk] at he'
      exact hv.kernel_hanging_disjoint hH₂ e' he' e he hee
  | succ m' =>
      have hR'' : ∃ R'', c.HangsOn R' R'' ∧ Reach c m' R'' := hR'
      obtain ⟨_, ⟨H'', hH'', hrows'', _⟩, _⟩ := hR''
      have hE : H'' = H₂ := by
        by_contra hne
        rw [← hrows''] at he'
        exact hv.hanging_disjoint hH'' hH₂ hne e' he' e he hee
      have hreach : Reach c (m' + 1) H₂.rows := by
        rw [← hE, hrows'']
        exact hR'
      have hle : depth c H₂.rows ≤ m' + 1 := Nat.sInf_le hreach
      omega

theorem mem_toB {C : BComp k} :
    C ∈ c.toB ↔ C = ⟨rowsEntries c.kernel, none, 0⟩ ∨
      ∃ H ∈ c.hanging, C = ⟨rowsEntries H.rows, some H.slot, depth c H.rows⟩ := by
  unfold NConfig.toB
  rw [List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨H, hH, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, hH, h.symm⟩
  · rintro (h | ⟨H, hH, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, hH, h.symm⟩

/-- **A valid standard configuration is a valid block configuration.** -/
theorem Valid.toB_valid (hv : c.Valid) : BValid c.toB := by
  have hdist := hv.distinct
  unfold NConfig.entries at hdist
  rw [List.pairwise_append, List.pairwise_flatMap] at hdist
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases mem_toB.mp hC with rfl | ⟨H, hH, rfl⟩
    · exact rowsEntries_ne_nil hv.kernel_ne hv.kernel_len
    · exact rowsEntries_ne_nil (hv.hanging_ne H hH) (hv.hanging_len H hH)
  · refine ⟨_, _, rfl, rfl, ?_⟩
    intro H' hH'
    obtain ⟨H, _, rfl⟩ := List.mem_map.mp hH'
    exact Option.some_ne_none _
  · intro C hC
    rcases mem_toB.mp hC with rfl | ⟨H, hH, rfl⟩
    · exact hdist.1
    · exact hdist.2.1.1 H hH
  · unfold NConfig.toB
    rw [List.pairwise_cons, List.pairwise_map]
    refine ⟨?_, hdist.2.1.2⟩
    intro C hC
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hC
    exact hv.kernel_hanging_disjoint hH
  · intro v
    obtain ⟨e, he, hrot⟩ := hv.cover v
    unfold NConfig.entries at he
    rcases List.mem_append.mp he with h | h
    · exact ⟨_, mem_toB.mpr (Or.inl rfl), e, h, hrot⟩
    · obtain ⟨H, hH, heH⟩ := List.mem_flatMap.mp h
      exact ⟨_, mem_toB.mpr (Or.inr ⟨H, hH, rfl⟩), e, heH, hrot⟩
  · intro C hC v hslot D hD hmem
    rcases mem_toB.mp hC with rfl | ⟨H, hH, rfl⟩
    · exact absurd hslot (by simp)
    · have hvs : H.slot = v := Option.some.inj hslot
      rw [← hvs] at hmem
      apply hv.slot H hH
      unfold NConfig.entries
      rcases mem_toB.mp hD with rfl | ⟨H₂, hH₂, rfl⟩
      · exact List.mem_append.mpr (Or.inl hmem)
      · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨H₂, hH₂, hmem⟩))
  · intro C hC D hD v h1 h2
    rcases mem_toB.mp hC with rfl | ⟨H, hH, rfl⟩
    · exact absurd h1 (by simp)
    · rcases mem_toB.mp hD with rfl | ⟨H₂, hH₂, rfl⟩
      · exact absurd h2 (by simp)
      · have e1 : H.slot = v := Option.some.inj h1
        have e2 : H₂.slot = v := Option.some.inj h2
        have hHH : H = H₂ :=
          List.inj_on_of_nodup_map hv.slots_nodup hH hH₂ (e1.trans e2.symm)
        rw [hHH]
  · intro C hC v hslot D hD hex
    obtain ⟨e, he, hrot⟩ := hex
    rcases mem_toB.mp hC with rfl | ⟨H, hH, rfl⟩
    · exact absurd hslot (by simp)
    · have hvs : H.slot = v := Option.some.inj hslot
      rw [← hvs] at hrot
      rcases mem_toB.mp hD with rfl | ⟨H₂, hH₂, rfl⟩
      · exact (hv.depth_spec hH).2
      · exact hv.depth_lt hH hH₂ he hrot

theorem Valid.comp_cost (hk : 2 ≤ k) (hv : c.Valid) {H : NHanging k} (hH : H ∈ c.hanging)
    (d : ℕ) : BComp.cost ⟨rowsEntries H.rows, some H.slot, d⟩ = H.cost := by
  have hne := hv.hanging_ne H hH
  have hlen := hv.hanging_len H hH
  obtain ⟨r₀, rest, hrows⟩ := List.exists_cons_of_ne_nil hne
  have hlast := List.getLast?_eq_some_getLast hne
  have hr₀ : 1 ≤ r₀.len := hlen r₀ (by rw [hrows]; exact List.mem_cons_self)
  have hrl : 1 ≤ (H.rows.getLast hne).len := hlen _ (List.getLast_mem hne)
  have hhead : (rowsEntries H.rows).head? = some r₀.entry := by
    rw [hrows]
    exact rowsEntries_head? hr₀
  have hgl := rowsEntries_getLast? hlast hrl
  have hw0 : H.w0 = ew k (H.rows.getLast hne).exit (sigma H.slot) := by
    simp only [NHanging.w0, hlast]
  have hw1 : H.w1 = ew k H.slot r₀.entry := by
    simp only [NHanging.w1, hrows, List.head?_cons]
  show lineCost (rowsEntries H.rows) +
      attCost k (some H.slot) (rowsEntries H.rows).getLast? (rowsEntries H.rows).head? =
    rowsCost H.rows + (H.w0 + H.w1 - 4)
  rw [lineCost_rowsEntries hk H.rows hne hlen (hv.hanging_seams H hH), hgl, hhead, hw0, hw1]
  rfl

/-- **The cost is the same.** -/
theorem Valid.toB_cost (hk : 2 ≤ k) (hv : c.Valid) : bcost c.toB = c.cost := by
  unfold bcost NConfig.toB NConfig.cost
  rw [List.map_cons, List.sum_cons, List.map_map]
  have hK : BComp.cost ⟨rowsEntries c.kernel, none, 0⟩ = rowsCost c.kernel := by
    show lineCost (rowsEntries c.kernel) + attCost k none _ _ = _
    rw [attCost_none, lineCost_rowsEntries hk c.kernel hv.kernel_ne hv.kernel_len hv.kernel_seams]
    rfl
  rw [hK]
  congr 1
  congr 1
  apply List.map_congr_left
  intro H hH
  exact hv.comp_cost hk hH _

/-- **Lemma T4.**  Every valid standard configuration can be changed into a valid standard
configuration without seams of type T4 whose cost (and so its defect) is not larger. -/
theorem Valid.exists_noT4 (hk : 3 ≤ k) (hv : c.Valid) :
    ∃ c' : NConfig k, c'.Valid ∧ c'.NoT4 ∧ c'.cost ≤ c.cost := by
  have hb := hv.toB_valid
  have hc := hv.toB_cost (by omega)
  obtain ⟨cs', hv', ht', hc'⟩ := exists_valid_noT4 hk hb
  obtain ⟨K, Hs, rfl, hK, hHs⟩ := hv'.kernel
  refine ⟨toConfig K Hs, toConfig_valid (by omega) hv' hHs, toConfig_noT4 (by omega) hv' ht', ?_⟩
  rw [toConfig_cost (by omega) hv' hK hHs]
  omega

end NConfig

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.NConfig.Valid.toB_valid
#print axioms SuperpermLowerBounds.NConfig.Valid.toB_cost
#print axioms SuperpermLowerBounds.NConfig.Valid.exists_noT4

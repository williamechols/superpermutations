import LowerBounds.NBlock
import LowerBounds.NTheorem

/-!
# Lemma T4 of the written model: seams of type T4 are never needed

A link of a line is of type T4 if it goes from the block entered at `g` to the block entered at
`σ x`, `x = τ₂ g`: into the class that would continue the row, one step late.

* `t4_step`: a valid block configuration with such a link can be changed into a valid block
  configuration of no larger cost that has fewer components, or the same number of components
  and a smaller value of `nuB` (the number of links of type T4 plus the number of links that are
  no doors).  The change is the one of the paper: enter the class at `x` instead of `σ x`; and
  if a component hangs at `σ⁻¹ x`, which is now the exit of the block, put its line into the
  line directly after the block.
* `exists_valid_noT4`: hence a valid block configuration without links of type T4 and of no
  larger cost exists.
* `exists_stdConfig_noT4`: every Hamiltonian path (`k ≥ 5`) gives a valid standard configuration
  without seams of type T4 and of defect at most `D(P)`.
* `covers_length_gt_of_no_stdConfig_noT4`: if no valid standard configuration without seams of
  type T4 has defect at most `D`, every covering word has at least `HPV(k) + D + 1` letters.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-! ### Rotation classes -/

theorem rot_sigma (x : Vtx k) : ((x : Vtx k) : List ℕ) ~r ((sigma x : Vtx k) : List ℕ) := ⟨1, rfl⟩

theorem rot_sigmaInv (x : Vtx k) : ((sigmaInv x : Vtx k) : List ℕ) ~r ((x : Vtx k) : List ℕ) :=
  ⟨1, congrArg Subtype.val (Hunter.ProofsStructure.sigma_sigmaInv x)⟩

theorem pairwise_iff_nodup_cls (l : List (Vtx k)) :
    l.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) ↔
      (l.map (fun e : Vtx k => rotClass (e : List ℕ))).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  constructor
  · intro h
    exact h.imp (fun hab he => hab (rotClass_eq_iff.mp he))
  · intro h
    exact h.imp (fun hab hr => hab (rotClass_eq_iff.mpr hr))

/-! ### Lists -/

theorem lsum_split (φ : Vtx k → Vtx k → ℕ) (A : List (Vtx k)) (g y : Vtx k) (B : List (Vtx k)) :
    lsum φ (A ++ g :: y :: B) = lsum φ (A ++ [g]) + φ g y + lsum φ (y :: B) := by
  have e : A ++ g :: y :: B = (A ++ [g]) ++ (y :: B) := by simp
  rw [e]
  exact lsum_append φ (A ++ [g]) (y :: B) g y List.getLast?_concat rfl

theorem head?_append_cons (A : List (Vtx k)) (g : Vtx k) (R : List (Vtx k)) :
    (A ++ g :: R).head? = (A ++ [g]).head? := by
  cases A <;> rfl

theorem getLast?_append_of_ne_nil {S T : List (Vtx k)} (hT : T ≠ []) :
    (S ++ T).getLast? = T.getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast hT]
  rfl

theorem sum_filter_not_singleton (f : BComp k → ℕ) : ∀ (l : List (BComp k)) (a : BComp k),
    l.Nodup → a ∈ l → ((l.filter (fun C => C ∉ [a])).map f).sum + f a = (l.map f).sum
  | [], a, _, h => by simp at h
  | x :: l, a, hnd, h => by
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      by_cases hxa : x = a
      · subst hxa
        have hfil : (x :: l).filter (fun C => C ∉ [x]) = l := by
          rw [List.filter_cons_of_neg (by simp)]
          apply List.filter_eq_self.mpr
          intro b hb
          have hbx : b ≠ x := fun e => hx (e ▸ hb)
          simpa using hbx
        rw [hfil, List.map_cons, List.sum_cons]
        omega
      · have ha : a ∈ l := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hxa
          · exact h
        have ih := sum_filter_not_singleton f l a hnd' ha
        rw [List.filter_cons_of_pos (by simpa using hxa), List.map_cons, List.sum_cons,
          List.map_cons, List.sum_cons]
        omega

theorem sum_upd_le (f g : BComp k → ℕ) (a : BComp k) (δ : ℕ) : ∀ l : List (BComp k), l.Nodup →
    (∀ x ∈ l, x ≠ a → g x ≤ f x) → g a ≤ f a + δ → (l.map g).sum ≤ (l.map f).sum + δ
  | [], _, _, _ => by simp
  | x :: l, hnd, h1, h2 => by
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      by_cases hxa : x = a
      · have h3 : (l.map g).sum ≤ (l.map f).sum := by
          apply List.sum_le_sum
          intro y hy
          refine h1 y (List.mem_cons_of_mem _ hy) (fun e => hx ?_)
          rw [hxa, ← e]
          exact hy
        rw [hxa]
        omega
      · have ih := sum_upd_le f g a δ l hnd' (fun y hy => h1 y (List.mem_cons_of_mem _ hy)) h2
        have h4 := h1 x List.mem_cons_self hxa
        omega

theorem exists_t4_of_not : ∀ L : List (Vtx k), ¬ LineNoT4 L →
    ∃ A g B, L = A ++ g :: sigma (tau2V g) :: B
  | [], h => absurd List.IsChain.nil h
  | [e], h => absurd (List.isChain_singleton e) h
  | a :: b :: rest, h => by
      unfold LineNoT4 at h
      rw [List.isChain_cons_cons] at h
      by_cases hb : b = sigma (tau2V a)
      · exact ⟨[], a, rest, by rw [hb]; rfl⟩
      · have h' : ¬ LineNoT4 (b :: rest) := fun hc => h ⟨hb, hc⟩
        obtain ⟨A, g, B, hL⟩ := exists_t4_of_not (b :: rest) h'
        exact ⟨a :: A, g, B, by rw [hL]; rfl⟩

/-! ### Weights -/

theorem costLink_door (hk : 2 ≤ k) (g : Vtx k) : costLink k g (tau2V g) = 0 := by
  have h := ew_tau_le hk (sigmaInv g)
  show ew k (sigmaInv g) (tau (sigmaInv g)) - 2 = 0
  omega

theorem costLink_t4_pos (hk : 2 ≤ k) {g : Vtx k}
    (hnr : ¬ ((g : List ℕ) ~r ((sigma (tau2V g) : Vtx k) : List ℕ))) :
    1 ≤ costLink k g (sigma (tau2V g)) := by
  have hg := goodLink_of_not_isRotated hk hnr
  have hne : ew k (sigmaInv g) (sigma (tau2V g)) ≠ 2 :=
    fun h2 => sigma_ne_self hk (tau2V g) (hg.2 h2)
  have h1 := hg.1
  unfold costLink
  omega

theorem ew_shift (hk : 1 ≤ k) (x e : Vtx k) : ew k (sigmaInv x) e ≤ ew k x e + 1 := by
  have h := Hunter.ImpRed.ew_triangle hk (sigmaInv x) x e
  rw [ew_sigmaInv_self hk x] at h
  omega

theorem costLink_shift (hk : 1 ≤ k) (x e : Vtx k) :
    costLink k x e ≤ costLink k (sigma x) e + 1 := by
  have h := ew_shift hk x e
  unfold costLink
  rw [sigmaInv_sigma hk]
  omega

theorem attCost_shift (hk : 1 ≤ k) (s : Option (Vtx k)) (x : Vtx k) (h : Option (Vtx k)) :
    attCost k s (some x) h ≤ attCost k s (some (sigma x)) h + 1 := by
  cases s with
  | none =>
      rw [attCost_none, attCost_none]
      omega
  | some v =>
      cases h with
      | none => exact Nat.zero_le _
      | some a =>
          show ew k (sigmaInv x) (sigma v) + ew k v a - 4 ≤
            ew k (sigmaInv (sigma x)) (sigma v) + ew k v a - 4 + 1
          rw [sigmaInv_sigma hk]
          have h1 := ew_shift hk x (sigma v)
          omega

theorem attCost_through (hk : 1 ≤ k) (s : Option (Vtx k)) (b' x : Vtx k) (h : Option (Vtx k)) :
    attCost k s (some b') h ≤ attCost k s (some (sigma x)) h + ew k (sigmaInv b') x := by
  cases s with
  | none =>
      rw [attCost_none, attCost_none]
      omega
  | some v =>
      cases h with
      | none => exact Nat.zero_le _
      | some a =>
          show ew k (sigmaInv b') (sigma v) + ew k v a - 4 ≤
            ew k (sigmaInv (sigma x)) (sigma v) + ew k v a - 4 + ew k (sigmaInv b') x
          rw [sigmaInv_sigma hk]
          have h1 := Hunter.ImpRed.ew_triangle hk (sigmaInv b') x (sigma v)
          omega

/-- The weight of a link for the measure: 1 if it is of type T4, plus 1 if it is no door. -/
noncomputable def nuLink (a b : Vtx k) : ℕ :=
  (if b = sigma (tau2V a) then 1 else 0) + (if b = tau2V a then 0 else 1)

/-- The measure of a block configuration. -/
noncomputable def nuB (cs : List (BComp k)) : ℕ := (cs.map (fun C => lsum nuLink C.line)).sum

theorem nuLink_door (hk : 2 ≤ k) (g : Vtx k) : nuLink g (tau2V g) = 0 := by
  unfold nuLink
  rw [if_neg (fun h => sigma_ne_self hk _ h.symm), if_pos rfl]

theorem nuLink_t4 (hk : 2 ≤ k) (g : Vtx k) : nuLink g (sigma (tau2V g)) = 2 := by
  unfold nuLink
  rw [if_pos rfl, if_neg (sigma_ne_self hk _)]

theorem nuLink_shift (hk : 3 ≤ k) (x e : Vtx k) : nuLink x e ≤ nuLink (sigma x) e + 1 := by
  have hτ : tau2V (sigma x) = tau x := by
    unfold tau2V
    rw [sigmaInv_sigma (by omega)]
  unfold nuLink
  by_cases h1 : e = sigma (tau2V x)
  · have h2 : e ≠ tau2V (sigma x) := by
      rw [hτ, h1]
      exact fun h => tau_ne_sigma_tau2V hk x h.symm
    rw [if_pos h1, if_neg h2]
    split_ifs <;> omega
  · rw [if_neg h1]
    split_ifs <;> omega

theorem nu_case1 (hk : 3 ≤ k) (A : List (Vtx k)) (g : Vtx k) (B : List (Vtx k)) :
    lsum nuLink (A ++ g :: tau2V g :: B) < lsum nuLink (A ++ g :: sigma (tau2V g) :: B) := by
  rw [lsum_split, lsum_split, nuLink_door (by omega), nuLink_t4 (by omega)]
  cases B with
  | nil =>
      simp only [lsum]
      omega
  | cons e B' =>
      have h := nuLink_shift hk (tau2V g) e
      simp only [lsum]
      omega

theorem lineCost_case1_nil (hk : 2 ≤ k) (A : List (Vtx k)) {g : Vtx k}
    (hnr : ¬ ((g : List ℕ) ~r ((sigma (tau2V g) : Vtx k) : List ℕ))) :
    lineCost (A ++ [g, tau2V g]) + 1 ≤ lineCost (A ++ [g, sigma (tau2V g)]) := by
  have h1 := costLink_door hk g
  have h2 := costLink_t4_pos hk hnr
  unfold lineCost
  rw [linkSum_eq_lsum, linkSum_eq_lsum, lsum_split, lsum_split]
  simp only [lsum]
  omega

theorem lineCost_case1_cons (hk : 2 ≤ k) (A : List (Vtx k)) {g : Vtx k} (e : Vtx k)
    (B' : List (Vtx k)) (hnr : ¬ ((g : List ℕ) ~r ((sigma (tau2V g) : Vtx k) : List ℕ))) :
    lineCost (A ++ g :: tau2V g :: e :: B') ≤ lineCost (A ++ g :: sigma (tau2V g) :: e :: B') := by
  have h1 := costLink_door hk g
  have h2 := costLink_t4_pos hk hnr
  have h3 := costLink_shift (by omega : 1 ≤ k) (tau2V g) e
  unfold lineCost
  rw [linkSum_eq_lsum, linkSum_eq_lsum, lsum_split, lsum_split]
  simp only [lsum]
  omega

/-! ### The surgery -/

/-- The component with a new line. -/
def reline (Ci : BComp k) (L' : List (Vtx k)) : BComp k := ⟨L', Ci.slot, Ci.rank⟩

/-- Give `Ci` the line `L'`, leave the other components as they are. -/
noncomputable def upd (Ci : BComp k) (L' : List (Vtx k)) (C : BComp k) : BComp k :=
  if C = Ci then reline Ci L' else C

theorem upd_self (Ci : BComp k) (L' : List (Vtx k)) : upd Ci L' Ci = reline Ci L' := if_pos rfl

theorem upd_of_ne {Ci C : BComp k} (L' : List (Vtx k)) (h : C ≠ Ci) : upd Ci L' C = C := if_neg h

theorem upd_slot (Ci : BComp k) (L' : List (Vtx k)) (C : BComp k) :
    (upd Ci L' C).slot = C.slot := by
  by_cases h : C = Ci
  · rw [h, upd_self]
    rfl
  · rw [upd_of_ne L' h]

theorem upd_rank (Ci : BComp k) (L' : List (Vtx k)) (C : BComp k) :
    (upd Ci L' C).rank = C.rank := by
  by_cases h : C = Ci
  · rw [h, upd_self]
    rfl
  · rw [upd_of_ne L' h]

/-- Give `Ci` the line `L'` and remove the components of `Drop`. -/
noncomputable def surg (cs : List (BComp k)) (Ci : BComp k) (L' : List (Vtx k))
    (Drop : List (BComp k)) : List (BComp k) :=
  (cs.filter (fun C => C ∉ Drop)).map (upd Ci L')

theorem mem_surg {cs : List (BComp k)} {Ci : BComp k} {L' : List (Vtx k)}
    {Drop : List (BComp k)} {C' : BComp k} :
    C' ∈ surg cs Ci L' Drop ↔ ∃ C ∈ cs, C ∉ Drop ∧ C' = upd Ci L' C := by
  unfold surg
  rw [List.mem_map]
  constructor
  · rintro ⟨C, hC, rfl⟩
    rw [List.mem_filter] at hC
    exact ⟨C, hC.1, by simpa using hC.2, rfl⟩
  · rintro ⟨C, hC, hd, rfl⟩
    exact ⟨C, List.mem_filter.mpr ⟨hC, by simpa using hd⟩, rfl⟩

theorem sum_surg (f : BComp k → ℕ) (cs : List (BComp k)) (Ci : BComp k) (L' : List (Vtx k))
    (Drop : List (BComp k)) :
    ((surg cs Ci L' Drop).map f).sum =
      ((cs.filter (fun C => C ∉ Drop)).map (fun C => f (upd Ci L' C))).sum := by
  unfold surg
  rw [List.map_map]
  rfl

/-- What the new line has to satisfy. -/
structure SurgOK (cs : List (BComp k)) (Ci : BComp k) (L' : List (Vtx k))
    (Drop : List (BComp k)) : Prop where
  mem : Ci ∈ cs
  drop_sub : ∀ D ∈ Drop, D ∈ cs
  not_drop : Ci ∉ Drop
  drop_slot : ∀ D ∈ Drop, D.slot ≠ none
  drop_rank : ∀ D ∈ Drop, Ci.rank < D.rank
  ne : L' ≠ []
  inner : L'.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))
  fwd : ∀ e ∈ L', (∃ e₀ ∈ Ci.line, (e : List ℕ) ~r (e₀ : List ℕ)) ∨
    ∃ D ∈ Drop, ∃ e₀ ∈ D.line, (e : List ℕ) ~r (e₀ : List ℕ)
  bwd₁ : ∀ e₀ ∈ Ci.line, ∃ e ∈ L', (e₀ : List ℕ) ~r (e : List ℕ)
  bwd₂ : ∀ D ∈ Drop, ∀ e₀ ∈ D.line, ∃ e ∈ L', (e₀ : List ℕ) ~r (e : List ℕ)
  slot : ∀ C ∈ cs, C ∉ Drop → ∀ v, C.slot = some v → sigma v ∉ L'

/-- **The surgery keeps validity.** -/
theorem surg_valid {cs : List (BComp k)} {Ci : BComp k} {L' : List (Vtx k)}
    {Drop : List (BComp k)} (hv : BValid cs) (h : SurgOK cs Ci L' Drop) :
    BValid (surg cs Ci L' Drop) := by
  have hCi' : reline Ci L' ∈ surg cs Ci L' Drop :=
    mem_surg.mpr ⟨Ci, h.mem, h.not_drop, (upd_self Ci L').symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C' hC'
    obtain ⟨C, hC, _, rfl⟩ := mem_surg.mp hC'
    by_cases hCi : C = Ci
    · rw [hCi, upd_self]
      exact h.ne
    · rw [upd_of_ne L' hCi]
      exact hv.line_ne C hC
  · obtain ⟨K, Hs, hcs, hK, hHs⟩ := hv.kernel
    have hKd : K ∉ Drop := fun hd => h.drop_slot K hd hK
    refine ⟨upd Ci L' K, (Hs.filter (fun C => C ∉ Drop)).map (upd Ci L'), ?_, ?_, ?_⟩
    · unfold surg
      rw [hcs, List.filter_cons_of_pos (by simpa using hKd), List.map_cons]
    · rw [upd_slot]
      exact hK
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      rw [upd_slot]
      exact hHs H (List.mem_of_mem_filter hH)
  · intro C' hC'
    obtain ⟨C, hC, _, rfl⟩ := mem_surg.mp hC'
    by_cases hCi : C = Ci
    · rw [hCi, upd_self]
      exact h.inner
    · rw [upd_of_ne L' hCi]
      exact hv.inner C hC
  · unfold surg
    rw [List.pairwise_map]
    refine (hv.outer.sublist List.filter_sublist).imp_of_mem ?_
    intro C D hC hD hCD
    have hC1 := List.mem_filter.mp hC
    have hD1 := List.mem_filter.mp hD
    have hCd : C ∉ Drop := by simpa using hC1.2
    have hDd : D ∉ Drop := by simpa using hD1.2
    by_cases hCi : C = Ci
    · by_cases hDi : D = Ci
      · exfalso
        rw [hCi, hDi] at hCD
        obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (hv.line_ne Ci h.mem)
        have hmem : e ∈ Ci.line := by
          rw [he]
          exact List.mem_cons_self
        exact hCD e hmem e hmem (List.IsRotated.refl _)
      · rw [hCi, upd_self, upd_of_ne L' hDi]
        rw [hCi] at hCD
        intro x hx y hy hrot
        rcases h.fwd x hx with ⟨e₀, he₀, hr⟩ | ⟨Dr, hDr, e₀, he₀, hr⟩
        · exact hCD e₀ he₀ y hy (hr.symm.trans hrot)
        · have hne : Dr ≠ D := by
            intro e
            apply hDd
            rw [← e]
            exact hDr
          exact hv.disjoint (h.drop_sub Dr hDr) hD1.1 hne e₀ he₀ y hy (hr.symm.trans hrot)
    · by_cases hDi : D = Ci
      · rw [upd_of_ne L' hCi, hDi, upd_self]
        rw [hDi] at hCD
        intro x hx y hy hrot
        rcases h.fwd y hy with ⟨e₀, he₀, hr⟩ | ⟨Dr, hDr, e₀, he₀, hr⟩
        · exact hCD x hx e₀ he₀ (hrot.trans hr)
        · have hne : C ≠ Dr := by
            intro e
            apply hCd
            rw [e]
            exact hDr
          exact hv.disjoint hC1.1 (h.drop_sub Dr hDr) hne x hx e₀ he₀ (hrot.trans hr)
      · rw [upd_of_ne L' hCi, upd_of_ne L' hDi]
        exact hCD
  · intro v
    obtain ⟨C, hC, e, he, hrot⟩ := hv.cover v
    by_cases hCd : C ∈ Drop
    · obtain ⟨e', he', hr⟩ := h.bwd₂ C hCd e he
      exact ⟨reline Ci L', hCi', e', he', hrot.trans hr⟩
    · by_cases hCi : C = Ci
      · rw [hCi] at he
        obtain ⟨e', he', hr⟩ := h.bwd₁ e he
        exact ⟨reline Ci L', hCi', e', he', hrot.trans hr⟩
      · exact ⟨C, mem_surg.mpr ⟨C, hC, hCd, (upd_of_ne L' hCi).symm⟩, e, he, hrot⟩
  · intro C' hC' v hslot D' hD'
    obtain ⟨C, hC, hCd, rfl⟩ := mem_surg.mp hC'
    obtain ⟨D, hD, _, rfl⟩ := mem_surg.mp hD'
    rw [upd_slot] at hslot
    by_cases hDi : D = Ci
    · rw [hDi, upd_self]
      exact h.slot C hC hCd v hslot
    · rw [upd_of_ne L' hDi]
      exact hv.slot C hC v hslot D hD
  · intro C' hC' D' hD' v h1 h2
    obtain ⟨C, hC, _, rfl⟩ := mem_surg.mp hC'
    obtain ⟨D, hD, _, rfl⟩ := mem_surg.mp hD'
    rw [upd_slot] at h1 h2
    rw [hv.slots C hC D hD v h1 h2]
  · intro C' hC' v hslot D' hD' hex
    obtain ⟨C, hC, hCd, rfl⟩ := mem_surg.mp hC'
    obtain ⟨D, hD, _, rfl⟩ := mem_surg.mp hD'
    rw [upd_slot] at hslot
    rw [upd_rank, upd_rank]
    obtain ⟨e, he, hrot⟩ := hex
    by_cases hDi : D = Ci
    · rw [hDi, upd_self] at he
      rw [hDi]
      rcases h.fwd e he with ⟨e₀, he₀, hr⟩ | ⟨Dr, hDr, e₀, he₀, hr⟩
      · exact hv.forest C hC v hslot Ci h.mem ⟨e₀, he₀, hrot.trans hr⟩
      · have h1 := hv.forest C hC v hslot Dr (h.drop_sub Dr hDr) ⟨e₀, he₀, hrot.trans hr⟩
        have h2 := h.drop_rank Dr hDr
        omega
    · rw [upd_of_ne L' hDi] at he
      exact hv.forest C hC v hslot D hD ⟨e, he, hrot⟩

/-! ### One step -/

/-- **One step of Lemma T4.** -/
theorem t4_step (hk : 3 ≤ k) {cs : List (BComp k)} (hv : BValid cs) {Ci : BComp k}
    (hCi : Ci ∈ cs) {A B : List (Vtx k)} {g : Vtx k}
    (hline : Ci.line = A ++ g :: sigma (tau2V g) :: B) :
    ∃ cs' : List (BComp k), BValid cs' ∧ bcost cs' ≤ bcost cs ∧
      (cs'.length < cs.length ∨ (cs'.length = cs.length ∧ nuB cs' < nuB cs)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨x, hx⟩ : ∃ x : Vtx k, x = tau2V g := ⟨_, rfl⟩
  rw [← hx] at hline
  have hin := hv.inner Ci hCi
  rw [hline] at hin
  have hmemL : ∀ e, e ∈ Ci.line ↔ e ∈ A ∨ e = g ∨ e = sigma x ∨ e ∈ B := by
    intro e
    rw [hline]
    simp only [List.mem_append, List.mem_cons]
  have hsxmem : sigma x ∈ Ci.line := (hmemL _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hnr : ¬ ((g : List ℕ) ~r ((sigma x : Vtx k) : List ℕ)) := by
    have h1 := (List.pairwise_append.mp hin).2.1
    exact (List.pairwise_cons.mp h1).1 (sigma x) List.mem_cons_self
  have hnr' : ¬ ((g : List ℕ) ~r ((sigma (tau2V g) : Vtx k) : List ℕ)) := by
    rw [← hx]
    exact hnr
  have hcostCi : Ci.cost = lineCost (A ++ g :: sigma x :: B) +
      attCost k Ci.slot (A ++ g :: sigma x :: B).getLast? (A ++ [g]).head? := by
    unfold BComp.cost BComp.att
    rw [hline, head?_append_cons]
  by_cases hex : ∃ H' ∈ cs, H'.slot = some (sigmaInv x)
  · -- a component hangs at `σ⁻¹ x`: its line goes into the line after the block
    obtain ⟨H', hH', hslot'⟩ := hex
    have hsig : sigma (sigmaInv x) = x := Hunter.ProofsStructure.sigma_sigmaInv x
    have hrk : Ci.rank < H'.rank :=
      hv.forest H' hH' _ hslot' Ci hCi ⟨sigma x, hsxmem, (rot_sigmaInv x).trans (rot_sigma x)⟩
    have hne : Ci ≠ H' := by
      intro e
      rw [e] at hrk
      exact lt_irrefl _ hrk
    have hdisj := hv.disjoint hCi hH' hne
    have hLne := hv.line_ne H' hH'
    obtain ⟨a', ha'⟩ : ∃ a', H'.line.head? = some a' := ⟨_, List.head?_eq_some_head hLne⟩
    obtain ⟨b', hb'⟩ : ∃ b', H'.line.getLast? = some b' := ⟨_, List.getLast?_eq_some_getLast hLne⟩
    have ha'mem : a' ∈ H'.line := by
      obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp ha'
      rw [hys]
      exact List.mem_cons_self
    have hb'mem : b' ∈ H'.line := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hb'
      rw [hys]
      simp
    have hnoslot := hv.slot H' hH' _ hslot' H' hH'
    rw [hsig] at hnoslot
    -- the two edges of the attachment of `H'` have weight at least 2
    have hw1 : 2 ≤ ew k (sigmaInv x) a' := by
      have h1 := Hunter.ProofsExitless.ew_ge_one hk1 (sigmaInv x) a'
      have h2 : ew k (sigmaInv x) a' ≠ 1 := by
        intro hone
        have h3 := (Hunter.ProofsExitless.ew_eq_one_iff hk1).mp hone
        rw [hsig] at h3
        exact hnoslot (h3 ▸ ha'mem)
      omega
    have hw0 : 2 ≤ ew k (sigmaInv b') x := by
      have h1 := Hunter.ProofsExitless.ew_ge_one hk1 (sigmaInv b') x
      have h2 : ew k (sigmaInv b') x ≠ 1 := by
        intro hone
        have h3 := (Hunter.ProofsExitless.ew_eq_one_iff hk1).mp hone
        rw [Hunter.ProofsStructure.sigma_sigmaInv] at h3
        exact hnoslot (h3 ▸ hb'mem)
      omega
    have hcostH : H'.cost = lineCost H'.line +
        (ew k (sigmaInv b') x + ew k (sigmaInv x) a' - 4) := by
      unfold BComp.cost BComp.att
      rw [hslot', hb', ha']
      show _ + (ew k (sigmaInv b') (sigma (sigmaInv x)) + ew k (sigmaInv x) a' - 4) = _
      rw [hsig]
    obtain ⟨L2, hL2⟩ : ∃ L2, L2 = A ++ g :: x :: (H'.line ++ B) := ⟨_, rfl⟩
    have hmemL2 : ∀ e, e ∈ L2 ↔ e ∈ A ∨ e = g ∨ e = x ∨ e ∈ H'.line ∨ e ∈ B := by
      intro e
      rw [hL2]
      simp only [List.mem_append, List.mem_cons]
    have hok : SurgOK cs Ci L2 [H'] := by
      refine ⟨hCi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro D hD
        rw [List.mem_singleton.mp hD]
        exact hH'
      · intro h
        exact hne (List.mem_singleton.mp h)
      · intro D hD
        rw [List.mem_singleton.mp hD, hslot']
        simp
      · intro D hD
        rw [List.mem_singleton.mp hD]
        exact hrk
      · rw [hL2]
        simp
      · -- the classes of the new line are those of the two old lines
        rw [pairwise_iff_nodup_cls]
        have hold : (Ci.line ++ H'.line).Pairwise
            (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) := by
          rw [List.pairwise_append]
          exact ⟨hv.inner Ci hCi, hv.inner H' hH', hdisj⟩
        rw [pairwise_iff_nodup_cls, hline] at hold
        have hcls : rotClass ((sigma x : Vtx k) : List ℕ) = rotClass ((x : Vtx k) : List ℕ) :=
          Hunter.ProofsStructure.rotClass_sigma x
        have hperm : (L2.map (fun e : Vtx k => rotClass (e : List ℕ))).Perm
            (((A ++ g :: sigma x :: B) ++ H'.line).map (fun e : Vtx k => rotClass (e : List ℕ))) := by
          rw [hL2]
          simp only [List.map_append, List.map_cons, hcls, List.append_assoc, List.cons_append]
          refine List.Perm.append_left _ (List.Perm.cons _ (List.Perm.cons _ ?_))
          exact List.perm_append_comm
        exact hperm.nodup_iff.mpr hold
      · intro e he
        rcases (hmemL2 e).mp he with h | h | h | h | h
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inl h), List.IsRotated.refl _⟩
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inr (Or.inl h)), List.IsRotated.refl _⟩
        · refine Or.inl ⟨sigma x, hsxmem, ?_⟩
          rw [h]
          exact rot_sigma x
        · exact Or.inr ⟨H', List.mem_singleton.mpr rfl, e, h, List.IsRotated.refl _⟩
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inr (Or.inr (Or.inr h))), List.IsRotated.refl _⟩
      · intro e₀ he₀
        rcases (hmemL e₀).mp he₀ with h | h | h | h
        · exact ⟨e₀, (hmemL2 e₀).mpr (Or.inl h), List.IsRotated.refl _⟩
        · exact ⟨e₀, (hmemL2 e₀).mpr (Or.inr (Or.inl h)), List.IsRotated.refl _⟩
        · refine ⟨x, (hmemL2 x).mpr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
          rw [h]
          exact (rot_sigma x).symm
        · exact ⟨e₀, (hmemL2 e₀).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))), List.IsRotated.refl _⟩
      · intro D hD e₀ he₀
        rw [List.mem_singleton.mp hD] at he₀
        exact ⟨e₀, (hmemL2 e₀).mpr (Or.inr (Or.inr (Or.inr (Or.inl he₀)))), List.IsRotated.refl _⟩
      · intro C hC hCd v hslot hmem
        have hCne : C ≠ H' := fun e => hCd (List.mem_singleton.mpr e)
        rcases (hmemL2 _).mp hmem with h | h | h | h | h
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inl h))
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inr (Or.inl h)))
        · apply hCne
          apply hv.slots C hC H' hH' v hslot
          rw [hslot', ← h, sigmaInv_sigma hk1]
        · exact hv.slot C hC v hslot H' hH' h
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inr (Or.inr (Or.inr h))))
    -- the cost of the new component
    have hcost2 : (reline Ci L2).cost ≤ Ci.cost + H'.cost := by
      have hd0 := costLink_door hk2 g
      have hd1 := costLink_t4_pos hk2 hnr'
      rw [← hx] at hd0 hd1
      have hφx : costLink k x a' = ew k (sigmaInv x) a' - 2 := rfl
      have hhead : (H'.line ++ B).head? = some a' := by
        rw [List.head?_append, ha']
        rfl
      have hsplit : lsum (costLink k) L2 = lsum (costLink k) (A ++ [g]) + costLink k g x +
          (costLink k x a' + lsum (costLink k) (H'.line ++ B)) := by
        rw [hL2, lsum_split]
        have e1 : x :: (H'.line ++ B) = [x] ++ (H'.line ++ B) := rfl
        rw [e1, lsum_append (costLink k) [x] (H'.line ++ B) x a' rfl hhead]
        simp only [lsum]
        omega
      have hnewcost : (reline Ci L2).cost = lineCost L2 +
          attCost k Ci.slot L2.getLast? (A ++ [g]).head? := by
        show lineCost L2 + attCost k Ci.slot L2.getLast? L2.head? = _
        rw [hL2, head?_append_cons]
      rw [hnewcost, hcostCi, hcostH]
      unfold lineCost
      rw [linkSum_eq_lsum, linkSum_eq_lsum, linkSum_eq_lsum, hsplit, lsum_split, hφx]
      cases B with
      | nil =>
          have hlast : L2.getLast? = some b' := by
            rw [hL2]
            have e2 : A ++ g :: x :: (H'.line ++ []) = (A ++ [g, x]) ++ H'.line := by simp
            rw [e2, getLast?_append_of_ne_nil hLne, hb']
          have hlast0 : (A ++ [g, sigma x]).getLast? = some (sigma x) := by
            have e3 : A ++ [g, sigma x] = (A ++ [g]) ++ [sigma x] := by simp
            rw [e3, List.getLast?_concat]
          have hatt := attCost_through hk1 Ci.slot b' x (A ++ [g]).head?
          rw [hlast, hlast0, List.append_nil]
          simp only [lsum]
          omega
      | cons e B' =>
          have hlast : L2.getLast? = (e :: B').getLast? := by
            rw [hL2]
            have e2 : A ++ g :: x :: (H'.line ++ e :: B') = (A ++ g :: x :: H'.line) ++ (e :: B') := by
              simp
            rw [e2, getLast?_append_of_ne_nil (List.cons_ne_nil _ _)]
          have hlast0 : (A ++ g :: sigma x :: e :: B').getLast? = (e :: B').getLast? := by
            have e3 : A ++ g :: sigma x :: e :: B' = (A ++ [g, sigma x]) ++ (e :: B') := by simp
            rw [e3, getLast?_append_of_ne_nil (List.cons_ne_nil _ _)]
          have hjoin := lsum_append (costLink k) H'.line (e :: B') b' e hb' rfl
          have hxe : 2 ≤ ew k x e := by
            have h1 := (List.pairwise_append.mp hin).2.1
            have h2 := (List.pairwise_cons.mp (List.pairwise_cons.mp h1).2).1 e List.mem_cons_self
            have h3 := (goodLink_of_not_isRotated hk2 h2).1
            rwa [sigmaInv_sigma hk1] at h3
          have htri := Hunter.ImpRed.ew_triangle hk1 (sigmaInv b') x e
          have hφb : costLink k b' e = ew k (sigmaInv b') e - 2 := rfl
          have hφs : costLink k (sigma x) e = ew k x e - 2 := by
            unfold costLink
            rw [sigmaInv_sigma hk1]
          rw [hlast, hlast0, hjoin, hφb]
          simp only [lsum]
          rw [hφs]
          omega
    refine ⟨surg cs Ci L2 [H'], surg_valid hv hok, ?_, Or.inl ?_⟩
    · unfold bcost
      rw [sum_surg]
      have h1 := sum_upd_le BComp.cost (fun C => (upd Ci L2 C).cost) Ci H'.cost
        (cs.filter (fun C => C ∉ [H'])) (hv.nodup.filter _)
        (fun C _ hCne => le_of_eq (congrArg BComp.cost (upd_of_ne L2 hCne)))
        (by rw [upd_self]; exact hcost2)
      have h2 := sum_filter_not_singleton BComp.cost cs H' hv.nodup hH'
      omega
    · unfold surg
      rw [List.length_map]
      exact List.length_filter_lt_length_iff_exists.mpr ⟨H', hH', by simp⟩
  · -- no component hangs at `σ⁻¹ x`: only the entry of the block changes
    obtain ⟨L1, hL1⟩ : ∃ L1, L1 = A ++ g :: x :: B := ⟨_, rfl⟩
    have hmemL1 : ∀ e, e ∈ L1 ↔ e ∈ A ∨ e = g ∨ e = x ∨ e ∈ B := by
      intro e
      rw [hL1]
      simp only [List.mem_append, List.mem_cons]
    have hok : SurgOK cs Ci L1 [] := by
      refine ⟨hCi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro D hD
        simp at hD
      · simp
      · intro D hD
        simp at hD
      · intro D hD
        simp at hD
      · rw [hL1]
        simp
      · rw [pairwise_iff_nodup_cls]
        have hold := hin
        rw [pairwise_iff_nodup_cls] at hold
        have hcls : rotClass ((sigma x : Vtx k) : List ℕ) = rotClass ((x : Vtx k) : List ℕ) :=
          Hunter.ProofsStructure.rotClass_sigma x
        have heq : L1.map (fun e : Vtx k => rotClass (e : List ℕ)) =
            (A ++ g :: sigma x :: B).map (fun e : Vtx k => rotClass (e : List ℕ)) := by
          rw [hL1]
          simp only [List.map_append, List.map_cons, hcls]
        rw [heq]
        exact hold
      · intro e he
        rcases (hmemL1 e).mp he with h | h | h | h
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inl h), List.IsRotated.refl _⟩
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inr (Or.inl h)), List.IsRotated.refl _⟩
        · refine Or.inl ⟨sigma x, hsxmem, ?_⟩
          rw [h]
          exact rot_sigma x
        · exact Or.inl ⟨e, (hmemL e).mpr (Or.inr (Or.inr (Or.inr h))), List.IsRotated.refl _⟩
      · intro e₀ he₀
        rcases (hmemL e₀).mp he₀ with h | h | h | h
        · exact ⟨e₀, (hmemL1 e₀).mpr (Or.inl h), List.IsRotated.refl _⟩
        · exact ⟨e₀, (hmemL1 e₀).mpr (Or.inr (Or.inl h)), List.IsRotated.refl _⟩
        · refine ⟨x, (hmemL1 x).mpr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
          rw [h]
          exact (rot_sigma x).symm
        · exact ⟨e₀, (hmemL1 e₀).mpr (Or.inr (Or.inr (Or.inr h))), List.IsRotated.refl _⟩
      · intro D hD
        simp at hD
      · intro C hC _ v hslot hmem
        rcases (hmemL1 _).mp hmem with h | h | h | h
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inl h))
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inr (Or.inl h)))
        · apply hex
          refine ⟨C, hC, ?_⟩
          rw [hslot, ← h, sigmaInv_sigma hk1]
        · exact hv.slot C hC v hslot Ci hCi ((hmemL _).mpr (Or.inr (Or.inr (Or.inr h))))
    have hcost1 : (reline Ci L1).cost ≤ Ci.cost := by
      have hnewcost : (reline Ci L1).cost = lineCost L1 +
          attCost k Ci.slot L1.getLast? (A ++ [g]).head? := by
        show lineCost L1 + attCost k Ci.slot L1.getLast? L1.head? = _
        rw [hL1, head?_append_cons]
      rw [hnewcost, hcostCi, hL1, hx]
      cases B with
      | nil =>
          have hl1 : (A ++ [g, tau2V g]).getLast? = some (tau2V g) := by
            have e3 : A ++ [g, tau2V g] = (A ++ [g]) ++ [tau2V g] := by simp
            rw [e3, List.getLast?_concat]
          have hl0 : (A ++ [g, sigma (tau2V g)]).getLast? = some (sigma (tau2V g)) := by
            have e3 : A ++ [g, sigma (tau2V g)] = (A ++ [g]) ++ [sigma (tau2V g)] := by simp
            rw [e3, List.getLast?_concat]
          have h1 := lineCost_case1_nil hk2 A hnr'
          have h2 := attCost_shift hk1 Ci.slot (tau2V g) (A ++ [g]).head?
          rw [hl1, hl0]
          omega
      | cons e B' =>
          have hl1 : (A ++ g :: tau2V g :: e :: B').getLast? = (e :: B').getLast? := by
            have e3 : A ++ g :: tau2V g :: e :: B' = (A ++ [g, tau2V g]) ++ (e :: B') := by simp
            rw [e3, getLast?_append_of_ne_nil (List.cons_ne_nil _ _)]
          have hl0 : (A ++ g :: sigma (tau2V g) :: e :: B').getLast? = (e :: B').getLast? := by
            have e3 : A ++ g :: sigma (tau2V g) :: e :: B' =
                (A ++ [g, sigma (tau2V g)]) ++ (e :: B') := by simp
            rw [e3, getLast?_append_of_ne_nil (List.cons_ne_nil _ _)]
          have h1 := lineCost_case1_cons hk2 A e B' hnr'
          rw [hl1, hl0]
          omega
    have hnu1 : lsum nuLink (reline Ci L1).line < lsum nuLink Ci.line := by
      show lsum nuLink L1 < lsum nuLink Ci.line
      rw [hL1, hline, hx]
      exact nu_case1 hk A g B
    have hfil : cs.filter (fun C => C ∉ ([] : List (BComp k))) = cs :=
      List.filter_eq_self.mpr (fun C _ => by simp)
    refine ⟨surg cs Ci L1 [], surg_valid hv hok, ?_, Or.inr ⟨?_, ?_⟩⟩
    · unfold bcost
      rw [sum_surg, hfil]
      apply List.sum_le_sum
      intro C _
      by_cases hCne : C = Ci
      · rw [hCne, upd_self]
        exact hcost1
      · rw [upd_of_ne L1 hCne]
    · unfold surg
      rw [List.length_map, hfil]
    · unfold nuB
      rw [sum_surg, hfil]
      apply List.sum_lt_sum
      · intro C _
        by_cases hCne : C = Ci
        · rw [hCne, upd_self]
          exact le_of_lt hnu1
        · rw [upd_of_ne L1 hCne]
      · exact ⟨Ci, hCi, by rw [upd_self]; exact hnu1⟩

/-! ### Lemma T4 -/

/-- **Lemma T4 for block configurations.** -/
theorem exists_valid_noT4 (hk : 3 ≤ k) {cs : List (BComp k)} (hv : BValid cs) :
    ∃ cs' : List (BComp k), BValid cs' ∧ BNoT4 cs' ∧ bcost cs' ≤ bcost cs := by
  have hex1 : ∃ n, ∃ cs' : List (BComp k), BValid cs' ∧ bcost cs' ≤ bcost cs ∧ cs'.length = n :=
    ⟨cs.length, cs, hv, le_refl _, rfl⟩
  obtain ⟨cs₁, hv₁, hc₁, hl₁⟩ := Nat.find_spec hex1
  have hmin₁ : ∀ m, m < Nat.find hex1 →
      ¬ ∃ cs' : List (BComp k), BValid cs' ∧ bcost cs' ≤ bcost cs ∧ cs'.length = m :=
    fun m hm => Nat.find_min hex1 hm
  have hex2 : ∃ ν, ∃ cs' : List (BComp k), BValid cs' ∧ bcost cs' ≤ bcost cs ∧
      cs'.length = Nat.find hex1 ∧ nuB cs' = ν := ⟨nuB cs₁, cs₁, hv₁, hc₁, hl₁, rfl⟩
  obtain ⟨cs₂, hv₂, hc₂, hl₂, hν₂⟩ := Nat.find_spec hex2
  have hmin₂ : ∀ m, m < Nat.find hex2 → ¬ ∃ cs' : List (BComp k), BValid cs' ∧ bcost cs' ≤ bcost cs ∧
      cs'.length = Nat.find hex1 ∧ nuB cs' = m :=
    fun m hm => Nat.find_min hex2 hm
  refine ⟨cs₂, hv₂, ?_, hc₂⟩
  intro C hC
  by_contra hnot
  obtain ⟨A, g, B, hline⟩ := exists_t4_of_not C.line hnot
  obtain ⟨cs', hv', hc', hcase⟩ := t4_step hk hv₂ hC hline
  rcases hcase with hlt | ⟨hleq, hνlt⟩
  · exact hmin₁ cs'.length (by omega) ⟨cs', hv', by omega, rfl⟩
  · exact hmin₂ (nuB cs') (by omega) ⟨cs', hv', by omega, by omega, rfl⟩

/-- **Theorems W and N with Lemma T4.**  Every Hamiltonian path gives a valid standard
configuration without seams of type T4 whose defect `cost - (k-2)!` is at most
`D(P) = wt(P) + k - HPV(k)`. -/
theorem exists_stdConfig_noT4 (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    ∃ c : NConfig k, c.Valid ∧ c.NoT4 ∧ hpv k + c.cost ≤ (k - 2).factorial + (P.wtP + k) := by
  have hv := (joinData hk hP).bcomps_valid
  have hc := (joinData hk hP).bcomps_cost_le (by omega)
  have hs := sum_charge_le hk hP
  obtain ⟨cs', hv', ht', hc'⟩ := exists_valid_noT4 (by omega) hv
  obtain ⟨K, Hs, rfl, hK, hHs⟩ := hv'.kernel
  refine ⟨toConfig K Hs, toConfig_valid (by omega) hv' hHs, toConfig_noT4 (by omega) hv' ht', ?_⟩
  rw [toConfig_cost (by omega) hv' hK hHs]
  omega

/-- **The lower direction with Lemma T4, for the searches.**  If no valid standard
configuration without seams of type T4 has defect at most `D`, every word over `Fin k` that
contains all permutations has at least `HPV(k) + D + 1` letters. -/
theorem covers_length_gt_of_no_stdConfig_noT4 (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → c.NoT4 → ¬ c.cost ≤ (k - 2).factorial + D) :
    ∀ w : List (Fin k), SuperpermutationBounds.Covers w → hpv k + D + 1 ≤ w.length := by
  have hpath : ∀ P : HPath k, P.IsHamiltonian → hpv k + D + 1 ≤ P.wtP + k := by
    intro P hP
    obtain ⟨c, hv, ht, hc⟩ := exists_stdConfig_noT4 hk hP
    have h1 := h c hv ht
    omega
  exact (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp
    (ssuper_ge_of_pathwise (by omega) hpath)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.surg_valid
#print axioms SuperpermLowerBounds.t4_step
#print axioms SuperpermLowerBounds.exists_valid_noT4
#print axioms SuperpermLowerBounds.exists_stdConfig_noT4
#print axioms SuperpermLowerBounds.covers_length_gt_of_no_stdConfig_noT4

import LowerBounds.NCore
import LowerBounds.NRules

/-!
# Standard configurations on the level of blocks

A *block configuration* is a list of components `BComp`: a line of block entries, the vertex of
its attachment (`none` for the kernel, which is the first component) and a rank.  `BValid` is
the standard model with the forest condition written with ranks: the component that contains
the vertex of `C` has a smaller rank than `C`.

* `toConfig`, `toConfig_valid`, `toConfig_cost`, `toConfig_noT4`: a valid block configuration is
  a valid standard configuration (`NConfig.Valid`) with the same cost, and without seams of
  type T4 if no link of a line lands at `σ (τ₂ g)`.
* `JoinData.bcomps`, `bcomps_valid`, `bcomps_cost_le`: the configuration of Theorem N as a block
  configuration.
* word lemmas: `ew_tau_le` (a door has weight at most 2), `tau_ne_sigma_tau2V` (the successor
  of type T5 is not the one of type T4).

This file prepares Lemma T4 (`NT4.lean`), which is proved by surgery on block configurations.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators

variable {k : ℕ}

/-! ### Sums over the links of a line -/

/-- The sum of `φ a b` over the links `a, b` (consecutive block entries) of a line. -/
def lsum (φ : Vtx k → Vtx k → ℕ) : List (Vtx k) → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => φ a b + lsum φ (b :: rest)

theorem lsum_append (φ : Vtx k → Vtx k → ℕ) : ∀ (A B : List (Vtx k)) (a b : Vtx k),
    A.getLast? = some a → B.head? = some b → lsum φ (A ++ B) = lsum φ A + φ a b + lsum φ B
  | [], _, _, _, h, _ => by simp at h
  | [x], B, a, b, h, hb => by
      rcases B with _ | ⟨b', B'⟩
      · simp at hb
      · simp only [List.getLast?_singleton, Option.some.injEq] at h
        simp only [List.head?_cons, Option.some.injEq] at hb
        subst h
        subst hb
        simp only [List.cons_append, List.nil_append, lsum]
        omega
  | x :: y :: A, B, a, b, h, hb => by
      rw [List.getLast?_cons_cons] at h
      have ih := lsum_append φ (y :: A) B a b h hb
      have e1 : lsum φ (x :: y :: A ++ B) = φ x y + lsum φ (y :: A ++ B) := by
        simp only [List.cons_append, lsum]
      rw [e1, ih]
      simp only [lsum]
      omega

/-- The cost of a link: weight minus 2. -/
noncomputable def costLink (k : ℕ) (a b : Vtx k) : ℕ := ew k (sigmaInv a) b - 2

theorem linkSum_eq_lsum : ∀ L : List (Vtx k), linkSum L = lsum (costLink k) L
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      show (ew k (sigmaInv a) b - 2) + linkSum (b :: rest) =
        costLink k a b + lsum (costLink k) (b :: rest)
      rw [linkSum_eq_lsum (b :: rest)]
      rfl

/-! ### Words -/

/-- A door has weight at most 2. -/
theorem ew_tau_le (hk : 2 ≤ k) (u : Vtx k) : ew k u (tau u) ≤ 2 := by
  have hlen := u.2.length
  show wt k (u : List ℕ) ((tau u : Vtx k) : List ℕ) ≤ 2
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord hk u.2)]
  apply wt_le (by omega) hk
  unfold Hunter.door
  rw [List.take_left' (by rw [List.length_drop]; omega)]

theorem ew_sigmaInv_self (hk : 1 ≤ k) (x : Vtx k) : ew k (sigmaInv x) x = 1 := by
  have h := Hunter.ew_sigma hk (sigmaInv x)
  rwa [Hunter.ProofsStructure.sigma_sigmaInv] at h

theorem sigma_ne_self (hk : 2 ≤ k) (x : Vtx k) : sigma x ≠ x := by
  intro h
  have h1 := Hunter.ProofsExitless.sigma_iter_inj x (a := 1) (b := 0) (by omega) (by omega)
    (by simpa using h)
  omega

/-- The successor of type T5 is not the successor of type T4: `τ x ≠ σ (τ₂ x)`. -/
theorem tau_ne_sigma_tau2V (hk : 3 ≤ k) (x : Vtx k) : tau x ≠ sigma (tau2V x) := by
  intro h
  have hval := congrArg Subtype.val h
  obtain ⟨u, hu0⟩ : ∃ u : Vtx k, u = sigmaInv x := ⟨_, rfl⟩
  have hx : x = sigma u := by
    rw [hu0, Hunter.ProofsStructure.sigma_sigmaInv]
  have hulen := u.2.length
  obtain ⟨a, b, c, M, hu⟩ : ∃ a b c M, (u : List ℕ) = a :: b :: c :: M := by
    rcases hul : (u : List ℕ) with _ | ⟨a, _ | ⟨b, _ | ⟨c, M⟩⟩⟩
    · rw [hul] at hulen; simp at hulen; omega
    · rw [hul] at hulen; simp at hulen; omega
    · rw [hul] at hulen; simp at hulen; omega
    · exact ⟨a, b, c, M, rfl⟩
  have hnd : (a :: b :: c :: M).Nodup := hu ▸ u.2.nodup
  have hab : a ≠ b := fun e => (List.nodup_cons.mp hnd).1 (by rw [e]; exact List.mem_cons_self)
  have hx1 : (x : List ℕ) = b :: c :: (M ++ [a]) := by
    rw [hx]
    show (u : List ℕ).rotate 1 = _
    rw [hu]
    simp [List.rotate_cons_succ]
  have h1 : ((tau x : Vtx k) : List ℕ) = (M ++ [a]) ++ [c, b] := by
    rw [Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) x.2), hx1]
    rfl
  have h2 : ((tau2V x : Vtx k) : List ℕ) = c :: (M ++ [b, a]) := by
    show ((tau (sigmaInv x) : Vtx k) : List ℕ) = _
    rw [← hu0, Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) u.2), hu]
    rfl
  have h3 : ((sigma (tau2V x) : Vtx k) : List ℕ) = (M ++ [b, a]) ++ [c] := by
    show ((tau2V x : Vtx k) : List ℕ).rotate 1 = _
    rw [h2]
    simp [List.rotate_cons_succ]
  rw [h1, h3] at hval
  simp at hval
  exact hab hval.1

/-! ### Seams of type T4 -/

/-- No link of the line lands at `σ (τ₂ g)`, `g` the block entry before. -/
def LineNoT4 (L : List (Vtx k)) : Prop := L.IsChain (fun a b => b ≠ sigma (tau2V a))

/-- No seam of type T4: no row starts at `σ (τ₂ g)`, `g` the last block entry of the row
before. -/
def RowsNoT4 (rows : List (NRow k)) : Prop :=
  rows.IsChain (fun r r' => r'.entry ≠ sigma (tau2V r.lastEntry))

/-- A configuration without seams of type T4. -/
def NConfig.NoT4 (c : NConfig k) : Prop := RowsNoT4 c.kernel ∧ ∀ H ∈ c.hanging, RowsNoT4 H.rows

theorem NRow.lastEntry_succ (e : Vtx k) (n : ℕ) :
    NRow.lastEntry ⟨e, n + 2⟩ = NRow.lastEntry ⟨tau2V e, n + 1⟩ := by
  unfold NRow.lastEntry
  simp only [Nat.add_sub_cancel]
  show tau2V^[n + 1] e = tau2V^[n] (tau2V e)
  rw [Function.iterate_succ_apply]

theorem groupRows_noT4 : ∀ L : List (Vtx k), L.IsChain (GoodLink k) → LineNoT4 L →
    RowsNoT4 (groupRows L)
  | [], _, _ => List.IsChain.nil
  | [e], _, _ => List.isChain_singleton _
  | e :: e' :: rest, hc, ht => by
      unfold LineNoT4 at ht
      rw [List.isChain_cons_cons] at hc ht
      have ih := groupRows_noT4 (e' :: rest) hc.2 ht.2
      have inv := groupRows_spec (e' :: rest) hc.2
      obtain ⟨rows, hrows⟩ : ∃ rows, rows = groupRows (e' :: rest) := ⟨_, rfl⟩
      have hg : groupRows (e :: e' :: rest) = consRow e rows := by
        rw [hrows]
        rfl
      rw [hg]
      rw [← hrows] at ih inv
      rcases rows with _ | ⟨r, rs⟩
      · have h := inv.entries
        simp [rowsEntries] at h
      obtain ⟨re, rl⟩ := r
      have hrl : 1 ≤ rl := inv.len ⟨re, rl⟩ List.mem_cons_self
      obtain ⟨m, rfl⟩ : ∃ m, rl = m + 1 := ⟨rl - 1, by omega⟩
      have hre : re = e' := by
        have h := inv.head
        simp only [List.head?_cons, Option.map_some] at h
        exact Option.some.inj h
      subst hre
      unfold RowsNoT4 at ih ⊢
      by_cases h2 : ew k (sigmaInv e) re = 2
      · have hτ : re = tau2V e := hc.1.2 h2
        have hcr : consRow e (⟨re, m + 1⟩ :: rs) = ⟨e, m + 2⟩ :: rs := by
          simp only [consRow, h2, if_true]
        rw [hcr]
        rcases rs with _ | ⟨r₂, rs'⟩
        · exact List.isChain_singleton _
        · rw [List.isChain_cons_cons] at ih ⊢
          refine ⟨?_, ih.2⟩
          rw [NRow.lastEntry_succ, ← hτ]
          exact ih.1
      · have hcr : consRow e (⟨re, m + 1⟩ :: rs) = ⟨e, 1⟩ :: ⟨re, m + 1⟩ :: rs := by
          simp only [consRow, h2, if_false]
        rw [hcr, List.isChain_cons_cons]
        exact ⟨ht.1, ih⟩

/-! ### Block configurations -/

/-- A component of a block configuration. -/
structure BComp (k : ℕ) where
  /-- the block entries, in order -/
  line : List (Vtx k)
  /-- the vertex of the attachment; `none` for the kernel -/
  slot : Option (Vtx k)
  /-- a rank; the component that contains `slot` has a smaller one -/
  rank : ℕ

/-- The cost of an attachment, from the vertex, the last and the first block entry. -/
noncomputable def attCost (k : ℕ) : Option (Vtx k) → Option (Vtx k) → Option (Vtx k) → ℕ
  | some v, some b, some a => ew k (sigmaInv b) (sigma v) + ew k v a - 4
  | _, _, _ => 0

theorem attCost_none (x y : Option (Vtx k)) : attCost k none x y = 0 := by
  cases x <;> cases y <;> rfl

/-- The cost of the attachment of a component. -/
noncomputable def BComp.att (C : BComp k) : ℕ := attCost k C.slot C.line.getLast? C.line.head?

/-- Rows, seam excess and attachment of a component. -/
noncomputable def BComp.cost (C : BComp k) : ℕ := lineCost C.line + C.att

/-- The components have no rotation class in common. -/
def LinesDisjoint (C D : BComp k) : Prop :=
  ∀ x ∈ C.line, ∀ y ∈ D.line, ¬ ((x : List ℕ) ~r (y : List ℕ))

instance : Std.Symm (LinesDisjoint (k := k)) :=
  ⟨fun _ _ h x hx y hy hr => h y hy x hx hr.symm⟩

/-- A valid block configuration. -/
structure BValid (cs : List (BComp k)) : Prop where
  line_ne : ∀ C ∈ cs, C.line ≠ []
  /-- the first component is the kernel, the others hang -/
  kernel : ∃ K Hs, cs = K :: Hs ∧ K.slot = none ∧ ∀ H ∈ Hs, H.slot ≠ none
  inner : ∀ C ∈ cs, C.line.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))
  outer : cs.Pairwise LinesDisjoint
  cover : ∀ v : Vtx k, ∃ C ∈ cs, ∃ e ∈ C.line, (v : List ℕ) ~r (e : List ℕ)
  slot : ∀ C ∈ cs, ∀ v, C.slot = some v → ∀ D ∈ cs, sigma v ∉ D.line
  slots : ∀ C ∈ cs, ∀ D ∈ cs, ∀ v, C.slot = some v → D.slot = some v → C = D
  forest : ∀ C ∈ cs, ∀ v, C.slot = some v → ∀ D ∈ cs,
    (∃ e ∈ D.line, (v : List ℕ) ~r (e : List ℕ)) → D.rank < C.rank

/-- The cost of a block configuration. -/
noncomputable def bcost (cs : List (BComp k)) : ℕ := (cs.map BComp.cost).sum

/-- No link of any line is of type T4. -/
def BNoT4 (cs : List (BComp k)) : Prop := ∀ C ∈ cs, LineNoT4 C.line

namespace BValid

variable {cs : List (BComp k)}

theorem chain (hk : 2 ≤ k) (hv : BValid cs) {C : BComp k} (hC : C ∈ cs) :
    C.line.IsChain (GoodLink k) :=
  (hv.inner C hC).isChain.imp (fun _ _ h => goodLink_of_not_isRotated hk h)

theorem nodup (hv : BValid cs) : cs.Nodup := by
  refine hv.outer.imp_of_mem ?_
  intro C D hC _ hd hCD
  obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (hv.line_ne C hC)
  have hmem : e ∈ C.line := by
    rw [he]
    exact List.mem_cons_self
  exact hd e hmem e (hCD ▸ hmem) (List.IsRotated.refl _)

theorem disjoint (hv : BValid cs) {C D : BComp k} (hC : C ∈ cs) (hD : D ∈ cs) (hne : C ≠ D) :
    LinesDisjoint C D :=
  hv.outer.forall hC hD hne

/-- Components with a common rotation class are equal. -/
theorem eq_of_common (hv : BValid cs) {C D : BComp k} (hC : C ∈ cs) (hD : D ∈ cs)
    {x y : Vtx k} (hx : x ∈ C.line) (hy : y ∈ D.line) (h : (x : List ℕ) ~r (y : List ℕ)) :
    C = D := by
  by_contra hne
  exact hv.disjoint hC hD hne x hx y hy h

end BValid

/-! ### From blocks to rows -/

/-- The hanging component of a block component with a vertex. -/
noncomputable def hangOf (C : BComp k) : Option (NHanging k) :=
  C.slot.map (fun v => ⟨groupRows C.line, v⟩)

/-- The standard configuration of a block configuration `K :: Hs`. -/
noncomputable def toConfig (K : BComp k) (Hs : List (BComp k)) : NConfig k :=
  ⟨groupRows K.line, Hs.filterMap hangOf⟩

theorem mem_toConfig_hanging {K : BComp k} {Hs : List (BComp k)} {H' : NHanging k} :
    H' ∈ (toConfig K Hs).hanging ↔
      ∃ H ∈ Hs, ∃ v, H.slot = some v ∧ H' = ⟨groupRows H.line, v⟩ := by
  show H' ∈ Hs.filterMap hangOf ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨H, hH, hh⟩
    unfold hangOf at hh
    obtain ⟨v, hv, hvH⟩ := Option.map_eq_some_iff.mp hh
    exact ⟨H, hH, v, hv, hvH.symm⟩
  · rintro ⟨H, hH, v, hv, rfl⟩
    refine ⟨H, hH, ?_⟩
    unfold hangOf
    rw [hv]
    rfl

theorem hang_cost (_hk : 2 ≤ k) {L : List (Vtx k)} (hL : L.IsChain (GoodLink k)) (hne : L ≠ [])
    (v : Vtx k) (r : ℕ) :
    NHanging.cost ⟨groupRows L, v⟩ = BComp.cost ⟨L, some v, r⟩ := by
  have hb := List.getLast?_eq_some_getLast hne
  have ha := List.head?_eq_some_head hne
  show rowsCost (groupRows L) +
      (NHanging.w0 ⟨groupRows L, v⟩ + NHanging.w1 ⟨groupRows L, v⟩ - 4) =
    lineCost L + attCost k (some v) L.getLast? L.head?
  rw [NHanging.w0_groupRows hL hb, NHanging.w1_groupRows hL ha, (groupRows_spec L hL).cost hne,
    hb, ha]
  rfl

theorem toConfig_entries (hk : 2 ≤ k) {K : BComp k} {Hs : List (BComp k)}
    (hv : BValid (K :: Hs)) (hs : ∀ H ∈ Hs, H.slot ≠ none) :
    (toConfig K Hs).entries = (K :: Hs).flatMap BComp.line := by
  have haux : ∀ Hs' : List (BComp k), (∀ H ∈ Hs', H ∈ K :: Hs) → (∀ H ∈ Hs', H.slot ≠ none) →
      (Hs'.filterMap hangOf).flatMap (fun H => rowsEntries H.rows) = Hs'.flatMap BComp.line := by
    intro Hs'
    induction Hs' with
    | nil => intro _ _; rfl
    | cons H Hs' ih =>
        intro hmem hsl
        obtain ⟨v, hslot⟩ := Option.ne_none_iff_exists'.mp (hsl H List.mem_cons_self)
        have hh : hangOf H = some ⟨groupRows H.line, v⟩ := by
          unfold hangOf
          rw [hslot]
          rfl
        rw [List.filterMap_cons_some hh, List.flatMap_cons, List.flatMap_cons,
          ih (fun H' h' => hmem H' (List.mem_cons_of_mem _ h'))
            (fun H' h' => hsl H' (List.mem_cons_of_mem _ h'))]
        show rowsEntries (groupRows H.line) ++ _ = _
        rw [(groupRows_spec _ (hv.chain hk (hmem H List.mem_cons_self))).entries]
  show rowsEntries (groupRows K.line) ++
      (Hs.filterMap hangOf).flatMap (fun H => rowsEntries H.rows) = _
  rw [(groupRows_spec _ (hv.chain hk List.mem_cons_self)).entries,
    haux Hs (fun H h => List.mem_cons_of_mem _ h) hs, List.flatMap_cons]

/-- **The cost is the same.** -/
theorem toConfig_cost (hk : 2 ≤ k) {K : BComp k} {Hs : List (BComp k)}
    (hv : BValid (K :: Hs)) (hK : K.slot = none) (hs : ∀ H ∈ Hs, H.slot ≠ none) :
    (toConfig K Hs).cost = bcost (K :: Hs) := by
  have haux : ∀ Hs' : List (BComp k), (∀ H ∈ Hs', H ∈ K :: Hs) → (∀ H ∈ Hs', H.slot ≠ none) →
      ((Hs'.filterMap hangOf).map NHanging.cost).sum = (Hs'.map BComp.cost).sum := by
    intro Hs'
    induction Hs' with
    | nil => intro _ _; rfl
    | cons H Hs' ih =>
        intro hmem hsl
        obtain ⟨v, hslot⟩ := Option.ne_none_iff_exists'.mp (hsl H List.mem_cons_self)
        have hh : hangOf H = some ⟨groupRows H.line, v⟩ := by
          unfold hangOf
          rw [hslot]
          rfl
        have hH := hmem H List.mem_cons_self
        have hc := hang_cost hk (hv.chain hk hH) (hv.line_ne H hH) v H.rank
        have hHeq : (⟨H.line, some v, H.rank⟩ : BComp k) = H := by
          rw [← hslot]
        rw [hHeq] at hc
        rw [List.filterMap_cons_some hh, List.map_cons, List.sum_cons, List.map_cons,
          List.sum_cons, hc, ih (fun H' h' => hmem H' (List.mem_cons_of_mem _ h'))
            (fun H' h' => hsl H' (List.mem_cons_of_mem _ h'))]
  have hKc : K.cost = lineCost K.line := by
    unfold BComp.cost BComp.att
    rw [hK, attCost_none]
    rfl
  show rowsCost (groupRows K.line) + ((Hs.filterMap hangOf).map NHanging.cost).sum = _
  rw [(groupRows_spec _ (hv.chain hk List.mem_cons_self)).cost (hv.line_ne K List.mem_cons_self),
    haux Hs (fun H h => List.mem_cons_of_mem _ h) hs]
  unfold bcost
  rw [List.map_cons, List.sum_cons, hKc]

theorem toConfig_forest (hk : 2 ≤ k) {K : BComp k} {Hs : List (BComp k)}
    (hv : BValid (K :: Hs)) (hs : ∀ H ∈ Hs, H.slot ≠ none) :
    ∀ (n : ℕ) (H : BComp k), H ∈ Hs → H.rank = n →
      Relation.TransGen (toConfig K Hs).HangsOn (groupRows H.line) (groupRows K.line) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hH hn
    obtain ⟨v, hslot⟩ := Option.ne_none_iff_exists'.mp (hs H hH)
    obtain ⟨D, hD, e, he, hrot⟩ := hv.cover v
    have hlt := hv.forest H (List.mem_cons_of_mem _ hH) v hslot D hD ⟨e, he, hrot⟩
    have hstep : (toConfig K Hs).HangsOn (groupRows H.line) (groupRows D.line) := by
      refine ⟨⟨groupRows H.line, v⟩, mem_toConfig_hanging.mpr ⟨H, hH, v, hslot, rfl⟩, rfl, e, ?_,
        hrot⟩
      rw [(groupRows_spec _ (hv.chain hk hD)).entries]
      exact he
    rcases List.mem_cons.mp hD with hDK | hDH
    · rw [hDK] at hstep
      exact Relation.TransGen.single hstep
    · exact Relation.TransGen.head hstep (ih _ (by omega) D hDH rfl)

/-- **A valid block configuration is a valid standard configuration.** -/
theorem toConfig_valid (hk : 2 ≤ k) {K : BComp k} {Hs : List (BComp k)}
    (hv : BValid (K :: Hs)) (hs : ∀ H ∈ Hs, H.slot ≠ none) : (toConfig K Hs).Valid := by
  have hS : ∀ C ∈ K :: Hs, GroupInv C.line (groupRows C.line) :=
    fun C hC => groupRows_spec _ (hv.chain hk hC)
  have hne : ∀ C ∈ K :: Hs, groupRows C.line ≠ [] := by
    intro C hC h
    have h1 := (hS C hC).entries
    rw [h] at h1
    exact hv.line_ne C hC h1.symm
  have hmemH : ∀ H ∈ Hs, H ∈ K :: Hs := fun H h => List.mem_cons_of_mem _ h
  have hE := toConfig_entries hk hv hs
  refine ⟨hne K List.mem_cons_self, ?_, (hS K List.mem_cons_self).len, ?_,
    (hS K List.mem_cons_self).seams, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H' hH'
    obtain ⟨H, hH, v, _, rfl⟩ := mem_toConfig_hanging.mp hH'
    exact hne H (hmemH H hH)
  · intro H' hH'
    obtain ⟨H, hH, v, _, rfl⟩ := mem_toConfig_hanging.mp hH'
    exact (hS H (hmemH H hH)).len
  · intro H' hH'
    obtain ⟨H, hH, v, _, rfl⟩ := mem_toConfig_hanging.mp hH'
    exact (hS H (hmemH H hH)).seams
  · rw [hE, List.pairwise_flatMap]
    exact ⟨hv.inner, hv.outer⟩
  · intro v
    obtain ⟨C, hC, e, he, hrot⟩ := hv.cover v
    refine ⟨e, ?_, hrot⟩
    rw [hE]
    exact List.mem_flatMap.mpr ⟨C, hC, he⟩
  · intro H' hH'
    obtain ⟨H, hH, v, hslot, rfl⟩ := mem_toConfig_hanging.mp hH'
    rw [hE]
    intro hmem
    obtain ⟨D, hD, hDm⟩ := List.mem_flatMap.mp hmem
    exact hv.slot H (hmemH H hH) v hslot D hD hDm
  · show ((Hs.filterMap hangOf).map NHanging.slot).Nodup
    unfold List.Nodup
    rw [List.pairwise_map, List.pairwise_filterMap]
    have hnd : Hs.Nodup := (List.nodup_cons.mp hv.nodup).2
    refine hnd.pairwise_of_forall_ne ?_
    intro H hH H' hH' hneq b hb b' hb' hbb
    unfold hangOf at hb hb'
    obtain ⟨v, hv1, hvb⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨v', hv1', hvb'⟩ := Option.map_eq_some_iff.mp hb'
    rw [← hvb, ← hvb'] at hbb
    have hvv : v = v' := hbb
    rw [← hvv] at hv1'
    exact hneq (hv.slots H (hmemH H hH) H' (hmemH H' hH') v hv1 hv1')
  · intro H' hH'
    obtain ⟨H, hH, v, hslot, rfl⟩ := mem_toConfig_hanging.mp hH'
    have hHm := hmemH H hH
    have hb := List.getLast?_eq_some_getLast (hv.line_ne H hHm)
    show 2 ≤ NHanging.w0 ⟨groupRows H.line, v⟩
    rw [NHanging.w0_groupRows (hv.chain hk hHm) hb]
    have h1 := Hunter.ProofsExitless.ew_ge_one (by omega : 1 ≤ k)
      (sigmaInv (H.line.getLast (hv.line_ne H hHm))) (sigma v)
    have hne1 : ew k (sigmaInv (H.line.getLast (hv.line_ne H hHm))) (sigma v) ≠ 1 := by
      intro hone
      have h := (Hunter.ProofsExitless.ew_eq_one_iff (by omega : 1 ≤ k)).mp hone
      rw [Hunter.ProofsStructure.sigma_sigmaInv] at h
      apply hv.slot H hHm v hslot H hHm
      rw [h]
      exact List.getLast_mem _
    omega
  · intro H' hH'
    obtain ⟨H, hH, v, hslot, rfl⟩ := mem_toConfig_hanging.mp hH'
    have hHm := hmemH H hH
    have ha := List.head?_eq_some_head (hv.line_ne H hHm)
    show 2 ≤ NHanging.w1 ⟨groupRows H.line, v⟩
    rw [NHanging.w1_groupRows (hv.chain hk hHm) ha]
    have h1 := Hunter.ProofsExitless.ew_ge_one (by omega : 1 ≤ k) v
      (H.line.head (hv.line_ne H hHm))
    have hne1 : ew k v (H.line.head (hv.line_ne H hHm)) ≠ 1 := by
      intro hone
      have h := (Hunter.ProofsExitless.ew_eq_one_iff (by omega : 1 ≤ k)).mp hone
      apply hv.slot H hHm v hslot H hHm
      rw [← h]
      exact List.head_mem _
    omega
  · intro H' hH'
    obtain ⟨H, hH, v, _, rfl⟩ := mem_toConfig_hanging.mp hH'
    exact toConfig_forest hk hv hs _ H hH rfl

/-- **No link of type T4 gives no seam of type T4.** -/
theorem toConfig_noT4 (hk : 2 ≤ k) {K : BComp k} {Hs : List (BComp k)}
    (hv : BValid (K :: Hs)) (ht : BNoT4 (K :: Hs)) : (toConfig K Hs).NoT4 := by
  refine ⟨groupRows_noT4 _ (hv.chain hk List.mem_cons_self) (ht K List.mem_cons_self), ?_⟩
  intro H' hH'
  obtain ⟨H, hH, v, _, rfl⟩ := mem_toConfig_hanging.mp hH'
  exact groupRows_noT4 _ (hv.chain hk (List.mem_cons_of_mem _ hH))
    (ht H (List.mem_cons_of_mem _ hH))

/-! ### The block configuration of Theorem N -/

namespace JoinData

variable {X : Type} [Fintype X] [DecidableEq X] (J : JoinData k X)

/-- The component made of the orbit of a representative. -/
noncomputable def bcomp (R : X) : BComp k :=
  ⟨J.newLine R, if R = J.root then none else some (J.slot R), if R = J.root then 0 else J.t R + 1⟩

/-- The block configuration of Theorem N: the kernel first. -/
noncomputable def bcomps : List (BComp k) := J.reps.map J.bcomp

theorem mem_bcomps {C : BComp k} : C ∈ J.bcomps ↔ ∃ R ∈ J.reps, C = J.bcomp R := by
  unfold bcomps
  rw [List.mem_map]
  exact ⟨fun ⟨R, hR, h⟩ => ⟨R, hR, h.symm⟩, fun ⟨R, hR, h⟩ => ⟨R, hR, h.symm⟩⟩

theorem bcomp_slot_some {R : X} {v : Vtx k} (h : (J.bcomp R).slot = some v) :
    R ≠ J.root ∧ v = J.slot R := by
  by_cases hR : R = J.root
  · exfalso
    have h1 : (J.bcomp R).slot = none := if_pos hR
    rw [h1] at h
    exact absurd h (by simp)
  · have h1 : (J.bcomp R).slot = some (J.slot R) := if_neg hR
    rw [h1] at h
    exact ⟨hR, (Option.some.inj h).symm⟩

theorem reps_disjoint {R R' : X} (hR : R ∈ J.reps) (hR' : R' ∈ J.reps) {C : X}
    (hC : C ∈ J.orbitList R) (hC' : C ∈ J.orbitList R') : R = R' := by
  have h1 : J.rep C = R := (J.rep_of_mem hC).trans (J.rep_of_mem_reps hR)
  have h2 : J.rep C = R' := (J.rep_of_mem hC').trans (J.rep_of_mem_reps hR')
  exact h1.symm.trans h2

theorem bcomps_valid : BValid J.bcomps := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨R, _, rfl⟩ := J.mem_bcomps.mp hC
    exact J.newLine_ne R
  · refine ⟨J.bcomp J.root, J.hangReps.map J.bcomp, rfl, if_pos rfl, ?_⟩
    intro H hH
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hH
    have hne := (J.mem_hangReps.mp hR).2
    have h1 : (J.bcomp R).slot = some (J.slot R) := if_neg hne
    rw [h1]
    simp
  · intro C hC
    obtain ⟨R, _, rfl⟩ := J.mem_bcomps.mp hC
    exact J.newLine_pairwise R
  · unfold bcomps
    rw [List.pairwise_map]
    have hnd : J.reps.Pairwise (· ≠ ·) := J.reps_nodup
    refine hnd.imp_of_mem ?_
    intro R R' hR hR' hne x hx y hy hrot
    obtain ⟨C, hC, hxC⟩ := List.mem_flatMap.mp hx
    obtain ⟨D, hD, hyD⟩ := List.mem_flatMap.mp hy
    have hCD : C = D := by
      by_contra hcd
      exact J.disjoint C D hcd x hxC y hyD hrot
    rw [← hCD] at hD
    exact hne (J.reps_disjoint hR hR' hC hD)
  · intro v
    obtain ⟨C, e, he, hrot⟩ := J.cover v
    exact ⟨J.bcomp (J.rep C), J.mem_bcomps.mpr ⟨_, J.rep_mem_reps C, rfl⟩, e,
      List.mem_flatMap.mpr ⟨C, J.mem_orbitList_rep C, he⟩, hrot⟩
  · intro C hC v hv D hD hmem
    obtain ⟨R, _, rfl⟩ := J.mem_bcomps.mp hC
    obtain ⟨R', _, rfl⟩ := J.mem_bcomps.mp hD
    obtain ⟨hR, rfl⟩ := J.bcomp_slot_some hv
    obtain ⟨E, _, hE⟩ := List.mem_flatMap.mp hmem
    exact J.slot_ne R hR E hE
  · intro C hC D hD v hv hv'
    obtain ⟨R, _, rfl⟩ := J.mem_bcomps.mp hC
    obtain ⟨R', _, rfl⟩ := J.mem_bcomps.mp hD
    obtain ⟨hR, h1⟩ := J.bcomp_slot_some hv
    obtain ⟨hR', h2⟩ := J.bcomp_slot_some hv'
    rw [J.slot_inj R R' hR hR' (h1.symm.trans h2)]
  · intro C hC v hv D hD hex
    obtain ⟨R, hRr, rfl⟩ := J.mem_bcomps.mp hC
    obtain ⟨R', hR'r, rfl⟩ := J.mem_bcomps.mp hD
    obtain ⟨hR, rfl⟩ := J.bcomp_slot_some hv
    obtain ⟨e, he, hrot⟩ := hex
    obtain ⟨E, hE, heE⟩ := List.mem_flatMap.mp he
    obtain ⟨e', he', hrot'⟩ := J.par_mem R hR
    -- the class of the slot lies in `par R` and in `E`
    have hEpar : E = J.par R := by
      by_contra hne
      exact J.disjoint E (J.par R) hne e heE e' he' (hrot.symm.trans hrot')
    rw [hEpar] at hE
    have hR'eq : R' = J.rep (J.par R) :=
      ((J.rep_of_mem hE).trans (J.rep_of_mem_reps hR'r)).symm
    have hlt := J.par_lt R hR
    show (if R' = J.root then 0 else J.t R' + 1) < (if R = J.root then 0 else J.t R + 1)
    rw [if_neg hR]
    by_cases hroot : R' = J.root
    · rw [if_pos hroot]
      omega
    · rw [if_neg hroot]
      have hnr : J.root ∉ J.orbitList (J.par R) := by
        intro h
        apply hroot
        rw [hR'eq]
        exact J.rep_eq_root h
      have hle : J.t (J.rep (J.par R)) ≤ J.t (J.par R) :=
        J.t_rep_le hnr (J.self_mem_orbitList _)
      rw [hR'eq]
      omega

theorem bcomp_cost_le (hk : 2 ≤ k) {R : X} (hR : R ∈ J.reps) :
    (J.bcomp R).cost ≤ ((J.orbitList R).map J.charge).sum := by
  have h := J.newLine_cost_le hk hR
  unfold BComp.cost BComp.att
  show lineCost (J.newLine R) +
      attCost k (if R = J.root then none else some (J.slot R)) (J.newLine R).getLast?
        (J.newLine R).head? ≤ _
  rw [J.newLine_last R, J.newLine_head R]
  by_cases hroot : R = J.root
  · rw [if_pos hroot] at h ⊢
    have h0 : attCost k none (some (J.lst (J.nxt.symm R))) (some (J.fst R)) = 0 := rfl
    rw [h0]
    exact h
  · rw [if_neg hroot] at h ⊢
    have hatt := J.att R hroot
    have h0 : attCost k (some (J.slot R)) (some (J.lst (J.nxt.symm R))) (some (J.fst R)) =
        ew k (sigmaInv (J.lst (J.nxt.symm R))) (sigma (J.slot R)) + ew k (J.slot R) (J.fst R) - 4 :=
      rfl
    rw [h0]
    omega

/-- The cost of the block configuration of Theorem N. -/
theorem bcomps_cost_le (hk : 2 ≤ k) : bcost J.bcomps ≤ ∑ C : X, J.charge C := by
  have hsum : ∑ C : X, J.charge C = (J.allList.map J.charge).sum := by
    rw [← List.sum_toFinset _ J.allList_nodup]
    congr 1
    exact (Finset.eq_univ_of_forall (fun C => List.mem_toFinset.mpr (J.mem_allList C))).symm
  rw [hsum]
  unfold allList bcost bcomps
  rw [sum_flatMap_map, List.map_map]
  apply List.sum_le_sum
  intro R hR
  exact J.bcomp_cost_le hk hR

end JoinData

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.tau_ne_sigma_tau2V
#print axioms SuperpermLowerBounds.toConfig_valid
#print axioms SuperpermLowerBounds.toConfig_cost
#print axioms SuperpermLowerBounds.toConfig_noT4
#print axioms SuperpermLowerBounds.JoinData.bcomps_valid
#print axioms SuperpermLowerBounds.JoinData.bcomps_cost_le

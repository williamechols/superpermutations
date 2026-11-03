import LowerBounds.NConfig

/-!
# Theorem N of the written model, the combinatorial part

No Hamiltonian path occurs in this file.  `JoinData k X` is what the canonical certificate of a
path provides (`NPath.lean` constructs it): a finite set `X` of components, each with a line of
blocks; a permutation `nxt` of `X` (the junctions, completed by "last component ↦ root"); for
every component `C` other than the root the cost `jin C` of the junction into `C`, its last slot
`slot C`, and the component `par C` that contains this slot; and a time `t` (when the path
reaches the tail of `C`) with `t (par C) < t C`.

From it `JoinData.config` builds a standard configuration:

* the components on one orbit of `nxt` are joined in the order of the orbit into one component;
  the orbit of the root starts at the root and is the kernel; every other orbit starts at its
  component of least `t` and is a hanging component, attached at the slot of that component;
* `config_valid`: the result is a valid standard configuration (coverage, slot rule, forest);
* `config_cost_le`: its cost is at most the sum of the costs of the lines and of the junctions.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped BigOperators

variable {k : ℕ}

/-- The data of a canonical certificate that Theorem N uses. -/
structure JoinData (k : ℕ) (X : Type) [Fintype X] [DecidableEq X] where
  /-- the block entries of a component, in order -/
  line : X → List (Vtx k)
  /-- the first block entry (the tail of the component) -/
  fst : X → Vtx k
  /-- the last block entry (`σ⁻¹` of it is the head of the component) -/
  lst : X → Vtx k
  /-- the root component -/
  root : X
  /-- the target of the junction that leaves a component; the last component goes to the root -/
  nxt : Equiv.Perm X
  /-- the time at which the tail is reached -/
  t : X → ℕ
  /-- the last slot of the junction into a component -/
  slot : X → Vtx k
  /-- the component that contains this slot -/
  par : X → X
  /-- the cost of the junction into a component -/
  jin : X → ℕ
  head_line : ∀ C, (line C).head? = some (fst C)
  last_line : ∀ C, (line C).getLast? = some (lst C)
  cover : ∀ v : Vtx k, ∃ C, ∃ e ∈ line C, (v : List ℕ) ~r (e : List ℕ)
  distinct : ∀ C, (line C).Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))
  disjoint : ∀ C D, C ≠ D → ∀ a ∈ line C, ∀ b ∈ line D, ¬ ((a : List ℕ) ~r (b : List ℕ))
  /-- Lemma 2 for a junction: head of the source to tail of the target -/
  link : ∀ C, nxt C ≠ root → ew k (sigmaInv (lst C)) (fst (nxt C)) ≤ jin (nxt C) + 3
  /-- a slot is not the exit of its block -/
  slot_ne : ∀ C, C ≠ root → ∀ D, sigma (slot C) ∉ line D
  /-- different junctions end at different slots -/
  slot_inj : ∀ C D, C ≠ root → D ≠ root → slot C = slot D → C = D
  /-- Lemma 2 for the attachment at the last slot -/
  att : ∀ C, C ≠ root →
    ew k (sigmaInv (lst (nxt.symm C))) (sigma (slot C)) + ew k (slot C) (fst C) ≤ jin C + 4
  par_mem : ∀ C, C ≠ root → ∃ e ∈ line (par C), ((slot C : Vtx k) : List ℕ) ~r (e : List ℕ)
  par_lt : ∀ C, C ≠ root → t (par C) < t C

namespace JoinData

variable {X : Type} [Fintype X] [DecidableEq X] (J : JoinData k X)

theorem fst_mem (C : X) : J.fst C ∈ J.line C := by
  obtain ⟨ys, h⟩ := List.head?_eq_some_iff.mp (J.head_line C)
  rw [h]
  exact List.mem_cons_self

theorem lst_mem (C : X) : J.lst C ∈ J.line C := by
  obtain ⟨ys, h⟩ := List.getLast?_eq_some_iff.mp (J.last_line C)
  rw [h]
  simp

theorem w0_ge (hk : 1 ≤ k) {C : X} (hC : C ≠ J.root) :
    2 ≤ ew k (sigmaInv (J.lst (J.nxt.symm C))) (sigma (J.slot C)) := by
  have h1 := Hunter.ProofsExitless.ew_ge_one hk (sigmaInv (J.lst (J.nxt.symm C)))
    (sigma (J.slot C))
  have hne : ew k (sigmaInv (J.lst (J.nxt.symm C))) (sigma (J.slot C)) ≠ 1 := by
    intro hone
    have h := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    rw [Hunter.ProofsStructure.sigma_sigmaInv] at h
    have hmem : sigma (J.slot C) ∈ J.line (J.nxt.symm C) := by
      rw [h]
      exact J.lst_mem _
    exact J.slot_ne C hC _ hmem
  omega

theorem w1_ge (hk : 1 ≤ k) {C : X} (hC : C ≠ J.root) : 2 ≤ ew k (J.slot C) (J.fst C) := by
  have h1 := Hunter.ProofsExitless.ew_ge_one hk (J.slot C) (J.fst C)
  have hne : ew k (J.slot C) (J.fst C) ≠ 1 := by
    intro hone
    have h := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    have hmem : sigma (J.slot C) ∈ J.line C := by
      rw [← h]
      exact J.fst_mem _
    exact J.slot_ne C hC _ hmem
  omega

/-! ### Orbits of the junction permutation -/

/-- The length of the orbit of a component. -/
noncomputable def per (C : X) : ℕ := Function.minimalPeriod J.nxt C

theorem mem_periodicPts (C : X) : C ∈ Function.periodicPts J.nxt := by
  have h : (⇑J.nxt)^[orderOf J.nxt] C = C := by
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  exact Function.mk_mem_periodicPts (orderOf_pos J.nxt) h

theorem per_pos (C : X) : 0 < J.per C :=
  Function.minimalPeriod_pos_of_mem_periodicPts (J.mem_periodicPts C)

theorem iterate_per (C : X) : (⇑J.nxt)^[J.per C] C = C := Function.iterate_minimalPeriod

/-- The orbit of a component, in order, starting with the component. -/
noncomputable def orbitList (C : X) : List X :=
  (List.range (J.per C)).map (fun i => (⇑J.nxt)^[i] C)

theorem mem_orbitList {C D : X} : D ∈ J.orbitList C ↔ ∃ n, (⇑J.nxt)^[n] C = D := by
  unfold orbitList
  rw [List.mem_map]
  constructor
  · rintro ⟨i, _, h⟩
    exact ⟨i, h⟩
  · rintro ⟨n, h⟩
    refine ⟨n % J.per C, List.mem_range.mpr (Nat.mod_lt _ (J.per_pos C)), ?_⟩
    rw [← h]
    exact Function.iterate_mod_minimalPeriod_eq

theorem self_mem_orbitList (C : X) : C ∈ J.orbitList C := J.mem_orbitList.mpr ⟨0, rfl⟩

theorem orbitList_nodup (C : X) : (J.orbitList C).Nodup := by
  unfold orbitList
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj h
  exact Function.iterate_injOn_Iio_minimalPeriod (f := ⇑J.nxt) (x := C)
    (Set.mem_Iio.mpr (List.mem_range.mp hi)) (Set.mem_Iio.mpr (List.mem_range.mp hj)) h

theorem mem_orbitList_symm {C D : X} (h : D ∈ J.orbitList C) : C ∈ J.orbitList D := by
  unfold orbitList at h
  obtain ⟨i, hi, hD⟩ := List.mem_map.mp h
  have hi' : i < J.per C := List.mem_range.mp hi
  refine J.mem_orbitList.mpr ⟨J.per C - i, ?_⟩
  rw [← hD]
  show (⇑J.nxt)^[J.per C - i] ((⇑J.nxt)^[i] C) = C
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hi')]
  exact J.iterate_per C

theorem mem_orbitList_trans {C D E : X} (h1 : D ∈ J.orbitList C) (h2 : E ∈ J.orbitList D) :
    E ∈ J.orbitList C := by
  obtain ⟨n, rfl⟩ := J.mem_orbitList.mp h1
  obtain ⟨m, rfl⟩ := J.mem_orbitList.mp h2
  exact J.mem_orbitList.mpr ⟨m + n, Function.iterate_add_apply _ _ _ _⟩

theorem orbitList_head (C : X) : (J.orbitList C).head? = some C := by
  unfold orbitList
  rw [List.head?_map, List.head?_range, if_neg (Nat.pos_iff_ne_zero.mp (J.per_pos C))]
  rfl

theorem orbitList_last (C : X) : (J.orbitList C).getLast? = some (J.nxt.symm C) := by
  have hp := J.per_pos C
  have h := J.iterate_per C
  unfold orbitList
  rw [List.getLast?_map, List.getLast?_range, if_neg (Nat.pos_iff_ne_zero.mp hp)]
  show some ((⇑J.nxt)^[J.per C - 1] C) = some (J.nxt.symm C)
  congr 1
  rw [Equiv.eq_symm_apply]
  obtain ⟨m, hm⟩ : ∃ m, J.per C = m + 1 := ⟨J.per C - 1, by omega⟩
  rw [hm] at h ⊢
  rw [Nat.add_sub_cancel]
  rw [Function.iterate_succ_apply'] at h
  exact h

/-! ### Representatives -/

/-- The orbit as a set. -/
noncomputable def orb (C : X) : Finset X := (J.orbitList C).toFinset

theorem mem_orb {C D : X} : D ∈ J.orb C ↔ D ∈ J.orbitList C := List.mem_toFinset

theorem orb_eq_of_mem {C D : X} (h : D ∈ J.orbitList C) : J.orb D = J.orb C := by
  ext E
  rw [mem_orb, mem_orb]
  exact ⟨fun hE => J.mem_orbitList_trans h hE,
    fun hE => J.mem_orbitList_trans (J.mem_orbitList_symm h) hE⟩

/-- The component an orbit starts with: the root if it is there, else one of least `t`. -/
noncomputable def pick (S : Finset X) : X :=
  if J.root ∈ S then J.root
  else if hne : S.Nonempty then Classical.choose (S.exists_min_image J.t hne) else J.root

theorem pick_mem {S : Finset X} (hne : S.Nonempty) : J.pick S ∈ S := by
  unfold pick
  split_ifs with h
  · exact h
  · exact (Classical.choose_spec (S.exists_min_image J.t hne)).1

theorem t_pick_le {S : Finset X} (hroot : J.root ∉ S) {D : X} (hD : D ∈ S) :
    J.t (J.pick S) ≤ J.t D := by
  have hne : S.Nonempty := ⟨D, hD⟩
  unfold pick
  rw [if_neg hroot, dif_pos hne]
  exact (Classical.choose_spec (S.exists_min_image J.t hne)).2 D hD

/-- The representative of the orbit of a component. -/
noncomputable def rep (C : X) : X := J.pick (J.orb C)

theorem rep_mem (C : X) : J.rep C ∈ J.orbitList C :=
  J.mem_orb.mp (J.pick_mem ⟨C, J.mem_orb.mpr (J.self_mem_orbitList C)⟩)

theorem rep_of_mem {C D : X} (h : D ∈ J.orbitList C) : J.rep D = J.rep C := by
  unfold rep
  rw [J.orb_eq_of_mem h]

theorem rep_rep (C : X) : J.rep (J.rep C) = J.rep C := J.rep_of_mem (J.rep_mem C)

theorem rep_eq_root {C : X} (h : J.root ∈ J.orbitList C) : J.rep C = J.root := by
  unfold rep pick
  rw [if_pos (J.mem_orb.mpr h)]

theorem rep_root : J.rep J.root = J.root := J.rep_eq_root (J.self_mem_orbitList _)

theorem mem_orbitList_rep (C : X) : C ∈ J.orbitList (J.rep C) :=
  J.mem_orbitList_symm (J.rep_mem C)

theorem t_rep_le {C D : X} (hroot : J.root ∉ J.orbitList C) (hD : D ∈ J.orbitList C) :
    J.t (J.rep C) ≤ J.t D :=
  J.t_pick_le (fun h => hroot (J.mem_orb.mp h)) (J.mem_orb.mpr hD)

/-- The representatives of the orbits that do not contain the root. -/
noncomputable def hangReps : List X :=
  (Finset.univ.filter (fun R => J.rep R = R ∧ R ≠ J.root)).toList

theorem mem_hangReps {R : X} : R ∈ J.hangReps ↔ J.rep R = R ∧ R ≠ J.root := by
  unfold hangReps
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- All representatives, the root first. -/
noncomputable def reps : List X := J.root :: J.hangReps

theorem rep_of_mem_reps {R : X} (h : R ∈ J.reps) : J.rep R = R := by
  rcases List.mem_cons.mp h with h | h
  · rw [h]
    exact J.rep_root
  · exact (J.mem_hangReps.mp h).1

theorem rep_mem_reps (C : X) : J.rep C ∈ J.reps := by
  by_cases h : J.rep C = J.root
  · rw [h]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (J.mem_hangReps.mpr ⟨J.rep_rep C, h⟩)

theorem reps_nodup : J.reps.Nodup := by
  unfold reps
  rw [List.nodup_cons]
  exact ⟨fun h => (J.mem_hangReps.mp h).2 rfl, Finset.nodup_toList _⟩

theorem root_not_mem_of_hang {R : X} (h : R ∈ J.hangReps) : J.root ∉ J.orbitList R := by
  intro hr
  have h1 := J.rep_eq_root hr
  rw [(J.mem_hangReps.mp h).1] at h1
  exact (J.mem_hangReps.mp h).2 h1

/-- All components, orbit after orbit. -/
noncomputable def allList : List X := J.reps.flatMap J.orbitList

theorem mem_allList (C : X) : C ∈ J.allList :=
  List.mem_flatMap.mpr ⟨J.rep C, J.rep_mem_reps C, J.mem_orbitList_rep C⟩

theorem allList_nodup : J.allList.Nodup := by
  unfold allList
  rw [List.nodup_flatMap]
  refine ⟨fun R _ => J.orbitList_nodup R, ?_⟩
  have hnd : J.reps.Pairwise (· ≠ ·) := J.reps_nodup
  refine hnd.imp_of_mem ?_
  intro R R' hR hR' hne
  show ∀ ⦃C : X⦄, C ∈ J.orbitList R → C ∈ J.orbitList R' → False
  intro C hC hC'
  have h1 : J.rep C = R := (J.rep_of_mem hC).trans (J.rep_of_mem_reps hR)
  have h2 : J.rep C = R' := (J.rep_of_mem hC').trans (J.rep_of_mem_reps hR')
  exact hne (h1.symm.trans h2)

/-! ### The joined lines -/

/-- The line of the component made of an orbit: the lines of its components one after the
other. -/
noncomputable def newLine (R : X) : List (Vtx k) := (J.orbitList R).flatMap J.line

theorem pairwise_flatMap_line {l : List X} (hl : l.Nodup) :
    (l.flatMap J.line).Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun C _ => J.distinct C, ?_⟩
  have hnd : l.Pairwise (· ≠ ·) := hl
  exact hnd.imp (fun {C D} hne a ha b hb => J.disjoint C D hne a ha b hb)

theorem newLine_pairwise (R : X) :
    (J.newLine R).Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ))) :=
  J.pairwise_flatMap_line (J.orbitList_nodup R)

theorem newLine_chain (hk : 2 ≤ k) (R : X) : (J.newLine R).IsChain (GoodLink k) :=
  (J.newLine_pairwise R).isChain.imp (fun _ _ h => goodLink_of_not_isRotated hk h)

theorem newLine_head (R : X) : (J.newLine R).head? = some (J.fst R) := by
  obtain ⟨ys, h⟩ := List.head?_eq_some_iff.mp (J.orbitList_head R)
  unfold newLine
  rw [h, List.flatMap_cons, List.head?_append, J.head_line]
  rfl

theorem newLine_last (R : X) : (J.newLine R).getLast? = some (J.lst (J.nxt.symm R)) := by
  obtain ⟨ys, h⟩ := List.getLast?_eq_some_iff.mp (J.orbitList_last R)
  unfold newLine
  rw [h, List.flatMap_append, List.flatMap_singleton, List.getLast?_append, J.last_line]
  rfl

theorem newLine_ne (R : X) : J.newLine R ≠ [] := by
  intro h
  have h1 := J.newLine_head R
  rw [h] at h1
  simp at h1

theorem groupInv (hk : 2 ≤ k) (R : X) : GroupInv (J.newLine R) (groupRows (J.newLine R)) :=
  groupRows_spec _ (J.newLine_chain hk R)

/-! ### The configuration -/

/-- The hanging component made of the orbit of `R`, attached at the last slot of the junction
into `R`. -/
noncomputable def hang (R : X) : NHanging k := ⟨groupRows (J.newLine R), J.slot R⟩

/-- The standard configuration of Theorem N. -/
noncomputable def config : NConfig k where
  kernel := groupRows (J.newLine J.root)
  hanging := J.hangReps.map J.hang

theorem config_entries (hk : 2 ≤ k) : J.config.entries = J.allList.flatMap J.line := by
  have hE : ∀ R, rowsEntries (groupRows (J.newLine R)) = J.newLine R :=
    fun R => (J.groupInv hk R).entries
  have h1 : ∀ l : List X, (l.map J.hang).flatMap (fun H => rowsEntries H.rows) =
      l.flatMap J.newLine := by
    intro l
    induction l with
    | nil => rfl
    | cons R l ih =>
        rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]
        show rowsEntries (groupRows (J.newLine R)) ++ _ = _
        rw [hE]
  show rowsEntries (groupRows (J.newLine J.root)) ++
      (J.hangReps.map J.hang).flatMap (fun H => rowsEntries H.rows) =
    ((J.root :: J.hangReps).flatMap J.orbitList).flatMap J.line
  rw [hE, h1, List.flatMap_assoc, List.flatMap_cons]
  rfl

theorem forest_aux (hk : 2 ≤ k) : ∀ (n : ℕ) (R : X), R ∈ J.hangReps → J.t R = n →
    Relation.TransGen J.config.HangsOn (groupRows (J.newLine R))
      (groupRows (J.newLine J.root)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R hR hn
    have hRne := (J.mem_hangReps.mp hR).2
    obtain ⟨e, he, hrot⟩ := J.par_mem R hRne
    have hstep : J.config.HangsOn (groupRows (J.newLine R))
        (groupRows (J.newLine (J.rep (J.par R)))) := by
      refine ⟨J.hang R, List.mem_map.mpr ⟨R, hR, rfl⟩, rfl, e, ?_, hrot⟩
      rw [(J.groupInv hk _).entries]
      exact List.mem_flatMap.mpr ⟨J.par R, J.mem_orbitList_rep _, he⟩
    by_cases hroot : J.rep (J.par R) = J.root
    · rw [hroot] at hstep
      exact Relation.TransGen.single hstep
    · have hR' : J.rep (J.par R) ∈ J.hangReps := J.mem_hangReps.mpr ⟨J.rep_rep _, hroot⟩
      have hnr : J.root ∉ J.orbitList (J.par R) := fun h => hroot (J.rep_eq_root h)
      have hle : J.t (J.rep (J.par R)) ≤ J.t (J.par R) :=
        J.t_rep_le hnr (J.self_mem_orbitList _)
      have hlt := J.par_lt R hRne
      exact Relation.TransGen.head hstep (ih _ (by omega) _ hR' rfl)

/-- **Theorem N, validity.**  The configuration is a valid standard configuration. -/
theorem config_valid (hk : 2 ≤ k) : J.config.Valid := by
  have hS := J.groupInv hk
  have hne : ∀ R, groupRows (J.newLine R) ≠ [] := by
    intro R h
    have h1 := (hS R).entries
    rw [h] at h1
    exact J.newLine_ne R h1.symm
  have hmem : ∀ H ∈ J.config.hanging, ∃ R ∈ J.hangReps, H = J.hang R := by
    intro H hH
    obtain ⟨R, hR, hRH⟩ := List.mem_map.mp hH
    exact ⟨R, hR, hRH.symm⟩
  refine ⟨hne J.root, ?_, (hS J.root).len, ?_, (hS J.root).seams, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨R, _, rfl⟩ := hmem H hH
    exact hne R
  · intro H hH
    obtain ⟨R, _, rfl⟩ := hmem H hH
    exact (hS R).len
  · intro H hH
    obtain ⟨R, _, rfl⟩ := hmem H hH
    exact (hS R).seams
  · rw [J.config_entries hk]
    exact J.pairwise_flatMap_line J.allList_nodup
  · intro v
    obtain ⟨C, e, he, hv⟩ := J.cover v
    refine ⟨e, ?_, hv⟩
    rw [J.config_entries hk]
    exact List.mem_flatMap.mpr ⟨C, J.mem_allList C, he⟩
  · intro H hH
    obtain ⟨R, hR, rfl⟩ := hmem H hH
    rw [J.config_entries hk]
    intro hmem'
    obtain ⟨D, _, hD⟩ := List.mem_flatMap.mp hmem'
    exact J.slot_ne R (J.mem_hangReps.mp hR).2 D hD
  · show ((J.hangReps.map J.hang).map NHanging.slot).Nodup
    rw [List.map_map]
    have hnd : J.hangReps.Nodup := Finset.nodup_toList _
    refine List.Nodup.map_on ?_ hnd
    intro R hR R' hR' h
    exact J.slot_inj R R' (J.mem_hangReps.mp hR).2 (J.mem_hangReps.mp hR').2 h
  · intro H hH
    obtain ⟨R, hR, rfl⟩ := hmem H hH
    show 2 ≤ NHanging.w0 ⟨groupRows (J.newLine R), J.slot R⟩
    rw [NHanging.w0_groupRows (J.newLine_chain hk R) (J.newLine_last R)]
    exact J.w0_ge (by omega) (J.mem_hangReps.mp hR).2
  · intro H hH
    obtain ⟨R, hR, rfl⟩ := hmem H hH
    show 2 ≤ NHanging.w1 ⟨groupRows (J.newLine R), J.slot R⟩
    rw [NHanging.w1_groupRows (J.newLine_chain hk R) (J.newLine_head R)]
    exact J.w1_ge (by omega) (J.mem_hangReps.mp hR).2
  · intro H hH
    obtain ⟨R, hR, rfl⟩ := hmem H hH
    exact J.forest_aux hk _ R hR rfl

/-! ### The cost -/

/-- Joining lines along junctions: every junction adds at most its cost. -/
theorem lineCost_flatMap_le : ∀ (Cs : List X), Cs ≠ [] →
    Cs.IsChain (fun C C' => 2 ≤ ew k (sigmaInv (J.lst C)) (J.fst C') ∧
      ew k (sigmaInv (J.lst C)) (J.fst C') ≤ J.jin C' + 3) →
    lineCost (Cs.flatMap J.line) ≤
      (Cs.map (fun C => lineCost (J.line C))).sum + (Cs.tail.map J.jin).sum
  | [], h, _ => absurd rfl h
  | [C], _, _ => by simp
  | C :: C' :: rest, _, hc => by
      rw [List.isChain_cons_cons] at hc
      have ih := lineCost_flatMap_le (C' :: rest) (List.cons_ne_nil _ _) hc.2
      have hhead : ((C' :: rest).flatMap J.line).head? = some (J.fst C') := by
        rw [List.flatMap_cons, List.head?_append, J.head_line]
        rfl
      have happ := linkSum_append (J.line C) ((C' :: rest).flatMap J.line) _ _
        (J.last_line C) hhead
      have e1 : (C :: C' :: rest).flatMap J.line =
          J.line C ++ (C' :: rest).flatMap J.line := List.flatMap_cons
      have h2 := hc.1.1
      have h3 := hc.1.2
      rw [e1]
      unfold lineCost at ih ⊢
      rw [happ]
      simp only [List.map_cons, List.sum_cons, List.tail_cons] at ih ⊢
      omega

/-- Along the orbit of a representative every step is a junction, with Lemma 2. -/
theorem orbitList_chain (hk : 2 ≤ k) {R : X} (hR : R ∈ J.reps) :
    (J.orbitList R).IsChain (fun C C' => 2 ≤ ew k (sigmaInv (J.lst C)) (J.fst C') ∧
      ew k (sigmaInv (J.lst C)) (J.fst C') ≤ J.jin C' + 3) := by
  unfold orbitList
  rw [List.isChain_map, List.isChain_range]
  intro m hm
  have hm1 : m + 1 < J.per R := by omega
  have hsucc : (⇑J.nxt)^[m + 1] R = J.nxt ((⇑J.nxt)^[m] R) :=
    Function.iterate_succ_apply' _ _ _
  have hne : (⇑J.nxt)^[m] R ≠ (⇑J.nxt)^[m + 1] R := by
    intro h
    have h1 := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑J.nxt) (x := R)
      (Set.mem_Iio.mpr (by omega : m < J.per R)) (Set.mem_Iio.mpr hm1) h
    omega
  have hnr : (⇑J.nxt)^[m + 1] R ≠ J.root := by
    intro h
    rcases List.mem_cons.mp hR with hRr | hR'
    · rw [hRr] at h hm1
      have h1 := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑J.nxt) (x := J.root)
        (Set.mem_Iio.mpr hm1) (Set.mem_Iio.mpr (J.per_pos J.root)) h
      omega
    · exact J.root_not_mem_of_hang hR' (J.mem_orbitList.mpr ⟨m + 1, h⟩)
  have hlink := J.link ((⇑J.nxt)^[m] R) (by rw [← hsucc]; exact hnr)
  rw [← hsucc] at hlink
  have hgood := goodLink_of_not_isRotated hk
    (J.disjoint _ _ hne _ (J.lst_mem _) _ (J.fst_mem _))
  exact ⟨hgood.1, hlink⟩

/-- What a component is charged: its line, and the junction into it unless it is the root. -/
noncomputable def charge (C : X) : ℕ :=
  lineCost (J.line C) + if C = J.root then 0 else J.jin C

theorem newLine_cost_le (hk : 2 ≤ k) {R : X} (hR : R ∈ J.reps) :
    lineCost (J.newLine R) + (if R = J.root then 0 else J.jin R) ≤
      ((J.orbitList R).map J.charge).sum := by
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp (J.orbitList_head R)
  have hchain := J.orbitList_chain hk hR
  have hle := J.lineCost_flatMap_le (J.orbitList R)
    (by rw [hrest]; exact List.cons_ne_nil _ _) hchain
  have hnd := J.orbitList_nodup R
  rw [hrest] at hle hnd
  have hrestne : ∀ C ∈ rest, C ≠ J.root := by
    intro C hC hCr
    rcases List.mem_cons.mp hR with hRr | hR'
    · have hmem : R ∈ rest := by
        rw [hRr, ← hCr]
        exact hC
      exact (List.nodup_cons.mp hnd).1 hmem
    · apply J.root_not_mem_of_hang hR'
      rw [hrest, ← hCr]
      exact List.mem_cons_of_mem _ hC
  have hsum : (rest.map J.charge).sum =
      (rest.map (fun C => lineCost (J.line C))).sum + (rest.map J.jin).sum := by
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro C hC
    unfold charge
    rw [if_neg (hrestne C hC)]
  unfold newLine
  rw [hrest]
  simp only [List.map_cons, List.sum_cons, List.tail_cons] at hle ⊢
  rw [hsum]
  unfold charge
  generalize (if R = J.root then 0 else J.jin R) = x
  omega

theorem hang_cost (hk : 2 ≤ k) (R : X) :
    (J.hang R).cost = lineCost (J.newLine R) +
      (ew k (sigmaInv (J.lst (J.nxt.symm R))) (sigma (J.slot R)) +
        ew k (J.slot R) (J.fst R) - 4) := by
  show rowsCost (groupRows (J.newLine R)) +
      (NHanging.w0 ⟨groupRows (J.newLine R), J.slot R⟩ +
        NHanging.w1 ⟨groupRows (J.newLine R), J.slot R⟩ - 4) = _
  rw [NHanging.w0_groupRows (J.newLine_chain hk R) (J.newLine_last R),
    NHanging.w1_groupRows (J.newLine_chain hk R) (J.newLine_head R),
    (J.groupInv hk R).cost (J.newLine_ne R)]

theorem sum_flatMap_map {α β : Type} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, ih]

/-- **Theorem N, the defect.**  The cost of the configuration is at most the sum of the costs
of the lines of all components and of all junctions. -/
theorem config_cost_le (hk : 2 ≤ k) : J.config.cost ≤ ∑ C : X, J.charge C := by
  have hsum : ∑ C : X, J.charge C = (J.allList.map J.charge).sum := by
    rw [← List.sum_toFinset _ J.allList_nodup]
    congr 1
    exact (Finset.eq_univ_of_forall (fun C => List.mem_toFinset.mpr (J.mem_allList C))).symm
  rw [hsum]
  unfold allList
  rw [sum_flatMap_map]
  show rowsCost (groupRows (J.newLine J.root)) + ((J.hangReps.map J.hang).map NHanging.cost).sum ≤
    ((J.root :: J.hangReps).map (fun R => ((J.orbitList R).map J.charge).sum)).sum
  rw [List.map_cons, List.sum_cons, List.map_map, (J.groupInv hk J.root).cost (J.newLine_ne _)]
  have hk0 := J.newLine_cost_le hk (R := J.root) List.mem_cons_self
  rw [if_pos rfl, Nat.add_zero] at hk0
  refine Nat.add_le_add hk0 ?_
  apply List.sum_le_sum
  intro R hR
  have hRne := (J.mem_hangReps.mp hR).2
  have h := J.newLine_cost_le hk (R := R) (List.mem_cons_of_mem _ hR)
  rw [if_neg hRne] at h
  show NHanging.cost (J.hang R) ≤ ((J.orbitList R).map J.charge).sum
  rw [J.hang_cost hk R]
  have hatt := J.att R hRne
  omega

end JoinData

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.JoinData.config_valid
#print axioms SuperpermLowerBounds.JoinData.config_cost_le

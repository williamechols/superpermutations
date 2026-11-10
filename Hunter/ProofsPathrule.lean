/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsStructure

/-!
# Proofs — §5 path rule of Hunter, *A New Lower Bound for Superpermutations*

The last gating lemma of §5: `lem_pathrule` (every weak component of `X = F(P)` linearizes
to a path-component), and its downstream `cor_exitlessrule`, `prp_Xk_se_necessity`,
`prp_Xk_se_sufficiency`.

Helper lemmas live in `namespace Hunter.ProofsPathrule`; targets are proved as
`Hunter.Proved.<name>` with the type copied verbatim from `Hunter/Statements.lean`.

Reuses `Hunter.ProofsStructure` (rules ladder, `lem_walking`), `Hunter.ProofsSpine`
(degree lemmas), `Hunter.ProofsExitless` (rotation lemmas).
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsPathrule

variable {k : ℕ}

/-! ## Small membership unfoldings for `C₀`, `C₋₁` -/

theorem mem_C0_iff {P : HPath k} {v : Vtx k} : v ∈ C0 P ↔ firstInCycle P v := by
  rw [C0, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_Cm1_iff {P : HPath k} {v : Vtx k} : v ∈ Cm1 P ↔ sigma v ∈ C0 P := by
  rw [Cm1, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ## The `C₀` representative of a 1-cycle and the σ-exponent -/

/-- Every vertex's 1-cycle contains a `firstInCycle` (i.e. `C₀`) vertex — the `P.pos`-minimum
of the cycle. -/
theorem exists_c0_in_cyc (P : HPath k) (v : Vtx k) :
    ∃ c, firstInCycle P c ∧ rotClass c.1 = rotClass v.1 := by
  have hne : (cyc v).Nonempty := ⟨v, ProofsExitless.mem_cyc.mpr rfl⟩
  obtain ⟨c, hcmem, hcmin⟩ := (cyc v).exists_min_image (fun u => P.pos u) hne
  have hcr : rotClass c.1 = rotClass v.1 := ProofsExitless.mem_cyc.mp hcmem
  refine ⟨c, ?_, hcr⟩
  intro u hu
  have huc : u ∈ cyc v := ProofsExitless.mem_cyc.mpr (hu.trans hcr)
  exact hcmin u huc

/-- The `C₀` representative of `v`'s 1-cycle. -/
noncomputable def c0rep (P : HPath k) (v : Vtx k) : Vtx k := (exists_c0_in_cyc P v).choose

theorem c0rep_first (P : HPath k) (v : Vtx k) : firstInCycle P (c0rep P v) :=
  (exists_c0_in_cyc P v).choose_spec.1

theorem c0rep_rotClass (P : HPath k) (v : Vtx k) :
    rotClass (c0rep P v).1 = rotClass v.1 := (exists_c0_in_cyc P v).choose_spec.2

theorem c0rep_mem_C0 (P : HPath k) (v : Vtx k) : c0rep P v ∈ C0 P :=
  mem_C0_iff.mpr (c0rep_first P v)

/-- Uniqueness of the `C₀` vertex in a 1-cycle (needs `P` Hamiltonian: `P.pos` is injective). -/
theorem c0_unique {P : HPath k} (hP : P.IsHamiltonian) {a b : Vtx k}
    (ha : firstInCycle P a) (hb : firstInCycle P b) (hr : rotClass a.1 = rotClass b.1) :
    a = b := by
  have h1 : P.pos a ≤ P.pos b := ha b hr.symm
  have h2 : P.pos b ≤ P.pos a := hb a hr
  have hpos : P.pos a = P.pos b := le_antisymm h1 h2
  rw [← ProofsExitless.vert_pos P (hP a), hpos, ProofsExitless.vert_pos P (hP b)]

/-- `c0rep` is constant on a 1-cycle: `c0rep (σv) = c0rep v`. -/
theorem c0rep_sigma {P : HPath k} (hP : P.IsHamiltonian) (v : Vtx k) :
    c0rep P (sigma v) = c0rep P v := by
  apply c0_unique hP (c0rep_first P (sigma v)) (c0rep_first P v)
  rw [c0rep_rotClass, c0rep_rotClass, ProofsStructure.rotClass_sigma]

/-- If `v ∈ C₀`, it is its own `C₀` representative. -/
theorem c0rep_of_mem_C0 {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k} (hv : v ∈ C0 P) :
    c0rep P v = v :=
  c0_unique hP (c0rep_first P v) (mem_C0_iff.mp hv) (c0rep_rotClass P v)

/-- The σ-exponent of `v` from its `C₀` representative (for `1 ≤ k`). -/
noncomputable def aExp (P : HPath k) (v : Vtx k) : ℕ :=
  if h : ∃ r, r < k ∧ v = sigma^[r] (c0rep P v) then h.choose else 0

theorem aExp_spec (hk : 1 ≤ k) (P : HPath k) (v : Vtx k) :
    aExp P v < k ∧ v = sigma^[aExp P v] (c0rep P v) := by
  have hmem : v ∈ cyc (c0rep P v) := ProofsExitless.mem_cyc.mpr (c0rep_rotClass P v).symm
  have hex : ∃ r, r < k ∧ v = sigma^[r] (c0rep P v) :=
    (ProofsExitless.mem_cyc_iff_exists hk).mp hmem
  rw [aExp, dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩

/-! ## The strict potential and acyclicity -/

/-- The topological potential: `pot v = k · P.pos(c0rep v) + aExp v` (lex order on
`(cycle position of the C₀ vertex, σ-distance within the cycle)`). -/
noncomputable def pot (P : HPath k) (v : Vtx k) : ℕ := k * P.pos (c0rep P v) + aExp P v

/-- `pot` strictly increases along every edge of `F(P)`. -/
theorem pot_lt_of_edge {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) {u w : Vtx k}
    (h : (u, w) ∈ F P) : pot P u < pot P w := by
  by_cases hu : u ∈ Cm1 P
  · -- Rule 3: `u ∈ C₋₁`, edge leaves to a `C₀` vertex `w`.
    have hne : outV (F P) u ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty]
      exact ⟨(u, w), by simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩⟩
    obtain ⟨w', hw'C0, hout⟩ := Proved.clm_rule3 hP hu hne
    have hww : w = w' := by
      have hmem : (u, w) ∈ outV (F P) u := by
        simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩
      rw [hout, Finset.mem_singleton] at hmem
      exact (Prod.ext_iff.mp hmem).2
    subst hww
    have hwnCm1 : w ∉ Cm1 P := ProofsStructure.C0_not_Cm1 hP hk hw'C0
    -- `walking_aux` on the 2-vertex walk `[u,w]` gives `P.pos u < P.pos w`.
    have hwalk : IsWalk (F P) [u, w] := by
      rw [IsWalk, List.isChain_iff_getElem]
      intro i hi
      have hlen : [u, w].length = 2 := rfl
      rw [hlen] at hi
      obtain rfl : i = 0 := by omega
      simpa using h
    have hposlt : P.pos u < P.pos w := by
      have hkey := Proved.walking_aux hP hwalk 1 0 1 (by simp) (by simp) rfl (by omega)
        (by simpa using Finset.mem_union.mpr (Or.inr hu))
      simpa using hkey
    -- assemble
    obtain ⟨hau_lt, -⟩ := aExp_spec (by omega : 1 ≤ k) P u
    obtain ⟨haw_lt, -⟩ := aExp_spec (by omega : 1 ≤ k) P w
    have hcu : P.pos (c0rep P u) ≤ P.pos u :=
      c0rep_first P u u (c0rep_rotClass P u).symm
    have hcw : c0rep P w = w := c0rep_of_mem_C0 hP hw'C0
    have hlt : P.pos (c0rep P u) < P.pos w := lt_of_le_of_lt hcu hposlt
    unfold pot
    rw [hcw]
    -- k*pos(c0rep u) + aExp u  <  k*pos w + aExp w
    have hstep : k * P.pos (c0rep P u) + k ≤ k * P.pos w :=
      calc k * P.pos (c0rep P u) + k = k * (P.pos (c0rep P u) + 1) := by ring
        _ ≤ k * P.pos w := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  · -- Rule 2: `u ∉ C₋₁`, edge is the 1-edge `(u, σu)`.
    have h2 := Proved.clm_rule2 hP hu
    have hw : w = sigma u := by
      have hmem : (u, w) ∈ outV (F P) u := by
        simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩
      rw [h2, Finset.mem_singleton] at hmem
      exact (Prod.ext_iff.mp hmem).2
    subst hw
    have hk1 : 1 ≤ k := by omega
    set c := c0rep P u with hc
    have hcsig : c0rep P (sigma u) = c := c0rep_sigma hP u
    obtain ⟨hau_lt, hau_eq⟩ := aExp_spec hk1 P u
    obtain ⟨haw_lt, haw_eq⟩ := aExp_spec hk1 P (sigma u)
    have haw_eq2 : sigma u = sigma^[aExp P u + 1] c := by
      rw [Function.iterate_succ_apply', ← hau_eq]
    -- `aExp u + 1 < k`
    have hau1 : aExp P u + 1 < k := by
      by_contra hcon
      have heq : aExp P u = k - 1 := by omega
      have hsig : sigma u = c := by
        have hb := haw_eq2
        rw [heq, show k - 1 + 1 = k from by omega] at hb
        rw [hb]; exact ProofsExitless.sigma_iter_period c
      have hcC0 : c ∈ C0 P := hc ▸ c0rep_mem_C0 P u
      exact hu (mem_Cm1_iff.mpr (hsig ▸ hcC0))
    -- `aExp (σu) = aExp u + 1`
    have haweq : aExp P (sigma u) = aExp P u + 1 := by
      have h' : sigma^[aExp P (sigma u)] c = sigma^[aExp P u + 1] c := by
        rw [hcsig] at haw_eq; rw [← haw_eq, ← haw_eq2]
      exact ProofsExitless.sigma_iter_inj c haw_lt hau1 h'
    unfold pot
    rw [hcsig, haweq, ← hc]
    omega

/-- Any list `D` whose consecutive image under `g : α → ℕ` strictly increases is `Nodup`. -/
theorem nodup_of_strictmono {α : Type*} {D : List α} {g : α → ℕ}
    (h : ∀ i (hi : i + 1 < D.length), g (D[i]'(by omega)) < g (D[i + 1]'hi)) : D.Nodup := by
  have hc : List.IsChain (· < ·) (D.map g) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    rw [List.length_map] at hi
    rw [List.getElem_map, List.getElem_map]
    exact h i hi
  have hp : List.Pairwise (· < ·) (D.map g) := List.isChain_iff_pairwise.mp hc
  exact List.Nodup.of_map g (hp.imp (fun hlt => Nat.ne_of_lt hlt))

/-- Companion of `nodup_of_strictmono` for a strictly *decreasing* image. -/
theorem nodup_of_strictanti {α : Type*} {D : List α} {g : α → ℕ}
    (h : ∀ i (hi : i + 1 < D.length), g (D[i + 1]'hi) < g (D[i]'(by omega))) : D.Nodup := by
  have hc : List.IsChain (· > ·) (D.map g) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    rw [List.length_map] at hi
    rw [List.getElem_map, List.getElem_map]
    exact h i hi
  have hp : List.Pairwise (· > ·) (D.map g) := List.isChain_iff_pairwise.mp hc
  exact List.Nodup.of_map g (hp.imp (fun hgt => (Nat.ne_of_lt hgt).symm))

/-- **Acyclicity**: every directed walk in `F(P)` is `Nodup` (`F(P)` is a DAG). -/
theorem acyc {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) {D : List (Vtx k)}
    (hD : IsWalk (F P) D) : D.Nodup := by
  apply nodup_of_strictmono (g := pot P)
  intro i hi
  have hedge : (D[i], D[i + 1]) ∈ F P := List.IsChain.getElem hD i hi
  exact pot_lt_of_edge hP hk hedge

/-! ## The deterministic successor / predecessor and the linearization `iterOpt` -/

/-- The unique out-neighbour of `v` in `X` (when out-degree ≤ 1). -/
noncomputable def succ (X : Finset (Vtx k × Vtx k)) (v : Vtx k) : Option (Vtx k) :=
  if h : ∃ w, (v, w) ∈ X then some h.choose else none

/-- The unique in-neighbour of `v` in `X` (when in-degree ≤ 1). -/
noncomputable def pred (X : Finset (Vtx k × Vtx k)) (v : Vtx k) : Option (Vtx k) :=
  if h : ∃ u, (u, v) ∈ X then some h.choose else none

theorem edge_of_succ_some {X : Finset (Vtx k × Vtx k)} {v w : Vtx k}
    (h : succ X v = some w) : (v, w) ∈ X := by
  unfold succ at h
  by_cases hex : ∃ w, (v, w) ∈ X
  · rw [dif_pos hex] at h
    have hw : hex.choose = w := Option.some.inj h
    have := hex.choose_spec
    rwa [hw] at this
  · rw [dif_neg hex] at h; exact absurd h (by simp)

theorem succ_some_of_edge {X : Finset (Vtx k × Vtx k)} {v w : Vtx k}
    (hcard : (outV X v).card ≤ 1) (h : (v, w) ∈ X) : succ X v = some w := by
  have hex : ∃ w, (v, w) ∈ X := ⟨w, h⟩
  unfold succ; rw [dif_pos hex]
  congr 1
  have hvw : (v, w) ∈ outV X v := by
    simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨h, trivial⟩
  have hcw : (v, hex.choose) ∈ outV X v := by
    simp only [outV, mem_out, Finset.mem_singleton]; exact ⟨hex.choose_spec, trivial⟩
  have := Finset.card_le_one.mp hcard _ hcw _ hvw
  exact (Prod.ext_iff.mp this).2

theorem edge_of_pred_some {X : Finset (Vtx k × Vtx k)} {v u : Vtx k}
    (h : pred X v = some u) : (u, v) ∈ X := by
  unfold pred at h
  by_cases hex : ∃ u, (u, v) ∈ X
  · rw [dif_pos hex] at h
    have hu : hex.choose = u := Option.some.inj h
    have := hex.choose_spec
    rwa [hu] at this
  · rw [dif_neg hex] at h; exact absurd h (by simp)

theorem pred_eq_none_iff {X : Finset (Vtx k × Vtx k)} {v : Vtx k} :
    pred X v = none ↔ intoV X v = ∅ := by
  unfold pred
  by_cases hex : ∃ u, (u, v) ∈ X
  · rw [dif_pos hex]
    have hne : (intoV X v).Nonempty := by
      obtain ⟨u, hu⟩ := hex
      exact ⟨(u, v), by simp only [intoV, mem_into, Finset.mem_singleton]; exact ⟨hu, trivial⟩⟩
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd (Finset.nonempty_iff_ne_empty.mp hne) (by rw [h]; simp)
  · rw [dif_neg hex]
    simp only [true_iff]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [intoV, mem_into, Finset.mem_singleton] at he
    exact hex ⟨e.1, by rw [← he.2]; exact he.1⟩

/-- Follow the partial function `f` from `v` for at most `n` steps. -/
noncomputable def iterOpt (f : Vtx k → Option (Vtx k)) : ℕ → Vtx k → List (Vtx k)
  | 0, v => [v]
  | (n + 1), v => v :: (match f v with | none => [] | some w => iterOpt f n w)

theorem iterOpt_succ_none (f : Vtx k → Option (Vtx k)) {n : ℕ} {v : Vtx k} (h : f v = none) :
    iterOpt f (n + 1) v = [v] := by simp only [iterOpt, h]

theorem iterOpt_succ_some (f : Vtx k → Option (Vtx k)) {n : ℕ} {v w : Vtx k} (h : f v = some w) :
    iterOpt f (n + 1) v = v :: iterOpt f n w := by simp only [iterOpt, h]

theorem iterOpt_head (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    ∃ t, iterOpt f n v = v :: t := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n => exact ⟨_, rfl⟩

theorem iterOpt_ne_nil (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    iterOpt f n v ≠ [] := by
  obtain ⟨t, ht⟩ := iterOpt_head f n v; rw [ht]; exact List.cons_ne_nil v t

theorem iterOpt_head_eq (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    (iterOpt f n v).head (iterOpt_ne_nil f n v) = v := by
  obtain ⟨t, ht⟩ := iterOpt_head f n v
  simp only [ht, List.head_cons]

theorem iterOpt_chain (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    List.IsChain (fun a b => f a = some b) (iterOpt f n v) := by
  induction n generalizing v with
  | zero => exact List.isChain_singleton _
  | succ n ih =>
    cases hfv : f v with
    | none => rw [iterOpt_succ_none f hfv]; exact List.isChain_singleton _
    | some w =>
      rw [iterOpt_succ_some f hfv]
      obtain ⟨t, ht⟩ := iterOpt_head f n w
      rw [ht]
      rw [List.isChain_cons_cons]
      refine ⟨hfv, ?_⟩
      rw [← ht]; exact ih w

theorem iterOpt_length_le (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    (iterOpt f n v).length ≤ n + 1 := by
  induction n generalizing v with
  | zero => simp [iterOpt]
  | succ n ih =>
    cases hfv : f v with
    | none => rw [iterOpt_succ_none f hfv]; simp
    | some w =>
      rw [iterOpt_succ_some f hfv, List.length_cons]
      have := ih w; omega

theorem iterOpt_mem_closed (f : Vtx k → Option (Vtx k)) {C : Finset (Vtx k)}
    (hstep : ∀ a b, f a = some b → a ∈ C → b ∈ C) :
    ∀ (n : ℕ) (v : Vtx k), v ∈ C → ∀ x ∈ iterOpt f n v, x ∈ C := by
  intro n
  induction n with
  | zero => intro v hv x hx; rw [iterOpt] at hx; rw [List.mem_singleton] at hx; rwa [hx]
  | succ n ih =>
    intro v hv x hx
    cases hfv : f v with
    | none => rw [iterOpt_succ_none f hfv, List.mem_singleton] at hx; rwa [hx]
    | some w =>
      rw [iterOpt_succ_some f hfv, List.mem_cons] at hx
      rcases hx with hx | hx
      · rwa [hx]
      · exact ih w (hstep v w hfv hv) x hx

theorem iterOpt_last_spec (f : Vtx k → Option (Vtx k)) (n : ℕ) (v : Vtx k) :
    (∀ z, (iterOpt f n v).getLast? = some z → f z = none) ∨
      (iterOpt f n v).length = n + 1 := by
  induction n generalizing v with
  | zero => right; simp [iterOpt]
  | succ n ih =>
    cases hfv : f v with
    | none =>
      left
      intro z hz
      rw [iterOpt_succ_none f hfv, List.getLast?_singleton] at hz
      rw [← Option.some.inj hz]; exact hfv
    | some w =>
      have hcons := iterOpt_succ_some f (n := n) hfv
      obtain ⟨t, ht⟩ := iterOpt_head f n w
      rcases ih w with hL | hR
      · left
        intro z hz
        rw [hcons, ht, List.getLast?_cons_cons] at hz
        exact hL z (by rw [ht]; exact hz)
      · right
        rw [hcons, List.length_cons, hR]

/-- Consecutive elements of an `f`-chain are `f`-related. -/
theorem chain_rel_of_zip {R : Vtx k → Vtx k → Prop} {L : List (Vtx k)}
    (hL : L.IsChain R) {a b : Vtx k} (h : (a, b) ∈ L.zip L.tail) : R a b := by
  induction L with
  | nil => simp at h
  | cons x l ih =>
    cases l with
    | nil => simp at h
    | cons y t =>
      rw [List.tail_cons] at h
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rw [List.isChain_cons_cons] at hL
      rcases h with h | h
      · injection h with h1 h2; subst h1; subst h2; exact hL.1
      · exact ih hL.2 (by rw [List.tail_cons]; exact h)

/-- In a completed `f`-chain (last vertex has `f = none`), any member with a defined `f`-value
has that value as its list-successor. -/
theorem chain_step_mem {f : Vtx k → Option (Vtx k)} {L : List (Vtx k)}
    (hL : L.IsChain (fun a b => f a = some b))
    (hlast : ∀ z, L.getLast? = some z → f z = none) {x y : Vtx k}
    (hx : x ∈ L) (hxy : f x = some y) : (x, y) ∈ L.zip L.tail := by
  induction L with
  | nil => simp at hx
  | cons a l ih =>
    cases l with
    | nil =>
      have hfa : f a = none := hlast a (by simp)
      rw [List.mem_singleton] at hx; rw [hx, hfa] at hxy; exact absurd hxy (by simp)
    | cons b t =>
      rw [List.isChain_cons_cons] at hL
      have hlast' : ∀ z, (b :: t).getLast? = some z → f z = none := by
        intro z hz; exact hlast z (by rw [List.getLast?_cons_cons]; exact hz)
      rw [List.mem_cons] at hx
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
      rcases hx with hx | hx
      · left
        have hb : f x = some b := by rw [hx]; exact hL.1
        rw [hxy] at hb
        have hyb : y = b := Option.some.inj hb
        rw [hx, hyb]
      · right
        have := ih hL.2 hlast' hx
        rwa [List.tail_cons] at this

/-- In an `f`-chain, any non-head member has a list-predecessor. -/
theorem chain_prev_mem {f : Vtx k → Option (Vtx k)} {L : List (Vtx k)}
    (hL : L.IsChain (fun a b => f a = some b)) {x : Vtx k}
    (hx : x ∈ L) (hxh : L.head? ≠ some x) : ∃ b, (b, x) ∈ L.zip L.tail := by
  induction L with
  | nil => simp at hx
  | cons a l ih =>
    cases l with
    | nil =>
      rw [List.mem_singleton] at hx
      rw [hx] at hxh; simp at hxh
    | cons b t =>
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hxh
      simp only [List.tail_cons, List.zip_cons_cons]
      rw [List.mem_cons] at hx
      by_cases hxb : x = b
      · exact ⟨a, by rw [hxb]; exact List.mem_cons_self⟩
      · have hxt : x ∈ t := by
          rcases hx with h | h
          · exact absurd h.symm hxh
          · rw [List.mem_cons] at h; rcases h with h | h
            · exact absurd h hxb
            · exact h
        rw [List.isChain_cons_cons] at hL
        have hxh' : (b :: t).head? ≠ some x := by
          simp only [List.head?_cons, ne_eq, Option.some.injEq]; exact fun hc => hxb hc.symm
        obtain ⟨c, hc⟩ := ih hL.2 (List.mem_cons_of_mem b hxt) hxh'
        exact ⟨c, List.mem_cons_of_mem _ (by rwa [List.tail_cons] at hc)⟩

theorem succ_eq_none_iff {X : Finset (Vtx k × Vtx k)} {v : Vtx k} :
    succ X v = none ↔ outV X v = ∅ := by
  unfold succ
  by_cases hex : ∃ w, (v, w) ∈ X
  · rw [dif_pos hex]
    obtain ⟨w, hw⟩ := hex
    have hne : (outV X v).Nonempty :=
      ⟨(v, w), by simp only [outV, mem_out]; exact ⟨hw, Finset.mem_singleton_self _⟩⟩
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd (Finset.nonempty_iff_ne_empty.mp hne) (by rw [h]; simp)
  · rw [dif_neg hex]
    simp only [true_iff]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [outV, mem_out, Finset.mem_singleton] at he
    exact hex ⟨e.2, by rw [← he.2]; exact he.1⟩

/-! ## Weak connectivity is symmetric; weak components are closed -/

theorem weakStep_symm {X : Finset (Vtx k × Vtx k)} {a b : Vtx k} (h : weakStep X a b) :
    weakStep X b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem weakConn_symm {X : Finset (Vtx k × Vtx k)} {a b : Vtx k} (h : weakConn X a b) :
    weakConn X b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (weakStep_symm hstep) ih

/-- A weakly incident vertex lies in `vertsOf X`. -/
theorem mem_vertsOf_of_weakStep {X : Finset (Vtx k × Vtx k)} {a b : Vtx k}
    (h : weakStep X a b) : b ∈ vertsOf X := by
  rw [vertsOf, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases h with h | h
  · exact ⟨(a, b), h, Or.inr rfl⟩
  · exact ⟨(b, a), h, Or.inl rfl⟩

/-- For `k ≥ 2` an `F(P)`-edge exists only if `k ≥ 2`. -/
theorem two_le_of_mem_F {P : HPath k} (hP : P.IsHamiltonian) {e : Vtx k × Vtx k}
    (he : e ∈ F P) : 2 ≤ k := by
  by_contra hc
  haveI := ProofsStructure.vtx_subsingleton (show k ≤ 1 by omega)
  have ha : e.1 ∈ Cm1 P := ProofsStructure.mem_Cm1_of_le_one (by omega) P e.1
  have hout : outV (F P) e.1 ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]
    exact ⟨e, by simp only [outV, mem_out]; exact ⟨he, Finset.mem_singleton_self _⟩⟩
  have heq := Proved.clm_rule1 hP ha hout
  have hPempty : P.edges = ∅ := by
    have hlen : P.verts.length ≤ 1 := ProofsSpine.length_le_one_of_subsingleton P.nodup
    rw [HPath.edges, Finset.eq_empty_iff_forall_notMem]
    intro x hx; rw [List.mem_toFinset] at hx
    have h3 := List.length_pos_of_mem (ProofsSpine.snd_mem_tail hx)
    rw [List.length_tail] at h3; omega
  rw [heq] at hout
  exact hout (by rw [outV, out, hPempty]; exact Finset.filter_empty _)

/-! ## The linearization of a weak component -/

/-- **Core of `lem_pathrule`**: every `C ∈ Comps(F P)` is `V(p)` for an `HPath`
path-component `p`. -/
theorem lem_pathrule_core {P : HPath k} (hP : P.IsHamiltonian) :
    ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P) := by
  intro C hC
  -- extract the component's representative `v₀`
  rw [Comps, Finset.mem_image] at hC
  obtain ⟨v₀, hv₀V, hCeq⟩ := hC
  have hCmem : ∀ u, u ∈ C ↔ u ∈ vertsOf (F P) ∧ weakConn (F P) v₀ u := by
    intro u; rw [← hCeq, Finset.mem_filter]
  have hv₀C : v₀ ∈ C := (hCmem v₀).mpr ⟨hv₀V, Relation.ReflTransGen.refl⟩
  -- `k ≥ 2`
  obtain ⟨e₀, he₀X, -⟩ := (by rw [vertsOf, Finset.mem_filter] at hv₀V; exact hv₀V.2)
  have hk2 : 2 ≤ k := two_le_of_mem_F hP he₀X
  -- degree bounds
  have houtcard : ∀ v, (outV (F P) v).card ≤ 1 := fun v => (Proved.clm_degree (sset_sPrecond P) v).1
  have hintocard : ∀ v, (intoV (F P) v).card ≤ 1 := fun v => (Proved.clm_degree (sset_sPrecond P) v).2
  -- weak closure of `C`
  have hCclosed : ∀ a b, a ∈ C → weakStep (F P) a b → b ∈ C := by
    intro a b ha hab
    rw [hCmem] at ha ⊢
    exact ⟨mem_vertsOf_of_weakStep hab, ha.2.tail hab⟩
  -- successor / predecessor step preserve `C`
  have hstepC : ∀ a b, succ (F P) a = some b → a ∈ C → b ∈ C := fun a b hab ha =>
    hCclosed a b ha (Or.inl (edge_of_succ_some hab))
  have hstepBack : ∀ a b, pred (F P) a = some b → a ∈ C → b ∈ C := fun a b hab ha =>
    hCclosed a b ha (Or.inr (edge_of_pred_some hab))
  set N := (vertsOf (F P)).card with hN
  -- ===== find the source `s` via a backward walk =====
  set B := iterOpt (pred (F P)) N v₀ with hB
  have hBmem : ∀ x ∈ B, x ∈ C := iterOpt_mem_closed (pred (F P)) hstepBack N v₀ hv₀C
  have hBchain : B.IsChain (fun a b => pred (F P) a = some b) := iterOpt_chain _ N v₀
  have hBnodup : B.Nodup := by
    apply nodup_of_strictanti (g := pot P)
    intro i hi
    have hrel := List.IsChain.getElem hBchain i hi
    exact pot_lt_of_edge hP hk2 (edge_of_pred_some hrel)
  have hBsub : B.toFinset ⊆ vertsOf (F P) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have := hBmem x hx
    rw [hCmem] at this; exact this.1
  have hBlen : B.length ≤ N := by
    rw [← List.toFinset_card_of_nodup hBnodup]; exact Finset.card_le_card hBsub
  have hBlast : ∀ z, B.getLast? = some z → pred (F P) z = none := by
    rcases iterOpt_last_spec (pred (F P)) N v₀ with h | h
    · exact h
    · rw [← hB] at h; omega
  set s := B.getLast (iterOpt_ne_nil _ N v₀) with hs
  have hsB : s ∈ B := List.getLast_mem (iterOpt_ne_nil _ N v₀)
  have hsC : s ∈ C := hBmem s hsB
  have hsource : intoV (F P) s = ∅ := by
    rw [← pred_eq_none_iff]
    apply hBlast s
    rw [hs]
    exact List.getLast?_eq_getLast_of_ne_nil (iterOpt_ne_nil _ N v₀)
  -- ===== build the forward path `L` from `s` =====
  set L := iterOpt (succ (F P)) N s with hL
  have hLmem : ∀ x ∈ L, x ∈ C := iterOpt_mem_closed (succ (F P)) hstepC N s hsC
  have hLchain : L.IsChain (fun a b => succ (F P) a = some b) := iterOpt_chain _ N s
  have hLnodup : L.Nodup := by
    apply nodup_of_strictmono (g := pot P)
    intro i hi
    have hrel := List.IsChain.getElem hLchain i hi
    exact pot_lt_of_edge hP hk2 (edge_of_succ_some hrel)
  have hLne : L ≠ [] := iterOpt_ne_nil _ N s
  have hLhead : L.head hLne = s := iterOpt_head_eq _ N s
  have hLsub : L.toFinset ⊆ vertsOf (F P) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have := hLmem x hx
    rw [hCmem] at this; exact this.1
  have hLlen : L.length ≤ N := by
    rw [← List.toFinset_card_of_nodup hLnodup]; exact Finset.card_le_card hLsub
  have hLlast : ∀ z, L.getLast? = some z → succ (F P) z = none := by
    rcases iterOpt_last_spec (succ (F P)) N s with h | h
    · exact h
    · rw [← hL] at h; omega
  -- ===== `L`'s vertex set is weakly closed =====
  have hLclosed : ∀ x y, x ∈ L.toFinset → weakStep (F P) x y → y ∈ L.toFinset := by
    intro x y hx hxy
    rw [List.mem_toFinset] at hx
    rcases hxy with hedge | hedge
    · -- forward edge `x → y`
      have hstep := chain_step_mem hLchain hLlast hx (succ_some_of_edge (houtcard x) hedge)
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.of_mem_zip hstep).2)
    · -- backward edge `y → x`
      have hxs : x ≠ s := by
        intro hc; rw [hc] at hedge
        have : (y, s) ∈ intoV (F P) s := by
          rw [intoV, mem_into]; exact ⟨hedge, Finset.mem_singleton_self _⟩
        rw [hsource] at this; exact absurd this (Finset.notMem_empty _)
      have hhead : L.head? ≠ some x := by
        obtain ⟨t, ht⟩ := iterOpt_head (succ (F P)) N s
        rw [← hL] at ht
        rw [ht, List.head?_cons]
        intro hc; exact hxs (Option.some.inj hc).symm
      obtain ⟨b, hb⟩ := chain_prev_mem hLchain hx hhead
      have hbedge : (b, x) ∈ F P := edge_of_succ_some (chain_rel_of_zip hLchain hb)
      -- in-degree ≤ 1 forces `b = y`
      have hby : b = y := by
        have h1 : (b, x) ∈ intoV (F P) x := by
          rw [intoV, mem_into]; exact ⟨hbedge, Finset.mem_singleton_self _⟩
        have h2 : (y, x) ∈ intoV (F P) x := by
          rw [intoV, mem_into]; exact ⟨hedge, Finset.mem_singleton_self _⟩
        have := Finset.card_le_one.mp (hintocard x) _ h1 _ h2
        exact (Prod.ext_iff.mp this).1
      rw [← hby]
      exact List.mem_toFinset.mpr (List.of_mem_zip hb).1
  -- ===== `V(L) = C` =====
  have hsL : s ∈ L.toFinset := List.mem_toFinset.mpr (hLhead ▸ List.head_mem hLne)
  have hVsubC : L.toFinset ⊆ C := by
    intro x hx; exact hLmem x (List.mem_toFinset.mp hx)
  have hCsubV : C ⊆ L.toFinset := by
    intro y hy
    -- `weakConn s y`
    have hsy : weakConn (F P) s y := by
      have hsv : weakConn (F P) v₀ s := ((hCmem s).mp hsC).2
      have hyv : weakConn (F P) v₀ y := ((hCmem y).mp hy).2
      exact (weakConn_symm hsv).trans hyv
    -- closure induction
    clear hy
    induction hsy with
    | refl => exact hsL
    | tail _ hstep ih => exact hLclosed _ _ ih hstep
  have hVC : L.toFinset = C := Finset.Subset.antisymm hVsubC hCsubV
  -- ===== assemble the `HPath` and `IsPathComponent` =====
  refine ⟨⟨L, hLne, hLnodup⟩, ?_, ?_, ?_, ?_⟩
  · show L.toFinset = C; exact hVC
  · -- `p.edges ⊆ F P`
    intro e he
    rw [HPath.edges, List.mem_toFinset] at he
    have hrel : succ (F P) e.1 = some e.2 := chain_rel_of_zip hLchain he
    have := edge_of_succ_some hrel
    simpa using this
  · -- boundary condition
    intro e he
    have hVsimp : (⟨L, hLne, hLnodup⟩ : HPath k).vertsFinset = C := hVC
    rw [hVsimp]
    constructor
    · intro h1; exact hCclosed e.1 e.2 h1 (Or.inl (show (e.1, e.2) ∈ F P by simpa using he))
    · intro h2; exact hCclosed e.2 e.1 h2 (Or.inr (show (e.1, e.2) ∈ F P by simpa using he))
  · -- internal condition
    intro e he h1
    have hx : e.1 ∈ L := List.mem_toFinset.mp h1
    have hstep := chain_step_mem hLchain hLlast hx
      (succ_some_of_edge (houtcard e.1) (show (e.1, e.2) ∈ F P by simpa using he))
    show e ∈ (⟨L, hLne, hLnodup⟩ : HPath k).edges
    rw [HPath.edges, List.mem_toFinset]
    simpa using hstep

/-! ## Each component of `F(P)` contains full 1-cycles (`cor_exitlessrule`) -/

/-- The vertex set of a path-component is closed under `weakStep` (both edge orientations). -/
theorem pc_vertsFinset_weakstep {P p : HPath k} (hp : IsPathComponent p (F P)) {x y : Vtx k}
    (hx : x ∈ p.vertsFinset) (hxy : weakStep (F P) x y) : y ∈ p.vertsFinset := by
  rcases hxy with h | h
  · exact (hp.2.1 (x, y) h).mp hx
  · exact (hp.2.1 (y, x) h).mpr hx

theorem pc_vertsFinset_weakconn {P p : HPath k} (hp : IsPathComponent p (F P)) {x y : Vtx k}
    (hx : x ∈ p.vertsFinset) (hxy : weakConn (F P) x y) : y ∈ p.vertsFinset := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact pc_vertsFinset_weakstep hp ih hstep

/-- The 1-edge chain `c₀ → σc₀ → ⋯` from a `C₀` vertex stays weakly connected in `F(P)`
(the whole 1-cycle sits in one component). -/
theorem weakConn_c0_forward {P : HPath k} (hP : P.IsHamiltonian) {c0 : Vtx k}
    (hc0 : c0 ∈ C0 P) : ∀ b, b < k → weakConn (F P) c0 (sigma^[b] c0) := by
  intro b
  induction b with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro hb
    have hcn : weakConn (F P) c0 (sigma^[n] c0) := ih (by omega)
    have hnotCm1 : sigma^[n] c0 ∉ Cm1 P := by
      rw [mem_Cm1_iff]
      intro hc
      rw [← Function.iterate_succ_apply' sigma n c0] at hc
      have heq : sigma^[n + 1] c0 = c0 :=
        c0_unique hP (mem_C0_iff.mp hc) (mem_C0_iff.mp hc0)
          (ProofsExitless.rotClass_sigma_iter (n + 1) c0)
      have hcontra : n + 1 = 0 :=
        ProofsExitless.sigma_iter_inj c0 hb (by omega) (by rw [heq]; simp)
      omega
    have hedge : (sigma^[n] c0, sigma (sigma^[n] c0)) ∈ F P :=
      ProofsStructure.mem_F_sigma_of_not_Cm1 hnotCm1
    have hstep : weakConn (F P) c0 (sigma (sigma^[n] c0)) := hcn.tail (Or.inl hedge)
    rwa [← Function.iterate_succ_apply' sigma n c0] at hstep

/-- Each path-component `p` of `F(P)` contains every full 1-cycle of its vertices. -/
theorem cyc_subset_pc {P p : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hp : IsPathComponent p (F P)) {v : Vtx k} (hv : v ∈ p.vertsFinset) :
    cyc v ⊆ p.vertsFinset := by
  intro u hu
  have hk1 : 1 ≤ k := by omega
  have hc0C0 : c0rep P v ∈ C0 P := c0rep_mem_C0 P v
  obtain ⟨ha, hav⟩ := aExp_spec hk1 P v
  have hcv : weakConn (F P) (c0rep P v) v := by
    have := weakConn_c0_forward hP hc0C0 (aExp P v) ha
    rwa [← hav] at this
  have hucyc : u ∈ cyc (c0rep P v) := by
    rw [ProofsExitless.mem_cyc] at hu ⊢
    rw [hu]; exact (c0rep_rotClass P v).symm
  obtain ⟨b, hb, hub⟩ := (ProofsExitless.mem_cyc_iff_exists hk1).mp hucyc
  have hcu : weakConn (F P) (c0rep P v) u := by
    have := weakConn_c0_forward hP hc0C0 b hb
    rwa [← hub] at this
  exact pc_vertsFinset_weakconn hp hv ((weakConn_symm hcv).trans hcu)

end ProofsPathrule

namespace Proved

/-- **lem-pathrule** — `Comps(F(P))` is a set of paths: every component is `V(p)` for a
path-component `p`. -/
theorem lem_pathrule {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) :
    ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P) :=
  ProofsPathrule.lem_pathrule_core hP

/-- **cor-exitlessrule** — `Comps(F(P))` is a set of strongly exitless paths. -/
theorem cor_exitlessrule {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) :
    IsUnionOfStronglyExitlessPaths (F P) := by
  intro C hC
  have hk2 : 2 ≤ k := by
    have hC' := hC
    rw [Comps, Finset.mem_image] at hC'
    obtain ⟨v₀, hv₀V, -⟩ := hC'
    rw [vertsOf, Finset.mem_filter] at hv₀V
    obtain ⟨e₀, he₀X, -⟩ := hv₀V.2
    exact ProofsPathrule.two_le_of_mem_F hP he₀X
  obtain ⟨p, hpV, hp⟩ := ProofsPathrule.lem_pathrule_core hP C hC
  refine ⟨p, hpV, hp, ?_, ?_⟩
  · -- Exitless
    rw [HPath.Exitless]
    intro hEE
    obtain ⟨i, hi1, hw, hlt⟩ := hEE
    by_cases hvCm1 : p.vert i ∈ Cm1 P
    · -- weight-≥2 edge from a `C₋₁` vertex: `σ(vert i)` precedes it, contradicting `hlt`
      have hi : i < p.numVerts := by omega
      have hviv : p.vert i ∈ p.verts := ProofsExitless.vert_mem p hi
      have hsvV : sigma (p.vert i) ∈ p.verts := by
        have hcyc : sigma (p.vert i) ∈ cyc (p.vert i) :=
          ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma (p.vert i))
        exact HPath.mem_vertsFinset.mp
          (ProofsPathrule.cyc_subset_pc hP hk2 hp (HPath.mem_vertsFinset.mpr hviv) hcyc)
      have hposvi : p.pos (p.vert i) = i := ProofsExitless.pos_vert p hi
      have hlt' : p.pos (p.vert i) < p.pos (sigma (p.vert i)) := by rw [hposvi]; exact hlt
      have hord := Proved.clm_ordering hP hp (Finset.mem_union.mpr (Or.inr hvCm1)) hviv hsvV hlt'
      have hsvC0 : sigma (p.vert i) ∈ C0 P := ProofsPathrule.mem_Cm1_iff.mp hvCm1
      have hle : P.pos (sigma (p.vert i)) ≤ P.pos (p.vert i) :=
        (ProofsPathrule.mem_C0_iff.mp hsvC0) (p.vert i)
          (ProofsStructure.rotClass_sigma (p.vert i)).symm
      omega
    · -- weight-1 edge: contradiction with `hw`
      have h2 := Proved.clm_rule2 hP hvCm1
      have hmem : (p.vert i, p.vert (i + 1)) ∈ outV (F P) (p.vert i) := by
        simp only [outV, mem_out, Finset.mem_singleton]
        exact ⟨hp.1 (ProofsStructure.vert_consec_mem_edges hi1), trivial⟩
      rw [h2, Finset.mem_singleton] at hmem
      have hsucc : p.vert (i + 1) = sigma (p.vert i) := (Prod.ext_iff.mp hmem).2
      rw [hsucc, ew_sigma (show (1 : ℕ) ≤ k by omega) (p.vert i)] at hw
      omega
  · -- `σ(p.last) ∈ p` (whole 1-cycle of the head sits in `p`)
    have hcyc : sigma p.last ∈ cyc p.last :=
      ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma p.last)
    exact HPath.mem_vertsFinset.mp
      (ProofsPathrule.cyc_subset_pc hP hk2 hp (HPath.mem_vertsFinset.mpr p.last_mem) hcyc)

/-- **prp-Xk-se (necessity)** — discharged form (no cross-track hypothesis).  For `k ≥ 2`,
`X ∈ 𝒳_k ⟹ V(X) = V(𝒮_k) ∧ Comps(X)` is a set of strongly exitless paths.

**AMENDED from the verbatim `Statements.lean` type: added the guard `2 ≤ k`.**  The verbatim
statement is FALSE at `k ≤ 1`: there every vertex is in `C₋₁`, so `F(P) = ∅`, giving
`vertsOf (F P) = ∅ ≠ Finset.univ` (a singleton for `k = 1`).  This just re-exposes the
structure track's `prp_Xk_se_necessity_amended`, now with its cross-track hypothesis `h_se`
discharged by `cor_exitlessrule` (proved above).  See `PROGRESS-pathrule.md`. -/
theorem prp_Xk_se_necessity_amended' {k : ℕ} {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k)
    (hX : X ∈ Xk k) : vertsOf X = Finset.univ ∧ IsUnionOfStronglyExitlessPaths X :=
  prp_Xk_se_necessity_amended hk (fun _ hP => cor_exitlessrule hP) hX

end Proved

end Hunter

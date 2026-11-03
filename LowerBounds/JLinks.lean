import LowerBounds.TheoremA

/-!
# Theorem L: a junction is a short route

the written proofs of the joint conditions, section 7.  A preimage chain `s` of a Hamiltonian path `P` has
slots `v₁, …, v_j ∈ S(P)` (`actualChainRoute s`), a source component `B` and, if it does not end
at `P.last`, a target component `A`.  `P` contains the edges `head B → σ v₁`, `v_i → σ v_{i+1}`
and `v_j → tail A`, of weights `w₀, …, w_j`.  The junction cost is

  `c(s) = (w₀ - 2) + Σ_{0<i<j} (w_i - 1) + (w_j - 2)`        (`junctionCost`).

The paper states `ew (head B) (tail A) ≤ c(s) + 3`.  Its proof gives more, and this file proves
the stronger form:

* `link_offset`: `c(s) + 3` is an overlap offset from `head B` to `tail A`, that is, `tail A`
  begins with `head B` without its first `c(s) + 3` letters;
* `theoremL`: `ew (head B) (tail A) ≤ c(s) + 3` (the statement of the paper), for `k ≥ 2`;
* `theoremL_eq`: if `c(s) + 3 < k` then `ew (head B) (tail A) = c(s) + 3`.  A permutation word
  has at most one overlap offset below `k` with a given word, so the inequality cannot be strict
  unless it is empty.  At `c(s) + 3 = k` equality can fail;
* `route_length_le`: the chain has at most `c(s) + 1` slots, because every edge out of a slot
  has weight at least 2;
* `junctionCost_eq`: `c(s) = g(s) + (μ_A - 2)` with Liu's cost `g = actualChainRouteNatCost` and
  `μ = compMinto`; `junctionCost_eq_zero_iff`: `c(s) = 0` exactly for the junctions that
  the paper calls free (`g = 0` and `μ = 2`).

The word statements (`offset_rho_step`, `offset_route`) use neither the path nor `S(P)`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

/-! ### Words: overlap offsets -/

/-- `d` is an overlap offset from `u` to `v`: `u` without its first `d` letters is the beginning
of `v`.  `wt k u v` is the least offset in `[1, k]`, and every `d ≥ k` is an offset. -/
def Offset (k d : ℕ) (u v : List ℕ) : Prop := u.drop d = v.take (k - d)

theorem offset_wt (hk : 1 ≤ k) {u v : List ℕ} (hu : u.length = k) :
    Offset k (wt k u v) u v :=
  (wt_spec hk (le_of_eq hu)).2.2

theorem wt_le_of_offset (hk : 1 ≤ k) {d : ℕ} {u v : List ℕ} (hu : u.length = k) (h1 : 1 ≤ d)
    (h : Offset k d u v) : wt k u v ≤ d := by
  by_cases hd : d ≤ k
  · exact wt_le h1 hd h
  · have := (wt_spec (u := u) (v := v) hk (le_of_eq hu)).2.1
    omega

/-- A permutation word has at most one overlap offset below `k` with a given word. -/
theorem wt_eq_of_offset (hk : 1 ≤ k) {d : ℕ} {u v : List ℕ} (hu : IsPermWord k u)
    (h1 : 1 ≤ d) (hd : d < k) (h : Offset k d u v) : wt k u v = d := by
  have hlen := hu.length
  have hle : wt k u v ≤ d := wt_le h1 (le_of_lt hd) h
  obtain ⟨e1, _, e3⟩ := wt_spec (u := u) (v := v) hk (le_of_eq hlen)
  by_contra hne
  have hlt : wt k u v < d := lt_of_le_of_ne hle hne
  generalize wt k u v = e at e1 e3 hlt
  have h' : u.drop d = v.take (k - d) := h
  have a1 : (u.drop d)[0]? = (v.take (k - d))[0]? := by rw [h']
  have a2 : (u.drop e)[0]? = (v.take (k - e))[0]? := by rw [e3]
  rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega)] at a1 a2
  have a3 : u[d]? = u[e]? := by
    simpa using a1.trans a2.symm
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at a3
  have a4 := (hu.nodup.getElem_inj_iff).mp (Option.some.inj a3)
  omega

/-- Two overlaps through a rotation compose, and one letter is saved: an offset `a` from `u` to
`σ v` and an offset `b` from `v` to `x` give the offset `a + b - 1` from `u` to `x`. -/
theorem offset_rho_step (hk : 1 ≤ k) {u v x : List ℕ} (hv : v.length = k)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : Offset k a u (rho v)) (h2 : Offset k b v x) : Offset k (a + b - 1) u x := by
  have h1' : u.drop a = (rho v).take (k - a) := h1
  have h2' : v.drop b = x.take (k - b) := h2
  show u.drop (a + b - 1) = x.take (k - (a + b - 1))
  have e0 : (rho v).take (k - a) = (v.drop 1).take (k - a) := by
    rw [rho, List.rotate_eq_drop_append_take (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  calc u.drop (a + b - 1) = (u.drop a).drop (b - 1) := by
        rw [List.drop_drop]
        congr 1
        omega
    _ = ((v.drop 1).take (k - a)).drop (b - 1) := by rw [h1', e0]
    _ = ((v.drop 1).drop (b - 1)).take (k - a - (b - 1)) := by rw [List.drop_take]
    _ = (v.drop b).take (k - a - (b - 1)) := by
        rw [List.drop_drop]
        congr 2
        omega
    _ = (x.take (k - b)).take (k - a - (b - 1)) := by rw [h2']
    _ = x.take (k - (a + b - 1)) := by
        rw [List.take_take]
        congr 1
        omega

/-- The offset of a route.  From `h` an offset `a` leads to `σ v₁`; then the route passes
`v₁, …, v_j` (each `v_i` to `σ v_{i+1}`) and ends with the step from `v_j` to `t`.  Every step
after the first saves one letter. -/
theorem offset_route (hk : 1 ≤ k) (h t : Vtx k) :
    ∀ (L : List (Vtx k)) (hne : L ≠ []) (a : ℕ), 1 ≤ a →
      Offset k a h.1 (sigma (L.head hne)).1 →
      Offset k (a + ((L.zip L.tail).map (fun d => ew k d.1 (sigma d.2) - 1)).sum +
          ew k (L.getLast hne) t - 1) h.1 t.1
  | [], hne, _, _, _ => absurd rfl hne
  | [v], _, a, ha, hoff => by
      have hb : 1 ≤ ew k v t := (wt_spec hk (le_of_eq v.2.length)).1
      have h2 : Offset k (ew k v t) v.1 t.1 := offset_wt hk v.2.length
      have hstep := offset_rho_step hk v.2.length ha hb hoff h2
      simpa using hstep
  | v :: w :: rest, _, a, ha, hoff => by
      have hb : 1 ≤ ew k v (sigma w) := (wt_spec hk (le_of_eq v.2.length)).1
      have h2 : Offset k (ew k v (sigma w)) v.1 (sigma w).1 := offset_wt hk v.2.length
      have hstep : Offset k (a + ew k v (sigma w) - 1) h.1 (sigma w).1 :=
        offset_rho_step hk v.2.length ha hb hoff h2
      have ih := offset_route hk h t (w :: rest) (List.cons_ne_nil _ _)
        (a + ew k v (sigma w) - 1) (by omega) hstep
      have hnum : a + (((v :: w :: rest).zip (v :: w :: rest).tail).map
            (fun d => ew k d.1 (sigma d.2) - 1)).sum +
          ew k ((v :: w :: rest).getLast (List.cons_ne_nil _ _)) t - 1 =
          a + ew k v (sigma w) - 1 + (((w :: rest).zip (w :: rest).tail).map
            (fun d => ew k d.1 (sigma d.2) - 1)).sum +
          ew k ((w :: rest).getLast (List.cons_ne_nil _ _)) t - 1 := by
        simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
          List.getLast_cons_cons]
        omega
      rw [hnum]
      exact ih

/-! ### Chains of a Hamiltonian path -/

section Path

variable {P : HPath k}

/-- The end of a chain that does not end at `P.last`, as an element of Liu's subtype. -/
noncomputable def ntEnd (s : {v : Vtx k // v ∈ chainStarts P})
    (hs : actualChainRouteEnd s ≠ P.last) : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
  ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hs⟩

/-- The junction cost `c(s)` of a chain that does not end at `P.last`:
`(w₀ - 2) + Σ (w_i - 1) + (w_j - 2)` over the edges `head B → σ v₁`, `v_i → σ v_{i+1}`,
`v_j → tail A` of `P`. -/
noncomputable def junctionCost (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) : ℕ :=
  (ew k (chainSourceHead hP s).1 (sigma s.1) - 2) +
    slotInternalCost (actualChainSlotSequence s) +
    (ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 - 2)

/-- An edge of `D_P` is an edge of `P` of weight at least 2: its source is in `S(P)`. -/
theorem chainEdge_ge_two (hk : 1 ≤ k) {a b : Vtx k} (h : (a, b) ∈ chainGraph P) :
    2 ≤ ew k a (sigma b) := by
  obtain ⟨haS, _, hedge⟩ := mem_chainGraph.mp h
  have h1 := Hunter.ProofsExitless.ew_ge_one hk a (sigma b)
  have hne : ew k a (sigma b) ≠ 1 := by
    intro hone
    have heq : sigma b = sigma a := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    exact Hunter.sset_sPrecond P a haS (heq ▸ hedge)
  omega

/-- The first edge of a chain, from the head of the source component, has weight at least 2. -/
theorem entry_ge_two (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) :
    2 ≤ ew k (chainSourceHead hP s).1 (sigma s.1) := by
  exact_mod_cast (sub_nonneg.mp (chainEntry_excess_nonneg hP hk s))

/-- The last edge of a chain, into the tail of the target component, has weight at least 2. -/
theorem exit_ge_two (hk : 1 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    2 ≤ ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 := by
  have hS : actualChainRouteEnd s ∈ Sset P :=
    (mem_chainEnds.mp (actualChainRouteEnd_mem_chainEnds s)).1
  have hedge : (actualChainRouteEnd s, (chainTargetTail hP (ntEnd s hs)).1) ∈ P.edges :=
    E1removed_subset P (Sset P) (chainTargetTail_spec hP (ntEnd s hs))
  have h1 := Hunter.ProofsExitless.ew_ge_one hk (actualChainRouteEnd s)
    (chainTargetTail hP (ntEnd s hs)).1
  have hne : ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 ≠ 1 := by
    intro hone
    have heq := (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    exact Hunter.sset_sPrecond P _ hS (heq ▸ hedge)
  omega

/-- A list that is a path of `D_P` has internal cost at least its number of edges. -/
theorem length_le_internal (hk : 1 ≤ k) :
    ∀ (L : List (Vtx k)), L.IsChain (fun a b => (a, b) ∈ chainGraph P) →
      L.length ≤ ((L.zip L.tail).map (fun d => ew k d.1 (sigma d.2) - 1)).sum + 1
  | [], _ => by simp
  | [_], _ => by simp
  | v :: w :: rest, hc => by
      rw [List.isChain_cons_cons] at hc
      have ih := length_le_internal hk (w :: rest) hc.2
      have h2 : 2 ≤ ew k v (sigma w) := chainEdge_ge_two hk hc.1
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

/-- A chain has at most `c(s) + 1` slots. -/
theorem route_length_le (hk : 1 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    (actualChainRoute s).length ≤ junctionCost hP s hs + 1 := by
  have h := length_le_internal hk (actualChainRoute s) (actualChainRoute_isChain s)
  have hint : slotInternalCost (actualChainSlotSequence s) =
      (((actualChainRoute s).zip (actualChainRoute s).tail).map
        (fun d => ew k d.1 (sigma d.2) - 1)).sum := rfl
  unfold junctionCost
  omega

/-- **Theorem L, offset form.**  `c(s) + 3` is an overlap offset from the head of the source
component to the tail of the target component. -/
theorem link_offset (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    Offset k (junctionCost hP s hs + 3) (chainSourceHead hP s).1.1
      (chainTargetTail hP (ntEnd s hs)).1.1 := by
  have hk1 : 1 ≤ k := by omega
  have h0 := entry_ge_two hk hP s
  have hj := exit_ge_two hk1 hP s hs
  have hoff : Offset k (ew k (chainSourceHead hP s).1 (sigma s.1)) (chainSourceHead hP s).1.1
      (sigma ((actualChainRoute s).head (actualChainRoute_ne_nil s))).1 := by
    rw [actualChainRoute_head]
    exact offset_wt hk1 (chainSourceHead hP s).1.2.length
  have h := offset_route hk1 (chainSourceHead hP s).1 (chainTargetTail hP (ntEnd s hs)).1
    (actualChainRoute s) (actualChainRoute_ne_nil s) _ (by omega) hoff
  have hint : slotInternalCost (actualChainSlotSequence s) =
      (((actualChainRoute s).zip (actualChainRoute s).tail).map
        (fun d => ew k d.1 (sigma d.2) - 1)).sum := rfl
  have hlast : (actualChainRoute s).getLast (actualChainRoute_ne_nil s) =
      actualChainRouteEnd s := rfl
  rw [hlast, ← hint] at h
  have hnum : junctionCost hP s hs + 3 =
      ew k (chainSourceHead hP s).1 (sigma s.1) + slotInternalCost (actualChainSlotSequence s) +
        ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 - 1 := by
    unfold junctionCost
    omega
  rw [hnum]
  exact h

/-- **Theorem L** (the written proofs of the joint conditions, section 7), for `k ≥ 2` and every Hamiltonian path:
`ew (head B(s)) (tail A(s)) ≤ c(s) + 3`. -/
theorem theoremL (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    ew k (actualComponentHead hP (actualChainSourceComponent hP hk s))
        (actualComponentTail hP (actualNonterminalTargetComponent hP hk (ntEnd s hs))) ≤
      junctionCost hP s hs + 3 := by
  rw [actualChainSourceComponent_head hP hk s, actualNonterminalTargetComponent_tail hP hk]
  exact wt_le_of_offset (by omega) (chainSourceHead hP s).1.2.length (by omega)
    (link_offset hk hP s hs)

/-- **Theorem L with equality.**  If `c(s) + 3 < k`, the weight from the head of the source to
the tail of the target is exactly `c(s) + 3`. -/
theorem theoremL_eq (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last)
    (hlt : junctionCost hP s hs + 3 < k) :
    ew k (actualComponentHead hP (actualChainSourceComponent hP hk s))
        (actualComponentTail hP (actualNonterminalTargetComponent hP hk (ntEnd s hs))) =
      junctionCost hP s hs + 3 := by
  rw [actualChainSourceComponent_head hP hk s, actualNonterminalTargetComponent_tail hP hk]
  exact wt_eq_of_offset (by omega) (chainSourceHead hP s).1.2 (by omega) hlt
    (link_offset hk hP s hs)

/-- The junction cost in Liu's terms: `c(s) = g(s) + (μ_{A(s)} - 2)`. -/
theorem junctionCost_eq (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    junctionCost hP s hs = actualChainRouteNatCost hP hk s +
      (compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1 - 2) := by
  have hmu2 : 2 ≤ compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1 :=
    actual_component_minto_ge_two hP hk _ (ne_univ_of_ne hP (target_ne_root hP hk (ntEnd s hs)))
  have hexit : compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1 ≤
      ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 := by
    exact_mod_cast (sub_nonneg.mp (chainExit_excess_nonneg hP hk (ntEnd s hs)))
  have h0 := entry_ge_two hk hP s
  have hcost : actualChainRouteNatCost hP hk s =
      ew k (chainSourceHead hP s).1 (sigma s.1) - 2 +
        slotInternalCost (actualChainSlotSequence s) +
        (ew k (actualChainRouteEnd s) (chainTargetTail hP (ntEnd s hs)).1 -
          compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1) := by
    unfold actualChainRouteNatCost
    rw [dif_neg hs]
    dsimp only
    unfold slotRouteCost slotRouteStarCost
    rw [actualChainSourceComponent_head hP hk s, actualChainSlotSequence_first,
      actualChainSlotSequence_last]
    have ht := actualNonterminalTargetComponent_tail hP hk (ntEnd s hs)
    unfold ntEnd at ht ⊢
    rw [ht]
  rw [hcost]
  unfold junctionCost
  omega

/-- `c(s) = 0` exactly when Liu's cost is zero and the target has minimum entry weight 2: the
free junctions of the paper. -/
theorem junctionCost_eq_zero_iff (hk : 2 ≤ k) (hP : P.IsHamiltonian)
    (s : {v : Vtx k // v ∈ chainStarts P}) (hs : actualChainRouteEnd s ≠ P.last) :
    junctionCost hP s hs = 0 ↔
      actualChainRouteNatCost hP hk s = 0 ∧
        compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1 = 2 := by
  have hmu2 : 2 ≤ compMinto (F P) (actualNonterminalTargetComponent hP hk (ntEnd s hs)).1 :=
    actual_component_minto_ge_two hP hk _ (ne_univ_of_ne hP (target_ne_root hP hk (ntEnd s hs)))
  rw [junctionCost_eq hk hP s hs]
  omega

end Path

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.offset_rho_step
#print axioms SuperpermLowerBounds.wt_eq_of_offset
#print axioms SuperpermLowerBounds.link_offset
#print axioms SuperpermLowerBounds.theoremL
#print axioms SuperpermLowerBounds.theoremL_eq
#print axioms SuperpermLowerBounds.route_length_le
#print axioms SuperpermLowerBounds.junctionCost_eq
#print axioms SuperpermLowerBounds.junctionCost_eq_zero_iff

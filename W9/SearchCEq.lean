import W9.SearchC

/-!
# The compiled copy of the window search is the window search

Every function of `W9/SearchC.lean` is equal to the function of `SSearch.lean` that it copies.  The
proofs use only the equations that `SSearch.lean` proves after each definition.  The result is
`searchC_eq : searchC k A q2 C1 C2 bn fuel = search k A q2 C1 C2 bn fuel` and
`runSearchC_eq : runSearchC k = runSearch k`.  Checked by the kernel; no `native_decide`.
-/

namespace SuperpermLowerBounds
namespace S

theorem idcC_eq (n : Nat) : idcC n = idc n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [idcC, idc_succ, ih]

theorem Tr.memC_eq (t : Tr) (x : Nat) : Tr.memC t x = Tr.mem t x := by
  induction t with
  | leaf => rfl
  | node l key r ihl ihr => rw [Tr.memC, Tr.mem_node, ihl, ihr]

theorem Tr.insC_eq (t : Tr) (x : Nat) : Tr.insC t x = Tr.ins t x := by
  induction t with
  | leaf => rfl
  | node l key r ihl ihr => rw [Tr.insC, Tr.ins_node, ihl, ihr]

theorem kidC_eq (A q2 C2 P N f d x : Nat) (T : Tr) (acc : List St) :
    kidC A q2 C2 P N f d x T acc = kid A q2 C2 P N f d x T acc :=
  (kid_eq A q2 C2 P N f d x T acc).symm

theorem walkC_eq (k A q2 C2 P N f : Nat) :
    ∀ (n D : Nat) (T : Tr) (acc : List St),
      walkC k A q2 C2 P N f n D T acc = walk k A q2 C2 P N f n D T acc := by
  intro n
  induction n with
  | zero => intro D T acc; rfl
  | succ n ih =>
    intro D T acc
    rw [walkC, walk_succ, Tr.memC_eq, Tr.insC_eq, kidC_eq, ih]

theorem childrenC_eq (k A q2 C2 : Nat) (st : St) :
    childrenC k A q2 C2 st = children k A q2 C2 st := by
  have h : (fun D acc => walkC k A q2 C2 st.P st.N st.f (Nat.sub k 1) D st.T acc) =
      (fun D acc => walk k A q2 C2 st.P st.N st.f (Nat.sub k 1) D st.T acc) := by
    funext D acc
    exact walkC_eq k A q2 C2 st.P st.N st.f (Nat.sub k 1) D st.T acc
  unfold childrenC children
  rw [h]

theorem anyIdxC_eq (f : St → Nat → Bool) :
    ∀ (l : List St) (j : Nat), anyIdxC f l j = anyIdx f l j := by
  intro l
  induction l with
  | nil => intro j; rfl
  | cons c t ih => intro j; rw [anyIdxC, anyIdx_cons, ih]

theorem violC_eq (C1 bn : Nat) (st : St) : violC C1 bn st = viol C1 bn st :=
  (viol_eq C1 bn st).symm

theorem goKC_eq (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) :
    ∀ (fuel : Nat) (st : St) (key : List Nat),
      goKC k A q2 C1 C2 bn leaf fuel st key = goK k A q2 C1 C2 bn leaf fuel st key := by
  intro fuel
  induction fuel with
  | zero => intro st key; rfl
  | succ fuel ih =>
    intro st key
    have h : (fun c i => goKC k A q2 C1 C2 bn leaf fuel c (i :: key)) =
        (fun c i => goK k A q2 C1 C2 bn leaf fuel c (i :: key)) := by
      funext c i
      exact ih c (i :: key)
    rw [goKC, goK_succ, violC_eq, childrenC_eq, anyIdxC_eq, h]

theorem rootChildrenC_eq (k A q2 C2 : Nat) : rootChildrenC k A q2 C2 = rootChildren k A q2 C2 := by
  unfold rootChildrenC rootChildren
  rw [walkC_eq, idcC_eq]

/-- **The compiled search is the search.** -/
theorem searchC_eq (k A q2 C1 C2 bn fuel : Nat) :
    searchC k A q2 C1 C2 bn fuel = search k A q2 C1 C2 bn fuel := by
  have h : (fun c i => goKC k A q2 C1 C2 bn (fun _ _ => true) fuel c [i]) =
      (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [i]) := by
    funext c i
    exact goKC_eq k A q2 C1 C2 bn (fun _ _ => true) fuel c [i]
  unfold searchC search
  rw [rootChildrenC_eq, anyIdxC_eq, h]

theorem runStartC_eq (k : Nat) : runStartC k = runStart k := by
  unfold runStartC runStart
  rw [Tr.insC_eq, idcC_eq]

/-- The compiled run check is the run check. -/
theorem runSearchC_eq (k : Nat) : runSearchC k = runSearch k := by
  unfold runSearchC runSearch
  rw [goKC_eq, runStartC_eq]

end S
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.S.searchC_eq
#print axioms SuperpermLowerBounds.S.runSearchC_eq

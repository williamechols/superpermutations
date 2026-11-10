import LowerBounds.SSearch

/-!
# States written out

A part of a search begins at a state deep in the tree.  Reaching that state from the first piece
by `stepPath` costs one evaluated state per piece of the path, in every lemma about it.  For deep
searches the plan therefore writes the state out (the exit, the tree of used classes, the two
scores and the flag as numbers) and proves once, by evaluation from the nearest written-out state
above it, that this is the state the path leads to: `St.beq (stepPath … parent path) lit = true`.
`St.eq_of_beq` turns this into an equation.

Nothing here is trusted: a wrong literal makes the comparison fail.  This file imports only
`SSearch.lean`.
-/

namespace SuperpermLowerBounds
namespace S

/-- Equality of two trees, as a Boolean (written with recursors, for the kernel). -/
noncomputable def Tr.beq (a : Tr) : Tr → Bool :=
  @Tr.rec (fun _ => Tr → Bool)
    (fun b => @Tr.rec (fun _ => Bool) true (fun _ _ _ _ _ => false) b)
    (fun _ key _ bl br b =>
      @Tr.rec (fun _ => Bool) false
        (fun l' key' r' _ _ =>
          @Bool.rec (fun _ => Bool) false
            (@Bool.rec (fun _ => Bool) false (br r') (bl l')) (Nat.beq key key')) b) a

theorem Tr.beq_leaf_leaf : Tr.beq .leaf .leaf = true := rfl
theorem Tr.beq_leaf_node (l r : Tr) (key : Nat) : Tr.beq .leaf (.node l key r) = false := rfl
theorem Tr.beq_node_leaf (l r : Tr) (key : Nat) : Tr.beq (.node l key r) .leaf = false := rfl

theorem Tr.beq_node_node (l r l' r' : Tr) (key key' : Nat) :
    Tr.beq (.node l key r) (.node l' key' r') =
      (Nat.beq key key' && (Tr.beq l l' && Tr.beq r r')) := by
  show @Bool.rec (fun _ => Bool) false
    (@Bool.rec (fun _ => Bool) false (Tr.beq r r') (Tr.beq l l')) (Nat.beq key key') = _
  cases Nat.beq key key' <;> cases Tr.beq l l' <;> rfl

theorem Tr.eq_of_beq : ∀ (a b : Tr), Tr.beq a b = true → a = b := by
  intro a
  induction a with
  | leaf =>
    intro b h
    cases b with
    | leaf => rfl
    | node l' key' r' =>
      rw [Tr.beq_leaf_node] at h
      cases h
  | node l key r ihl ihr =>
    intro b h
    cases b with
    | leaf =>
      rw [Tr.beq_node_leaf] at h
      cases h
    | node l' key' r' =>
      rw [Tr.beq_node_node, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, ihl l' h.2.1, ihr r' h.2.2]

/-- Equality of two states, as a Boolean. -/
noncomputable def St.beq (a b : St) : Bool :=
  Nat.beq a.y b.y && (Nat.beq a.P b.P && (Nat.beq a.N b.N && (Nat.beq a.f b.f && Tr.beq a.T b.T)))

theorem St.eq_of_beq {a b : St} (h : St.beq a b = true) : a = b := by
  unfold St.beq at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases a with
  | mk y T P N f =>
    cases b with
    | mk y' T' P' N' f' =>
      have e1 : y = y' := Nat.eq_of_beq_eq_true h1
      have e2 : P = P' := Nat.eq_of_beq_eq_true h2
      have e3 : N = N' := Nat.eq_of_beq_eq_true h3
      have e4 : f = f' := Nat.eq_of_beq_eq_true h4
      have e5 : T = T' := Tr.eq_of_beq T T' h5
      rw [e1, e2, e3, e4, e5]

/-- `Ref` for the state that a path leads to, from `Ref` for the written-out state. -/
theorem ref_of_lit {k A q2 C1 C2 bn b : Nat} {st lit : St} (he : St.beq st lit = true)
    (h : Ref k A q2 C1 C2 bn b lit) : Ref k A q2 C1 C2 bn b st := by
  rw [St.eq_of_beq he]
  exact h

end S
end SuperpermLowerBounds

import LowerBounds.SSearch

/-!
# Trees written as lists of numbers

A state of a deep search has a tree of used classes with tens of thousands of numbers.  Written as
a term `Tr.node (Tr.node …) key (…)` it costs Lean's elaborator minutes.  Here the tree is written
as a short list of large numbers, which costs the elaborator almost nothing, and the kernel builds
the tree from the list (`trOf`) when a lemma needs it.

The list is the tree in preorder.  A node is one record `4 * key + 2 * hasRight + hasLeft`
(below `2 ^ 68`); 32 records are packed into one number, the first record in the lowest digits.

Nothing is proved about `trOf` and nothing needs to be: a state written with it is compared, by
evaluation, with the state that the search reaches (`St.beq`, `SLit.lean`).  This file imports only
`SSearch.lean`.
-/

namespace SuperpermLowerBounds
namespace S

/-- `2 ^ 68`: the size of a record. -/
def recB : Nat := 295147905179352825856

/-- The next record of a stream (the rest of the current number, the numbers that follow) and the
stream after it. -/
noncomputable def nextRec (s : Nat × List Nat) : Nat × (Nat × List Nat) :=
  @Bool.rec (fun _ => Nat × (Nat × List Nat))
    (Nat.mod s.1 recB, (Nat.div s.1 recB, s.2))
    (@List.rec Nat (fun _ => Nat × (Nat × List Nat)) (0, (0, []))
      (fun c t _ => (Nat.mod c recB, (Nat.div c recB, t))) s.2)
    (Nat.beq s.1 0)

/-- The tree at the beginning of a stream, of height at most `fuel`, and the stream after it. -/
noncomputable def decTr (fuel : Nat) : Nat × List Nat → Tr × (Nat × List Nat) :=
  @Nat.rec (fun _ => Nat × List Nat → Tr × (Nat × List Nat)) (fun s => (Tr.leaf, s))
    (fun _ ih s =>
      (fun (r : Nat × (Nat × List Nat)) =>
        (fun (pl : Tr × (Nat × List Nat)) =>
          (fun (pr : Tr × (Nat × List Nat)) => (Tr.node pl.1 (Nat.div r.1 4) pr.1, pr.2))
            (@Bool.rec (fun _ => Tr × (Nat × List Nat)) (Tr.leaf, pl.2) (ih pl.2)
              (Nat.beq (Nat.mod (Nat.div r.1 2) 2) 1)))
          (@Bool.rec (fun _ => Tr × (Nat × List Nat)) (Tr.leaf, r.2) (ih r.2)
            (Nat.beq (Nat.mod r.1 2) 1)))
        (nextRec s)) fuel

/-- The tree written as the list `chunks`; `fuel` is at least its height. -/
noncomputable def trOf (fuel : Nat) (chunks : List Nat) : Tr := (decTr fuel (0, chunks)).1

end S
end SuperpermLowerBounds

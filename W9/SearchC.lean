import LowerBounds.SSearch

/-!
# A compiled copy of Halfar's window search

`LowerBounds/SSearch.lean` (Jakub Halfar) defines the window search `S.search` with recursors, for evaluation in the kernel; Lean
does not compile such definitions (they are `noncomputable`).  This file defines the same functions
again by pattern matching, so that they are compiled: `idcC`, `Tr.memC`, `Tr.insC`, `kidC`, `walkC`,
`childrenC`, `anyIdxC`, `violC`, `goKC`, `rootChildrenC`, `searchC`.  The functions of `SSearch.lean`
that are already compiled (`pw`, `exc`, `doorc`, `rotl`, `pos`, `canon`, `six`) are used as they are.

`W9/SearchCEq.lean` proves, with the kernel, that every copy is equal to its original; in particular
`searchC = search`.  This file contains definitions only and imports `SSearch.lean` only.
-/

namespace SuperpermLowerBounds
namespace S

/-- Compiled copy of `idc`. -/
def idcC : Nat → Nat
  | 0 => 0
  | n + 1 => idcC n * 16 + (n + 1)

/-- Compiled copy of `Tr.mem`. -/
def Tr.memC : Tr → Nat → Bool
  | .leaf, _ => false
  | .node l key r, x =>
    bif Nat.ble key x then (bif Nat.ble x key then true else Tr.memC r x) else Tr.memC l x

/-- Compiled copy of `Tr.ins`. -/
def Tr.insC : Tr → Nat → Tr
  | .leaf, x => .node .leaf x .leaf
  | .node l key r, x =>
    bif Nat.ble key x then .node l key (Tr.insC r x) else .node (Tr.insC l x) key r

/-- Compiled copy of `kid` (the right-hand side of `kid_eq`). -/
def kidC (A q2 C2 P N f d x : Nat) (T : Tr) (acc : List St) : List St :=
  bif Nat.beq d 0 then
    (bif Nat.beq f 1 then acc else (⟨x, T, P, N + q2, 0⟩ :: acc))
  else bif Nat.ble (N + q2 + C2) (P + A * d) then acc
  else bif Nat.beq f 0 then
    (bif Nat.ble N P then acc
      else (⟨x, T, P + A * d, N + q2, bif Nat.ble 2 d then 2 else 1⟩ :: acc))
  else (⟨x, T, P + A * d, N + q2, bif Nat.ble 2 d then 2 else f⟩ :: acc)

/-- Compiled copy of `walk`. -/
def walkC (k A q2 C2 P N f : Nat) : Nat → Nat → Tr → List St → List St
  | 0, _, _, acc => acc
  | n + 1, D, T, acc =>
    bif Tr.memC T (canon k D) then acc
    else walkC k A q2 C2 P N f n (doorc k (exc k D)) (Tr.insC T (canon k D))
        (kidC A q2 C2 P N f n (exc k D) (Tr.insC T (canon k D)) acc)

/-- Compiled copy of `children`. -/
def childrenC (k A q2 C2 : Nat) (st : St) : List St :=
  six (fun D acc => walkC k A q2 C2 st.P st.N st.f (Nat.sub k 1) D st.T acc)
    (Nat.mul (Nat.mod st.y (pw (Nat.sub k 3))) 4096) (Nat.div st.y (pw (Nat.sub k 1)))
    (Nat.mod (Nat.div st.y (pw (Nat.sub k 2))) 16) (Nat.mod (Nat.div st.y (pw (Nat.sub k 3))) 16)

/-- Compiled copy of `anyIdx`. -/
def anyIdxC (f : St → Nat → Bool) : List St → Nat → Bool
  | [], _ => false
  | c :: t, j => f c j || anyIdxC f t (j + 1)

/-- Compiled copy of `viol` (the right-hand side of `viol_eq`). -/
def violC (C1 bn : Nat) (st : St) : Bool :=
  Nat.beq st.f 2 && !Nat.ble (st.N + C1) (st.P + bn)

/-- Compiled copy of `goK`. -/
def goKC (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) : Nat → St → List Nat → Bool
  | 0, st, key => leaf st key
  | fuel + 1, st, key =>
    bif violC C1 bn st then true
    else anyIdxC (fun c i => goKC k A q2 C1 C2 bn leaf fuel c (i :: key)) (childrenC k A q2 C2 st) 0

/-- Compiled copy of `rootChildren`. -/
def rootChildrenC (k A q2 C2 : Nat) : List St :=
  walkC k A q2 C2 0 0 1 (Nat.sub k 1) (idcC k) Tr.leaf []

/-- Compiled copy of `search`. -/
def searchC (k A q2 C1 C2 bn fuel : Nat) : Bool :=
  anyIdxC (fun c i => goKC k A q2 C1 C2 bn (fun _ _ => true) fuel c [i]) (rootChildrenC k A q2 C2) 0

/-- Compiled copy of `runStart`. -/
def runStartC (k : Nat) : St :=
  ⟨exc k (idcC k), Tr.insC Tr.leaf (canon k (idcC k)), 0, 0, 0⟩

/-- Compiled copy of `runSearch`. -/
def runSearchC (k : Nat) : Bool :=
  goKC k 0 0 0 0 0 (fun _ _ => true) (Nat.sub k 2) (runStartC k) []

end S
end SuperpermLowerBounds

/-!
# The window search on numbers

A search that the Lean kernel can evaluate: it looks for a window (a chain of pieces that starts and
ends with a partial piece) that violates the bound

  `2 q r + 2 q (k - 4) + cn δ ≤ q (k - 3) δ + bn`      (`r` pieces, total deficit `δ`),

and it looks only among the violating windows with the fewest pieces.  `SSound.lean` proves that
if the search returns `false` then no chain of the model violates the bound.

Everything is a natural number:

* a word (a permutation of `1 … k`) is its *code*, the word read as `k` hexadecimal digits, first
  symbol first;
* the set of used rotation classes is a binary search tree `Tr` of codes, one per class (the
  rotation that begins with the symbol `k`, `canon`);
* the score of a prefix is kept as two numbers, `P = A δ` with `A = q (k - 3) - cn`, and
  `N = q2 r` with `q2 = 2 q`; the bound for a window is `N + C1 ≤ P + bn` with
  `C1 = 2 q (k - 4)`.

The rules of the search:

* the first piece is partial and its first entry is the word `1 2 … k`;
* a full piece may follow a partial piece only if the interval that it closes contains a piece of
  deficit at least 2 (otherwise the chain is not a window);
* a partial piece may follow a full piece only if `P < N` (otherwise the pieces that follow form a
  shorter window that violates the bound as well);
* a prefix that ends with a partial piece and has `N + C2 ≤ P`, `C2 = 2 q (k - 3)`, is dropped (a
  run of full pieces has at most `k - 3` pieces, so the score cannot become negative again);
* found: a prefix that ends with a partial piece, whose last interval contains a piece of deficit
  at least 2, with `P + bn < N + C1`.

The run bound is itself checked by the same function (`runSearch`): no chain consists of one block
followed by `k - 2` full pieces.

This file imports nothing, so that the generated files which evaluate the search load quickly.
The definitions are written for the kernel: `Nat.add`, `Nat.mul` and so on without notation, and
recursors (`Nat.rec`, `List.rec`, `Tr.rec`, `Bool.rec`) instead of pattern matching, which saves
most of the unfolding steps.  The equations that pattern matching would give are proved after each
definition (`…_zero`, `…_succ`, `…_node`, `…_eq`); nothing else is used about these definitions.
-/

namespace SuperpermLowerBounds
namespace S

/-- `sel(c, a, b)` is `a` if `c` is `true` and `b` otherwise, written with the recursor. -/
local macro "sel(" c:term ", " a:term ", " b:term ")" : term => `(@Bool.rec (fun _ => _) $b $a $c)

theorem cond_rec {α : Type} (c : Bool) (a b : α) :
    @Bool.rec (fun _ => α) b a c = (bif c then a else b) := by
  cases c <;> rfl

/-! ### Arithmetic on codes -/

/-- `16 ^ n`. -/
def pw (n : Nat) : Nat := Nat.pow 16 n

/-- The code of the word `1 2 … n`. -/
noncomputable def idc (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun n c => Nat.add (Nat.mul c 16) (Nat.succ n)) n

theorem idc_zero : idc 0 = 0 := rfl
theorem idc_succ (n : Nat) : idc (n + 1) = idc n * 16 + (n + 1) := rfl

/-- The exit of a block from its entry: the last of the `k` digits moves to the front. -/
def exc (k c : Nat) : Nat := Nat.add (Nat.mul (Nat.mod c 16) (pw (Nat.sub k 1))) (Nat.div c 16)

/-- The door: the first two of the `k` digits move to the end, in reverse order. -/
def doorc (k x : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (Nat.mod x (pw (Nat.sub k 2))) 256)
    (Nat.mul (Nat.mod (Nat.div x (pw (Nat.sub k 2))) 16) 16)) (Nat.div x (pw (Nat.sub k 1)))

/-- The `k` digits rotated to the left by `i` digits (`i ≤ k`). -/
def rotl (k c i : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.mod c (pw (Nat.sub k i))) (pw i)) (Nat.div c (pw (Nat.sub k i)))

/-- The position, counted from the right, of the digit `k` among the digits of `c` (found by
operations on bits; nothing is proved about it, and nothing needs to be). -/
def pos (k c : Nat) : Nat :=
  Nat.div (Nat.log2 (Nat.xor (Nat.land
    (Nat.lor (Nat.add (Nat.land (Nat.xor c (Nat.mul k 0x1111111111111111)) 0x7777777777777777)
      0x7777777777777777) (Nat.xor c (Nat.mul k 0x1111111111111111)))
    0x8888888888888888) 0x8888888888888888)) 4

/-- A rotation of `c` (the one that begins with the digit `k`): the name of its rotation class. -/
def canon (k c : Nat) : Nat := rotl k c (Nat.sub (Nat.sub k 1) (pos k c))

/-! ### Sets of codes -/

/-- A binary search tree of numbers. -/
inductive Tr where
  | leaf : Tr
  | node : Tr → Nat → Tr → Tr

/-- Is `x` in the tree? -/
noncomputable def Tr.mem (t : Tr) : Nat → Bool :=
  @Tr.rec (fun _ => Nat → Bool) (fun _ => false)
    (fun _ key _ ml mr x => sel(Nat.ble key x, sel(Nat.ble x key, true, mr x), ml x)) t

theorem Tr.mem_leaf (x : Nat) : Tr.mem .leaf x = false := rfl

theorem Tr.mem_node (l r : Tr) (key x : Nat) : Tr.mem (.node l key r) x =
    bif Nat.ble key x then (bif Nat.ble x key then true else Tr.mem r x) else Tr.mem l x := by
  show sel(Nat.ble key x, sel(Nat.ble x key, true, Tr.mem r x), Tr.mem l x) = _
  rw [cond_rec, cond_rec]

/-- The tree with `x` added. -/
noncomputable def Tr.ins (t : Tr) : Nat → Tr :=
  @Tr.rec (fun _ => Nat → Tr) (fun x => .node .leaf x .leaf)
    (fun l key r il ir x => sel(Nat.ble key x, .node l key (ir x), .node (il x) key r)) t

theorem Tr.ins_leaf (x : Nat) : Tr.ins .leaf x = .node .leaf x .leaf := rfl

theorem Tr.ins_node (l r : Tr) (key x : Nat) : Tr.ins (.node l key r) x =
    bif Nat.ble key x then .node l key (Tr.ins r x) else .node (Tr.ins l x) key r := by
  show sel(Nat.ble key x, Tr.node l key (Tr.ins r x), Tr.node (Tr.ins l x) key r) = _
  rw [cond_rec]

/-! ### The search -/

/-- A state of the search: a chain of pieces, of which only this is kept. -/
structure St where
  /-- code of the exit of the last block -/
  y : Nat
  /-- the used rotation classes -/
  T : Tr
  /-- `A` times the total deficit -/
  P : Nat
  /-- `q2` times the number of pieces -/
  N : Nat
  /-- `0`: the last piece is full; `2`: it is partial and its interval contains a piece of
  deficit at least 2; `1`: it is partial and its interval does not (also: no piece yet) -/
  f : Nat

/-- The state after a piece of deficit `d` whose last block has exit `x`, put in front of `acc` if
the rules allow the piece. -/
noncomputable def kid (A q2 C2 P N f d x : Nat) (T : Tr) (acc : List St) : List St :=
  sel(Nat.beq d 0,
    sel(Nat.beq f 1, acc, (⟨x, T, P, Nat.add N q2, 0⟩ :: acc)),
    sel(Nat.ble (Nat.add (Nat.add N q2) C2) (Nat.add P (Nat.mul A d)), acc,
      sel(Nat.beq f 0,
        sel(Nat.ble N P, acc,
          (⟨x, T, Nat.add P (Nat.mul A d), Nat.add N q2, sel(Nat.ble 2 d, 2, 1)⟩ :: acc)),
        (⟨x, T, Nat.add P (Nat.mul A d), Nat.add N q2, sel(Nat.ble 2 d, 2, f)⟩ :: acc))))

theorem kid_eq (A q2 C2 P N f d x : Nat) (T : Tr) (acc : List St) :
    kid A q2 C2 P N f d x T acc =
      bif Nat.beq d 0 then
        (bif Nat.beq f 1 then acc else (⟨x, T, P, N + q2, 0⟩ :: acc))
      else bif Nat.ble (N + q2 + C2) (P + A * d) then acc
      else bif Nat.beq f 0 then
        (bif Nat.ble N P then acc
          else (⟨x, T, P + A * d, N + q2, bif Nat.ble 2 d then 2 else 1⟩ :: acc))
      else (⟨x, T, P + A * d, N + q2, bif Nat.ble 2 d then 2 else f⟩ :: acc) := by
  unfold kid
  simp only [cond_rec]
  rfl

/-- The pieces that begin with the block of entry `D`: the walk goes from block to block through
the door as long as the classes are new.  The first argument is the number of blocks that may
still be added; a piece that ends with the current block has deficit one less. -/
noncomputable def walk (k A q2 C2 P N f : Nat) (n : Nat) : Nat → Tr → List St → List St :=
  @Nat.rec (fun _ => Nat → Tr → List St → List St) (fun _ _ acc => acc)
    (fun n ih D T acc =>
      sel(Tr.mem T (canon k D), acc,
        ih (doorc k (exc k D)) (Tr.ins T (canon k D))
          (kid A q2 C2 P N f n (exc k D) (Tr.ins T (canon k D)) acc))) n

theorem walk_zero (k A q2 C2 P N f D : Nat) (T : Tr) (acc : List St) :
    walk k A q2 C2 P N f 0 D T acc = acc := rfl

theorem walk_succ (k A q2 C2 P N f n D : Nat) (T : Tr) (acc : List St) :
    walk k A q2 C2 P N f (n + 1) D T acc =
      bif Tr.mem T (canon k D) then acc
      else walk k A q2 C2 P N f n (doorc k (exc k D)) (Tr.ins T (canon k D))
          (kid A q2 C2 P N f n (exc k D) (Tr.ins T (canon k D)) acc) := by
  show sel(Tr.mem T (canon k D), acc,
    walk k A q2 C2 P N f n (doorc k (exc k D)) (Tr.ins T (canon k D))
      (kid A q2 C2 P N f n (exc k D) (Tr.ins T (canon k D)) acc)) = _
  rw [cond_rec]

/-- `w` applied to the six numbers `base + (a b c)`, …, `base + (c b a)` (three hexadecimal
digits each), the results chained. -/
def six (w : Nat → List St → List St) (base a b c : Nat) : List St :=
  w (Nat.add base (Nat.add (Nat.add (Nat.mul a 256) (Nat.mul b 16)) c))
   (w (Nat.add base (Nat.add (Nat.add (Nat.mul a 256) (Nat.mul c 16)) b))
    (w (Nat.add base (Nat.add (Nat.add (Nat.mul b 256) (Nat.mul a 16)) c))
     (w (Nat.add base (Nat.add (Nat.add (Nat.mul b 256) (Nat.mul c 16)) a))
      (w (Nat.add base (Nat.add (Nat.add (Nat.mul c 256) (Nat.mul a 16)) b))
       (w (Nat.add base (Nat.add (Nat.add (Nat.mul c 256) (Nat.mul b 16)) a)) [])))))

/-- The states after one more piece: the next piece begins with one of the six words that begin
with the digits 4 to `k` of the exit `st.y`. -/
noncomputable def children (k A q2 C2 : Nat) (st : St) : List St :=
  six (fun D acc => walk k A q2 C2 st.P st.N st.f (Nat.sub k 1) D st.T acc)
    (Nat.mul (Nat.mod st.y (pw (Nat.sub k 3))) 4096) (Nat.div st.y (pw (Nat.sub k 1)))
    (Nat.mod (Nat.div st.y (pw (Nat.sub k 2))) 16) (Nat.mod (Nat.div st.y (pw (Nat.sub k 3))) 16)

/-- `f c i` for some element `c` of the list, `i` being its index plus `j`. -/
noncomputable def anyIdx (f : St → Nat → Bool) (l : List St) : Nat → Bool :=
  @List.rec St (fun _ => Nat → Bool) (fun _ => false)
    (fun c _ ih j => sel(f c j, true, ih (Nat.succ j))) l

theorem anyIdx_nil (f : St → Nat → Bool) (j : Nat) : anyIdx f [] j = false := rfl

theorem anyIdx_cons (f : St → Nat → Bool) (c : St) (t : List St) (j : Nat) :
    anyIdx f (c :: t) j = (f c j || anyIdx f t (j + 1)) := by
  show sel(f c j, true, anyIdx f t (j + 1)) = _
  cases f c j <;> rfl

/-- The state is a window that violates the bound. -/
noncomputable def viol (C1 bn : Nat) (st : St) : Bool :=
  sel(Nat.beq st.f 2, sel(Nat.ble (Nat.add st.N C1) (Nat.add st.P bn), false, true), false)

theorem viol_eq (C1 bn : Nat) (st : St) :
    viol C1 bn st = (Nat.beq st.f 2 && !Nat.ble (st.N + C1) (st.P + bn)) := by
  show sel(Nat.beq st.f 2, sel(Nat.ble (st.N + C1) (st.P + bn), false, true), false) = _
  cases Nat.beq st.f 2 <;> cases Nat.ble (st.N + C1) (st.P + bn) <;> rfl

/-- The search below `st`: `fuel` pieces deep, then `leaf`.  The argument `key` records the path
(the index of each child taken, last first); leaves use it to cut the search into parts. -/
noncomputable def goK (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) (fuel : Nat) :
    St → List Nat → Bool :=
  @Nat.rec (fun _ => St → List Nat → Bool) (fun st key => leaf st key)
    (fun _ ih st key =>
      sel(viol C1 bn st, true,
        anyIdx (fun c i => ih c (i :: key)) (children k A q2 C2 st) 0)) fuel

theorem goK_zero (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) (st : St)
    (key : List Nat) : goK k A q2 C1 C2 bn leaf 0 st key = leaf st key := rfl

theorem goK_succ (k A q2 C1 C2 bn : Nat) (leaf : St → List Nat → Bool) (fuel : Nat) (st : St)
    (key : List Nat) : goK k A q2 C1 C2 bn leaf (fuel + 1) st key =
      bif viol C1 bn st then true
      else anyIdx (fun c i => goK k A q2 C1 C2 bn leaf fuel c (i :: key))
          (children k A q2 C2 st) 0 := by
  show sel(viol C1 bn st, true,
    anyIdx (fun c i => goK k A q2 C1 C2 bn leaf fuel c (i :: key)) (children k A q2 C2 st) 0) = _
  rw [cond_rec]

/-- The states after the first piece, which is partial and begins with the word `1 2 … k`. -/
noncomputable def rootChildren (k A q2 C2 : Nat) : List St :=
  walk k A q2 C2 0 0 1 (Nat.sub k 1) (idc k) Tr.leaf []

/-- The whole search.  `false`: no violating window with the fewest pieces exists (and the fuel
was enough to see that). -/
noncomputable def search (k A q2 C1 C2 bn fuel : Nat) : Bool :=
  anyIdx (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [i]) (rootChildren k A q2 C2) 0

/-- The state after one block with entry `1 2 … k`, for the run check. -/
noncomputable def runStart (k : Nat) : St :=
  ⟨exc k (idc k), Tr.ins Tr.leaf (canon k (idc k)), 0, 0, 0⟩

/-- The run check.  `false`: one block cannot be followed by `k - 2` full pieces.  (With
`A = q2 = 0` and `P = N = 0` the rules allow full pieces only, and with no fuel left the search
answers `true`.) -/
noncomputable def runSearch (k : Nat) : Bool :=
  goK k 0 0 0 0 0 (fun _ _ => true) (Nat.sub k 2) (runStart k) []

/-! ### Cutting a search into parts

Used by the generated files; the lemmas are in `SCut.lean`. -/

/-- Element `i` of a list of states, or `d`. -/
noncomputable def nthD (l : List St) : Nat → St → St :=
  @List.rec St (fun _ => Nat → St → St) (fun _ d => d)
    (fun c _ ih i d => @Nat.rec (fun _ => St) c (fun i _ => ih i d) i) l

theorem nthD_nil (i : Nat) (d : St) : nthD [] i d = d := rfl
theorem nthD_cons_zero (c : St) (t : List St) (d : St) : nthD (c :: t) 0 d = c := rfl
theorem nthD_cons_succ (c : St) (t : List St) (i : Nat) (d : St) :
    nthD (c :: t) (i + 1) d = nthD t i d := rfl

/-- The state reached from `st` by taking child `i` at each step of the path. -/
noncomputable def stepPath (k A q2 C2 : Nat) (st : St) (path : List Nat) : St :=
  @List.rec Nat (fun _ => St → St) (fun st => st)
    (fun i _ ih st => ih (nthD (children k A q2 C2 st) i st)) path st

theorem stepPath_nil (k A q2 C2 : Nat) (st : St) : stepPath k A q2 C2 st [] = st := rfl
theorem stepPath_cons (k A q2 C2 : Nat) (st : St) (i : Nat) (t : List Nat) :
    stepPath k A q2 C2 st (i :: t) = stepPath k A q2 C2 (nthD (children k A q2 C2 st) i st) t :=
  rfl

def beqKey : List Nat → List Nat → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && beqKey s t
  | _, _ => false

def memKey (key : List Nat) : List (List Nat) → Bool
  | [] => false
  | k :: t => beqKey key k || memKey key t

/-- The leaf that accepts (returns `false` for) exactly the paths of `cover`.  Paths are stored
last step first, as the search records them. -/
def leafCover (cover : List (List Nat)) : St → List Nat → Bool := fun _ key => !(memKey key cover)

/-- `Ref b st`: the search `b` pieces deep finds nothing below `st`. -/
def Ref (k A q2 C1 C2 bn b : Nat) (st : St) : Prop :=
  goK k A q2 C1 C2 bn (fun _ _ => true) b st [] = false

end S
end SuperpermLowerBounds

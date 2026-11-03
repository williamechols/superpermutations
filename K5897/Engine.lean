import LowerBounds.PSearch
import K5897.Tab

/-!
# A search on 7 symbols for the Lean kernel

The engine of Halfar's `K6/Engine.lean` (`proofs/lean/small/` of github.com/jhalfar/superpermutations),
written for 7 symbols with the tables of `K5897/Tab.lean`. One depth-first search over sequences of
rows on 7 symbols whose blocks lie in pairwise different rotation classes. A word is its index
`0 … 5039` (index 0 is `1 2 3 4 5 6 7`); the tables are natural numbers read with shifts, and the set
of used classes is a natural number read as a set of bits, so that every step of the search is a
few operations on numbers, which the kernel does with GMP.

A row is a walk from block to block (`nxtC`, the door) as long as the classes are new; it has 1 to
6 blocks. After a row the search continues with a row whose entry is one of the six words that
begin with the last four letters of the exit of the last block (`s3`; a seam of weight 3, kind `0`;
the one of these words that is a rotation of the exit has a used class and is refused at once), or
with a row that starts at any word (a jump, any other kind). What the search counts and when it
stops is given by `Rules`, as in `K6/Engine.lean`.

`part R fuel`: the answer `false` means: nothing found, and the fuel was enough to see that (fuel `0`
counts as found). `K5897/Sound.lean` proves what it means.
-/

namespace SuperpermLowerBounds
namespace K5897

/-- The code of word `i`. -/
def codeC (i : Nat) : Nat := (CODE >>> (28 * i)) % 268435456

/-- The class of word `i`, a number below 720. -/
def ciC (i : Nat) : Nat := (CI >>> (10 * i)) % 1024

/-- A word of class `c`. -/
def repC (c : Nat) : Nat := (REP >>> (13 * c)) % 8192

/-- The entry of the next block of a row. -/
def nxtC (i : Nat) : Nat := (NX >>> (13 * i)) % 8192

/-- The key of a code of four letters. -/
def key4 (p : Nat) : Nat :=
  (((p >>> 12) % 16 * 8 + (p >>> 8) % 16) * 8 + (p >>> 4) % 16) * 8 + p % 16

/-- The six words whose first four letters have the key `key`. -/
def bucket (key : Nat) : List Nat :=
  (List.range 6).map fun j => (BK >>> (13 * (6 * key + j))) % 8192

/-- The key of the last four letters of the exit of the block entered at word `i`. -/
def exitKey (i : Nat) : Nat := key4 (PS.excF (16 ^ (7 - 1) - 1) (codeC i) % 16 ^ (7 - 3))

/-- The successors of weight 3 of word `i`. -/
def s3C (i : Nat) : List Nat := bucket (exitKey i)

/-- The `j`-th (`j < 6`) successor of weight 3 of word `i`. -/
def s3 (i j : Nat) : Nat := (BK >>> (13 * (6 * exitKey i + j))) % 8192

/-- The set `{c}` as a number. -/
@[inline] def bit (c : Nat) : Nat := 1 <<< c

/-- What the search counts and when it stops. -/
structure Rules (Cn : Type) where
  init : Nat → Nat → Cn
  stN : Cn → Nat → Nat → Cn
  stJ : Cn → Nat → Nat → Cn
  keepN : Cn → Bool
  keepJ : Cn → Bool
  bad : Cn → Nat → Bool

/-- The rows that begin with the block of entry `D`, given the used classes `U`.  The last
argument is the number of blocks that may still be added; when it is `n + 1`, the row that ends
with the current block has `n` holes.  `g U' e n` is the search below the sequence extended by the
row with `n` holes that ends with the block of entry `e`, with the used classes `U'`. -/
def walk (g : Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | U, D, n + 1 =>
    cond (U.testBit (ciC D)) false
      (g (U ||| bit (ciC D)) D n || walk g (U ||| bit (ciC D)) (nxtC D) n)

/-- The rows after a seam: the six successors `s3 q j`, `j < 6`. -/
def succ3 (g : Nat → Nat → Nat → Bool) (U q : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => walk g U (s3 q j) 6 || succ3 g U q j

/-- The rows after a jump: every word `i < 5040`. -/
def jumps (g : Nat → Nat → Nat → Bool) (U : Nat) : Nat → Bool
  | 0 => false
  | i + 1 => walk g U i 6 || jumps g U i

/-- The search below a sequence with used classes `U`, last entry `q` and counters `c`. -/
def go {Cn : Type} (R : Rules Cn) : Nat → Nat → Nat → Cn → Bool
  | 0, _, _, _ => true
  | f + 1, U, q, c =>
    R.bad c U || (R.keepN c && succ3 (fun U' e n => go R f U' e (R.stN c n e)) U q 6) ||
      (R.keepJ c && jumps (fun U' e n => go R f U' e (R.stJ c n e)) U 5040)

/-- The search: the first row starts at the word `1 2 3 4 5 6 7`. -/
def part {Cn : Type} (R : Rules Cn) (fuel : Nat) : Bool :=
  walk (fun U e n => go R fuel U e (R.init n e)) 0 0 6

end K5897
end SuperpermLowerBounds

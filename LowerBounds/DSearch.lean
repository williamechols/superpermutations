/-!
# The prefix search on numbers

A depth-first search over the chains of the model (`SModelDef.lean`) whose first entry is the word
`1 2 … k`.  The rule is given by two Boolean functions of the number of pieces `r` and the total
deficit `δ` of a chain:

* `bad r δ`: the chain is what the search looks for;
* `keep r δ`: the chains that begin with this chain are searched.

The search visits every chain all of whose non-empty proper prefixes satisfy `keep`, and answers
`true` if one of the visited chains is `bad` (or if the fuel runs out).  `DSound.lean` proves that
if the answer is `false`, then no chain all of whose non-empty proper prefixes satisfy `keep` is
`bad`.

Unlike `SSearch.lean` this file is written for compiled evaluation, not for the kernel:

* a word is its code as in `SSearch.lean` (the word read as `k` hexadecimal digits);
* the set of used rotation classes is a table of bytes (`ByteArray`), one byte per class, indexed
  by `cidxF`; a mark is set when a block is entered and removed when the search returns, so the
  table is updated in place;
* a table of size zero stands for "found".

To cut one search into parts that can be evaluated in parallel, the search takes a gate
(`gateF ds nt t`): the chains with exactly `ds` pieces are continued only if the code of their last
exit, without its last digit, is `t` modulo `nt`.  The parts `t = 0, …, nt - 1` together cover the whole search.

This file imports nothing; it is compiled to C and loaded by the files that evaluate the search.
-/

namespace SuperpermLowerBounds
namespace S

/-! ### Arithmetic on codes

`s1 = 4 (k - 1)` is the number of bits below the first digit and `m1 = 16 ^ (k - 1) - 1` the mask
of these bits. -/

/-- The code of the word `1 2 … n`. -/
def idcF : Nat → Nat
  | 0 => 0
  | n + 1 => idcF n * 16 + (n + 1)

/-- The exit of a block from its entry: the last digit moves to the front. -/
@[inline] def excF (m1 c : Nat) : Nat := c % 16 * (m1 + 1) + c / 16

/-- The door: the first two digits move to the end, in reverse order. -/
@[inline] def doorF (s1 m1 x : Nat) : Nat :=
  (x &&& (m1 >>> 4)) * 256 + (x >>> (s1 - 4)) % 16 * 16 + (x >>> s1)

/-- The code rotated to the left, one digit at a time, until its first digit is `k` (at most `n`
times). -/
def canonF (k s1 m1 : Nat) : Nat → Nat → Nat
  | 0, c => c
  | n + 1, c => if c >>> s1 == k then c else canonF k s1 m1 n ((c &&& m1) * 16 + (c >>> s1))

/-- The last `n` hexadecimal digits of `c`, each lowered by one, read in base `B`. -/
def packF (B : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, c => packF B n (c / 16) * B + (c % 16 - 1)

/-- The index of the rotation class of the word with code `c`. -/
@[inline] def cidxF (k s1 m1 c : Nat) : Nat := packF k (k - 1) (canonF k s1 m1 k c)

/-! ### The search -/

/-- The pieces that begin with the block of entry `D`: the walk goes from block to block through
the door as long as the classes are new.  The first numeric argument is the number of blocks that
may still be added; a piece that ends with the current block has deficit one less.  `visit d x M`
is the search below the chain extended by that piece (deficit `d`, last exit `x`). -/
@[specialize] def pwalk (k s1 m1 : Nat) (visit : Nat → Nat → ByteArray → ByteArray) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, M => M
  | n + 1, D, M =>
    if M.get! (cidxF k s1 m1 D) != 0 then M
    else
      let M1 := visit n (excF m1 D) (M.set! (cidxF k s1 m1 D) 1)
      if M1.size == 0 then M1
      else (pwalk k s1 m1 visit n (doorF s1 m1 (excF m1 D)) M1).set! (cidxF k s1 m1 D) 0

/-- `w` applied to the numbers of the list in turn, until found. -/
@[specialize] def pall (w : Nat → ByteArray → ByteArray) : List Nat → ByteArray → ByteArray
  | [], M => M
  | D :: Ds, M =>
    let M' := w D M
    if M'.size == 0 then M' else pall w Ds M'

/-- The six numbers `base + (a b c)`, …, `base + (c b a)` (three hexadecimal digits each). -/
@[inline] def sixL (base a b c : Nat) : List Nat :=
  [base + (a * 256 + b * 16 + c), base + (a * 256 + c * 16 + b), base + (b * 256 + a * 16 + c),
    base + (b * 256 + c * 16 + a), base + (c * 256 + a * 16 + b), base + (c * 256 + b * 16 + a)]

/-- The gate of part `t` of `nt`: a chain with exactly `ds` pieces is continued only if the code
of its last exit without its last digit is `t` modulo `nt`.  (The code itself is useless here: it
is the same modulo 15 for all words.) -/
@[inline] def gateF (ds nt t : Nat) (r y : Nat) : Bool := r != ds || y / 16 % nt == t

/-- The search below a chain with `r` pieces, total deficit `δ` and last exit `y`. -/
@[specialize] def pgo (k s1 m1 ds nt t : Nat) (keep bad : Nat → Nat → Bool) :
    Nat → Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, _, _ => ByteArray.empty
  | fuel + 1, r, δ, y, M =>
    if bad r δ then ByteArray.empty
    else if keep r δ && gateF ds nt t r y then
      pall (fun D M' => pwalk k s1 m1
          (fun d x M'' => pgo k s1 m1 ds nt t keep bad fuel (r + 1) (δ + d) x M'') (k - 1) D M')
        (sixL (y % ((m1 + 1) / 256) * 4096) (y / (m1 + 1)) (y / ((m1 + 1) / 16) % 16)
          (y / ((m1 + 1) / 256) % 16)) M
    else M

/-- The table with no mark. -/
def marks0 (sz : Nat) : ByteArray := ByteArray.mk (Array.replicate sz 0)

/-- Part `t` of `nt` of the search.  `false`: none of the visited chains is `bad` (and the fuel
was enough to see that). -/
@[specialize] def psearchPart (k sz : Nat) (keep bad : Nat → Nat → Bool) (fuel ds nt t : Nat) :
    Bool :=
  (pwalk k (4 * (k - 1)) (16 ^ (k - 1) - 1)
    (fun d x M => pgo k (4 * (k - 1)) (16 ^ (k - 1) - 1) ds nt t keep bad fuel 1 d x M) (k - 1)
    (idcF k) (marks0 sz)).size == 0

/-- All `nt` parts, evaluated as tasks. -/
@[specialize] def psearchPar (k sz : Nat) (keep bad : Nat → Nat → Bool) (fuel ds nt : Nat) :
    Bool :=
  ((List.range nt).map fun t => Task.spawn fun _ => psearchPart k sz keep bad fuel ds nt t).any
    Task.get

/-! ### The rules -/

/-- Line `a r ≤ b δ + c`: the prefixes searched have `0 < a r - b δ ≤ c`. -/
@[inline] def lineKeep (a b c : Nat) (r δ : Nat) : Bool := b * δ < a * r && a * r ≤ b * δ + c

/-- Line `a r ≤ b δ + c`: a chain above the line. -/
@[inline] def lineBad (a b c : Nat) (r δ : Nat) : Bool := b * δ + c < a * r

/-- Zone of two lines `a₁ r ≤ b₁ δ + c₁` and `a₂ r ≤ b₂ δ + c₂` with widths `u₁`, `u₂`: the
prefixes searched have `a₁ r - b₁ δ ≥ -u₁` and `a₂ r - b₂ δ ≥ -u₂`. -/
@[inline] def zoneKeep (a₁ b₁ u₁ a₂ b₂ u₂ : Nat) (r δ : Nat) : Bool :=
  b₁ * δ ≤ a₁ * r + u₁ && b₂ * δ ≤ a₂ * r + u₂

/-- A chain in the zone (`a₁ r - b₁ δ ≥ c₁ - u₁` and `a₂ r - b₂ δ ≥ c₂ - u₂`) that is not on the
first line. -/
@[inline] def zoneBad (a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ : Nat) (r δ : Nat) : Bool :=
  b₁ * δ + c₁ ≤ a₁ * r + u₁ && b₂ * δ + c₂ ≤ a₂ * r + u₂ && a₁ * r != b₁ * δ + c₁

/-- The search for a chain above the line `a r ≤ b δ + c`, in `nt` parts. -/
def lineSearch (k sz a b c fuel ds nt : Nat) : Bool :=
  psearchPar k sz (lineKeep a b c) (lineBad a b c) fuel ds nt

/-- The search for a chain in the zone of two lines that is not on the first line, in `nt`
parts. -/
def zoneSearch (k sz a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂ fuel ds nt : Nat) : Bool :=
  psearchPar k sz (zoneKeep a₁ b₁ u₁ a₂ b₂ u₂) (zoneBad a₁ b₁ c₁ u₁ a₂ b₂ c₂ u₂) fuel ds nt

end S
end SuperpermLowerBounds

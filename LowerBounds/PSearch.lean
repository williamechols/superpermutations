/-!
# The search for the finite statements of 5,899 (the written proof, section 8)

One depth-first search over sequences of rows on `k` symbols with pairwise different classes.  The
first row starts at the word `1 2 … k`.  A row is followed by a row that starts

* at a word that the exit of its last block overlaps in `k - 3` symbols (a link of weight 3), or
* at a word that the exit overlaps in `k - 4` symbols (a link of weight 4; "special"), or
* at any word (a jump; "special").

The search keeps three counters: `t`, the number of special links so far; `r`, the number of rows;
`d`, the number of holes (`k - 1` minus the number of blocks, summed over the rows).  With
`rs = true` the counters `r` and `d` start again at every special link.  The rule is five Boolean
functions of `(t, r, d)`:

* `bad`: found;
* `badR`: found if moreover the first word is a weight-3 successor of the last block (a ring);
* `keepN`, `keepS`, `keepJ`: continue with links of weight 3, of weight 4, with jumps.

`PSound.lean` proves: if the answer is `false`, there is no sequence along which the rule holds
(every proper prefix satisfies the `keep` of the link that follows it, and the whole is found).

The engine does not know what a word is.  It is given

* `ci`: the class index of a word (the index of its mark in a table of bytes);
* `nxt`: the entry of the next block of a row;
* `s3`, `s4`: the lists of weight-3 and of weight-4 successors of a last entry;
* `jl`: the list of all words; `st`: the first word.

Two sets of these are defined here.  **A**: a word is its code (read as `k` hexadecimal digits) and
everything is arithmetic; this is what the kernel can evaluate on 5 symbols.  **B**: a word is its
index in the list of all permutation codes and everything is read from tables that are computed
once from the arithmetic of A; this is what is compiled for 7 symbols.

To cut one search into parts, a sequence whose remaining fuel is `fg` is continued only if its
last entry is `tp` modulo `nt` (`tp = 0, …, nt - 1` cover the search).

This file imports nothing; it is compiled to C and loaded by the files that evaluate the search.
-/

namespace SuperpermLowerBounds
namespace PS

/-! ### The engine -/

/-- The rows that begin with the block of entry `D`: the walk goes from block to block as long as
the classes are new.  The first numeric argument is the number of blocks that may still be added;
when it is `n + 1`, the row that ends with the current block has `n` holes.  `visit n e M` is the
search below the sequence extended by the row with `n` holes that ends with the block of entry
`e`. -/
@[specialize] def walk (ci nxt : Nat → Nat) (visit : Nat → Nat → ByteArray → ByteArray) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, M => M
  | n + 1, D, M =>
    if M.get! (ci D) != 0 then M
    else
      let M1 := visit n D (M.set! (ci D) 1)
      if M1.size == 0 then M1
      else (walk ci nxt visit n (nxt D) M1).set! (ci D) 0

/-- `w` applied to the numbers of the list in turn, until found. -/
@[specialize] def all (w : Nat → ByteArray → ByteArray) : List Nat → ByteArray → ByteArray
  | [], M => M
  | D :: Ds, M =>
    let M' := w D M
    if M'.size == 0 then M' else all w Ds M'

/-- The search below a sequence with counters `t`, `r`, `d` and last entry `q`.  A table of size
zero stands for "found". -/
@[specialize] def go (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat) (st kb : Nat)
    (rs : Bool) (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (fg nt tp : Nat) :
    Nat → Nat → Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, _, _, _ => ByteArray.empty
  | fuel + 1, t, r, d, q, M =>
    if bad t r d || (badR t r d && (s3 q).contains st) then ByteArray.empty
    else if fuel != fg || q % nt == tp then
      let M1 :=
        if keepN t r d then
          all (fun D M' => walk ci nxt
            (fun n e M'' => go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel
              t (r + 1) (d + n) e M'') kb D M') (s3 q) M
        else M
      if M1.size == 0 then M1
      else
        let M2 :=
          if keepS t r d then
            all (fun D M' => walk ci nxt
              (fun n e M'' => go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel
                (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb D M')
              (s4 q) M1
          else M1
        if M2.size == 0 then M2
        else if keepJ t r d then
          all (fun D M' => walk ci nxt
            (fun n e M'' => go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel
              (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) e M'') kb D M')
            jl M2
        else M2
    else M

/-- The table with no mark. -/
def marks0 (sz : Nat) : ByteArray := ByteArray.mk (Array.replicate sz 0)

/-- Part `tp` of `nt` of the search.  `false`: none of the visited sequences is found (and the
fuel was enough to see that). -/
@[specialize] def searchPart (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (st kb : Nat) (rs : Bool) (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool)
    (sz fuel fg nt tp : Nat) : Bool :=
  (walk ci nxt
    (fun n e M => go ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ fg nt tp fuel 0 1 n e M)
    kb st (marks0 sz)).size == 0

/-- The parts `pa ≤ tp < pb` of `nt`, evaluated as tasks. -/
@[specialize] def searchPar (ci nxt : Nat → Nat) (s3 s4 : Nat → List Nat) (jl : List Nat)
    (st kb : Nat) (rs : Bool) (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool)
    (sz fuel fg nt pa pb : Nat) : Bool :=
  ((List.range (pb - pa)).map fun i => Task.spawn fun _ =>
    searchPart ci nxt s3 s4 jl st kb rs bad badR keepN keepS keepJ sz fuel fg nt (pa + i)).any
      Task.get

/-! ### Arithmetic on codes (set A)

`s1 = 4 (k - 1)` is the number of bits below the first digit and `m1 = 16 ^ (k - 1) - 1` the mask
of these bits.  The first six definitions are those of `DSearch.lean`. -/

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

/-- The entry of the next block of a row. -/
@[inline] def nxtF (s1 m1 c : Nat) : Nat := doorF s1 m1 (excF m1 c)

/-- Does the digit `a` occur among the last `n` hexadecimal digits of `c`? -/
def occF : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, c, a => c % 16 == a || occF n (c / 16) a

/-- The codes of the words of length `n` with different symbols from `1 … k`. -/
def permCodes (k : Nat) : Nat → List Nat
  | 0 => [0]
  | n + 1 => (permCodes k n).flatMap fun c =>
      ((List.range k).filter fun a => !occF n c (a + 1)).map fun a => c * 16 + (a + 1)

/-- The exit of the block entered at `a`, without its first `d` symbols, is the beginning of `b`
(`pd = 16 ^ (k - d)`, `qd = 16 ^ d`). -/
@[inline] def ovlF (m1 pd qd a b : Nat) : Bool := excF m1 a % pd == b / qd

/-- The words of `jl` that the exit of the block entered at `a` overlaps in `k - d` symbols. -/
def sdA (k d : Nat) (jl : List Nat) (a : Nat) : List Nat :=
  jl.filter fun b => ovlF (16 ^ (k - 1) - 1) (16 ^ (k - d)) (16 ^ d) a b

/-- The search with words as codes (set A). -/
@[specialize] def searchA (k : Nat) (rs : Bool)
    (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (fuel ds nt pa pb : Nat) : Bool :=
  searchPar (cidxF k (4 * (k - 1)) (16 ^ (k - 1) - 1)) (nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1))
    (sdA k 3 (permCodes k k)) (sdA k 4 (permCodes k k)) (permCodes k k) (idcF k) (k - 1) rs
    bad badR keepN keepS keepJ (k ^ (k - 1)) fuel (fuel - ds) nt pa pb

/-! ### Tables (set B) -/

/-- Class indices: the index of the rotation that begins with `k`. -/
def ciTab (k : Nat) (jl : List Nat) : Array Nat :=
  (jl.map fun c => jl.idxOf (canonF k (4 * (k - 1)) (16 ^ (k - 1) - 1) k c)).toArray

/-- Next entries. -/
def nxtTab (k : Nat) (jl : List Nat) : Array Nat :=
  (jl.map fun c => jl.idxOf (nxtF (4 * (k - 1)) (16 ^ (k - 1) - 1) c)).toArray

/-- Successors of weight `d`. -/
def sdTab (k d : Nat) (jl : List Nat) : Array (List Nat) :=
  let m1 := 16 ^ (k - 1) - 1
  let pd := 16 ^ (k - d)
  let qd := 16 ^ d
  let ja := jl.toArray
  (jl.map fun a => (List.range jl.length).filter fun j => ovlF m1 pd qd a ja[j]!).toArray

/-- The search with words as indices into the list of permutation codes (set B). -/
@[specialize] def searchB (k : Nat) (rs : Bool)
    (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (fuel ds nt pa pb : Nat) : Bool :=
  let jl := permCodes k k
  let ciT := ciTab k jl
  let nxtT := nxtTab k jl
  let s3T := sdTab k 3 jl
  let s4T := sdTab k 4 jl
  searchPar (fun i => ciT[i]!) (fun i => nxtT[i]!) (fun i => s3T[i]!) (fun i => s4T[i]!)
    (List.range jl.length) (jl.idxOf (idcF k)) (k - 1) rs bad badR keepN keepS keepJ jl.length
    fuel (fuel - ds) nt pa pb

/-! ### Tabulated rules -/

/-- A Boolean function of three numbers, tabulated for `t < A`, `r < B`, `d < C`. -/
def tab3 (A B C : Nat) (f : Nat → Nat → Nat → Bool) : Array Bool :=
  Array.ofFn (n := A * B * C) fun i => f (i.val / C / B) (i.val / C % B) (i.val % C)

/-- The function read from its table; outside the table it is evaluated. -/
@[inline] def look3 (A B C : Nat) (T : Array Bool) (f : Nat → Nat → Nat → Bool) (t r d : Nat) :
    Bool :=
  if t < A && r < B && d < C then T[(t * B + r) * C + d]! else f t r d

/-! ### The rules -/

/-- The cap of the sequences with `j` links of weight 4 at `x` holes. -/
def capF (caps : List (List Nat)) (j x : Nat) : Nat := (caps.getD j []).getD x 0

/-- F_s, levels `lo … hi`: a sequence with `s` links and `lo ≤ d ≤ hi` holes above its cap. -/
def seqBad (caps : List (List Nat)) (s lo hi : Nat) (t r d : Nat) : Bool :=
  t == s && lo ≤ d && d ≤ hi && capF caps s d < r

/-- F_s, continue with a link of weight 3: there is a total `x` of holes, `lo ≤ x ≤ hi`, such
that with a rest of `s - t` links and `x - d` holes at its cap the sequence would be above the cap
at `x`. -/
def seqKeepN (caps : List (List Nat)) (s lo hi : Nat) (t r d : Nat) : Bool :=
  t ≤ s && (List.range (hi + 1)).any fun x =>
    lo ≤ x && d ≤ x && capF caps s x < r + capF caps (s - t) (x - d)

/-- F_s: the same for a rest with `s - t - 1` links that follows a link of weight 4. -/
def seqKeepS (caps : List (List Nat)) (s lo hi : Nat) (t r d : Nat) : Bool :=
  t < s && (List.range (hi + 1)).any fun x =>
    lo ≤ x && d ≤ x && capF caps s x < r + capF caps (s - t - 1) (x - d)

/-- The rule that never holds. -/
def noRule (_ _ _ : Nat) : Bool := false

/-- FR: at least two rows, at most `G` holes, above the ring cap. -/
def ringBad (PR : List Nat) (G : Nat) (_ r d : Nat) : Bool := 2 ≤ r && d ≤ G && PR.getD d 0 < r

/-- FR: there is a target (`T` rows, `H` holes) above the ring cap and within the chain cap for
which the prefix obeys the cycle lemma and the rest obeys the chain cap. -/
def ringKeep (M PR : List Nat) (G : Nat) (_ r d : Nat) : Bool :=
  (List.range (G + 1)).any fun H => d ≤ H &&
    (let mh := M.getD H 0
     let pr := PR.getD H 0
     let mr := M.getD (H - d) 0
     (List.range (mh + 1)).any fun T => pr < T && r < T && d * T ≤ r * H && T ≤ r + mr)

/-- FF: the last chain has its rows. -/
def profBad (ts : List (Nat × Nat)) (t r d : Nat) : Bool :=
  t + 1 == ts.length && r == (ts.getD t (0, 0)).1 && d ≤ (ts.getD t (0, 0)).2

/-- FF: chain `t` can still reach its number of rows within its holes. -/
def profKeepN (M : List Nat) (ts : List (Nat × Nat)) (t r d : Nat) : Bool :=
  r < (ts.getD t (0, 0)).1 && d ≤ (ts.getD t (0, 0)).2 &&
    (List.range ((ts.getD t (0, 0)).2 - d + 1)).any fun e => (ts.getD t (0, 0)).1 ≤ r + M.getD e 0

/-- FF: chain `t` has its rows and is not the last. -/
def profKeepJ (ts : List (Nat × Nat)) (t r d : Nat) : Bool :=
  t + 1 < ts.length && r == (ts.getD t (0, 0)).1 && d ≤ (ts.getD t (0, 0)).2

/-! ### The searches of the finite statements -/

/-- F_s on levels `lo … hi`, with words as codes (for the kernel). -/
def seqSearchA (k : Nat) (caps : List (List Nat)) (s lo hi fuel ds nt pa pb : Nat) : Bool :=
  searchA k false (seqBad caps s lo hi) noRule (seqKeepN caps s lo hi) (seqKeepS caps s lo hi)
    noRule fuel ds nt pa pb

/-- F_s on levels `lo … hi`, compiled. -/
def seqSearch (k : Nat) (caps : List (List Nat)) (s lo hi fuel ds nt pa pb : Nat) : Bool :=
  let B := capF caps s hi + 2
  let tb := tab3 (s + 1) B (hi + 1) (seqBad caps s lo hi)
  let tn := tab3 (s + 1) B (hi + 1) (seqKeepN caps s lo hi)
  let tS := tab3 (s + 1) B (hi + 1) (seqKeepS caps s lo hi)
  searchB k false (look3 (s + 1) B (hi + 1) tb (seqBad caps s lo hi)) noRule
    (look3 (s + 1) B (hi + 1) tn (seqKeepN caps s lo hi))
    (look3 (s + 1) B (hi + 1) tS (seqKeepS caps s lo hi)) noRule fuel ds nt pa pb

/-- FR, with words as codes (for the kernel). -/
def ringSearchA (k : Nat) (M PR : List Nat) (G fuel ds nt pa pb : Nat) : Bool :=
  searchA k false noRule (ringBad PR G) (ringKeep M PR G) noRule noRule fuel ds nt pa pb

/-- FR, compiled. -/
def ringSearch (k : Nat) (M PR : List Nat) (G fuel ds nt pa pb : Nat) : Bool :=
  let B := M.getD G 0 + 2
  let tb := tab3 1 B (G + 1) (ringBad PR G)
  let tn := tab3 1 B (G + 1) (ringKeep M PR G)
  searchB k false noRule (look3 1 B (G + 1) tb (ringBad PR G))
    (look3 1 B (G + 1) tn (ringKeep M PR G)) noRule noRule fuel ds nt pa pb

/-- FF, with words as codes (for the kernel). -/
def profSearchA (k : Nat) (M : List Nat) (ts : List (Nat × Nat)) (fuel ds nt pa pb : Nat) :
    Bool :=
  searchA k true (profBad ts) noRule (profKeepN M ts) noRule (profKeepJ ts) fuel ds nt pa pb

/-- FF, compiled. -/
def profSearch (k : Nat) (M : List Nat) (ts : List (Nat × Nat)) (fuel ds nt pa pb : Nat) :
    Bool :=
  let B := (ts.map Prod.fst).foldl max 0 + 2
  let C := (ts.map Prod.snd).foldl max 0 + 2
  let tb := tab3 ts.length B C (profBad ts)
  let tn := tab3 ts.length B C (profKeepN M ts)
  let tj := tab3 ts.length B C (profKeepJ ts)
  searchB k true (look3 ts.length B C tb (profBad ts)) noRule
    (look3 ts.length B C tn (profKeepN M ts)) noRule
    (look3 ts.length B C tj (profKeepJ ts)) fuel ds nt pa pb

end PS
end SuperpermLowerBounds

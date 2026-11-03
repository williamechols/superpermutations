import K5897.Engine
import K5897.CapTab
import K5897.Caps

/-!
# The rules of the chain search (F0 on 7 symbols)

As Halfar's `K6/CapRules.lean`: one trail, counters `(rows, holes)`; continue with a seam when
`PS.seqKeepN caps 0 lo hi 0 r d`, found when `PS.seqBad caps 0 lo hi 0 r d`, never a jump. The two
rules are read from the bit tables `TB`, `TK` for `r < 160`, `d < 80` and computed outside;
`TabAgrees` (in `Cap.lean`) says that a table agrees with its rule.
-/

namespace SuperpermLowerBounds
namespace K5897

/-- A Boolean function of two numbers, read from the bits of `T` for `r < 160`, `d < 80`. -/
@[inline] def lk (T : Nat) (f : Nat → Nat → Bool) (r d : Nat) : Bool :=
  cond (r.blt 160 && d.blt 80) (T.testBit (80 * r + d)) (f r d)

/-- The rules of the chain search with caps `caps` on the levels `lo … hi`. -/
def capRules (caps : List (List Nat)) (lo hi TB TK : Nat) : Rules (Nat × Nat) where
  init n _ := (1, n)
  stN c n _ := (c.1 + 1, c.2 + n)
  stJ c _ _ := c
  keepN c := lk TK (PS.seqKeepN caps 0 lo hi 0) c.1 c.2
  keepJ _ := false
  bad c _ := lk TB (PS.seqBad caps 0 lo hi 0) c.1 c.2

end K5897
end SuperpermLowerBounds

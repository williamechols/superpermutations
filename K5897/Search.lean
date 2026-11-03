import K5897.Cap
import K5897.CapEval
import K5897.Arith

/-!
# The chain caps `T`, from the search that the kernel evaluates

`capEval` (`CapEval.lean`) is the answer of the search, `tabB` and `tabK` say that the bit tables
of its rules are the rules `PS.seqBad`, `PS.seqKeepN` of Halfar's `PSearch.lean`, and
`chainCapK_of_capParts` (`Cap.lean`) turns the three into the chain caps.
-/

namespace SuperpermLowerBounds
namespace K5897

open PS

theorem tabB : TabAgrees TB (seqBad [Tcap] 0 0 72 0) = true := by decide +kernel

theorem tabK : TabAgrees TK (seqKeepN [Tcap] 0 0 72 0) = true := by decide +kernel

/-- **The chain caps.** A chain on 7 symbols with `x ≤ 72` holes has at most `T x` rows. -/
theorem chainCap_T : ChainCap Tf 72 :=
  chainCapK_of_capParts tabB tabK capEval

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.chainCap_T

-- S(7) >= 5897 for superpermutations on seven symbols, checked by the Lean kernel alone.
import AlmanacDefs
import K5897.Main

namespace AlmanacSubmission

/-- Every superpermutation on 7 symbols has at least 5897 letters. The proof uses no native_decide. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5897 := SuperpermLowerBounds.K5897.lowerBoundAt_7_5897

end AlmanacSubmission

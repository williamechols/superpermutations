-- S(9) >= 408470 for superpermutations on nine symbols, with one finite search evaluated by native_decide.
import AlmanacDefs
import W9.Main

namespace AlmanacSubmission

/-- Every superpermutation on 9 symbols has at least 408470 letters. One search is evaluated by native_decide. -/
theorem lower_nine : Almanac.LowerBoundAt 9 408470 := SuperpermLowerBounds.W9.lowerBoundAt_9_408470

end AlmanacSubmission

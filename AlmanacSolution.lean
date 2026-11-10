-- S(11) >= 43917904 for superpermutations on eleven symbols, checked by the Lean kernel alone.
import AlmanacDefs
import K11.Main

namespace AlmanacSubmission

/-- Every superpermutation on 11 symbols has at least 43917904 letters. The proof uses no native_decide. -/
theorem lower_eleven : Almanac.LowerBoundAt 11 43917904 := SuperpermLowerBounds.K11.lowerBoundAt_11_43917904

end AlmanacSubmission

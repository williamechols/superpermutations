import LowerBounds.SSearch

/-!
# The run check, evaluated by the kernel

`S.runSearch k = false` for `k = 5, …, 15`: a chain of the model cannot consist of one block
followed by `k - 2` full pieces.  `SSound.lean` derives from this that a run of full pieces that
follows a piece has at most `k - 3` pieces.  Each search has `3 k - 8` states.
-/

namespace SuperpermLowerBounds
namespace S

set_option maxRecDepth 100000

theorem runSearch_5 : runSearch 5 = false := by decide +kernel
theorem runSearch_6 : runSearch 6 = false := by decide +kernel
theorem runSearch_7 : runSearch 7 = false := by decide +kernel
theorem runSearch_8 : runSearch 8 = false := by decide +kernel
theorem runSearch_9 : runSearch 9 = false := by decide +kernel
theorem runSearch_10 : runSearch 10 = false := by decide +kernel
theorem runSearch_11 : runSearch 11 = false := by decide +kernel
theorem runSearch_12 : runSearch 12 = false := by decide +kernel
theorem runSearch_13 : runSearch 13 = false := by decide +kernel
theorem runSearch_14 : runSearch 14 = false := by decide +kernel
theorem runSearch_15 : runSearch 15 = false := by decide +kernel

end S
end SuperpermLowerBounds

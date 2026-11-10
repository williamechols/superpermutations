import AlmanacDefs
import W9.Bound
import W9.Native

/-!
# S(9) ≥ 408,470

Every word over 9 symbols that contains all 362,880 permutations as contiguous parts has at least
408,470 letters.

**Trusted here.**  Every theorem of this file depends on the axiom recorded by `native_decide` in
`W9/Native.lean`:

* `S.searchC_9_111_5978_1000._native.native_decide.ax_1_1`:
  `S.searchC 9 5889 2000 10000 12000 5978 1200 = false`.

This equation was not checked by the kernel.  Everything else is: this file only applies
`covers_boundC_9_of_searchC` (`W9/Bound.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`)
to it.
-/

namespace SuperpermLowerBounds
namespace W9

/-- Every covering word on 9 symbols has at least 408,470 letters. -/
theorem covers_408470 : ∀ w : List (Fin 9), SuperpermutationBounds.Covers w → 408470 ≤ w.length :=
  covers_boundC_9_of_searchC S.searchC_9_111_5978_1000

/-- The same for `Hunter.Ssuper 9`. -/
theorem ssuper_408470 : 408470 ≤ Hunter.Ssuper 9 :=
  superperm_boundC_9_of_searchC S.searchC_9_111_5978_1000

/-- The Almanac's statement. -/
theorem lowerBoundAt_9_408470 : Almanac.LowerBoundAt 9 408470 := by
  intro w hw
  apply covers_408470 w
  intro p hl hn
  obtain ⟨s, t, h⟩ := hw p hn hl
  exact ⟨s, t, h.symm⟩

end W9
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.W9.lowerBoundAt_9_408470

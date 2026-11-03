import AlmanacDefs
import K5897.Final
import K5897.Search

/-!
# S(7) ≥ 5,897, checked by the Lean kernel alone

Every word over 7 symbols that contains all 5,040 permutations as contiguous parts has at least
5,897 letters. The proof has no `native_decide`: its one finite search (`K5897.capEval`) and
its arithmetic are evaluated by `decide +kernel`.
-/

namespace SuperpermLowerBounds
namespace K5897

/-- Every covering word on 7 symbols has at least 5,897 letters. -/
theorem covers_5897 : ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5897 ≤ w.length :=
  covers_5897_of_cap chainCap_T

/-- The Almanac's statement. -/
theorem lowerBoundAt_7_5897 : Almanac.LowerBoundAt 7 5897 := by
  intro w hw
  apply covers_5897 w
  intro p hl hn
  obtain ⟨s, t, h⟩ := hw p hn hl
  exact ⟨s, t, h.symm⟩

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.lowerBoundAt_7_5897

import LowerBounds.TheoremC
import Superperm.Bridge

/-!
# Theorem C for covering words over `Fin k`

The same conditional bounds in the vocabulary of `Challenge.lean` of the upper-bound project:
a word `w : List (Fin k)` with `SuperpermutationBounds.Covers w` contains every duplicate-free
list of length `k` as a factor.  `SuperpermBridge.hunter_le_ssuper_iff` translates
`L ≤ Hunter.Ssuper k` into `∀ w, Covers w → L ≤ w.length`.

Every statement has the window hypothesis `HStatement k cn bn q` as an explicit hypothesis.
-/

namespace SuperpermLowerBounds

open SuperpermutationBounds

/-- Theorem C for covering words, conditional on the window hypothesis. -/
theorem covers_length_ge_boundC {k cn bn q : ℕ} (hk : 5 ≤ k) (hcond : ConditionsC k cn bn q)
    (hH : HStatement k cn bn q) :
    ∀ w : List (Fin k), Covers w → boundC k cn bn q ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (superperm_boundC hk hcond hH)

/-- `H(8; 9/20, 73/5)`: every covering word on 8 symbols has at least 46133 letters. -/
theorem covers_boundC_8 :
    HStatement 8 9 292 20 → ∀ w : List (Fin 8), Covers w → 46133 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_8 hH)

/-- `H(9; 1/10, 19/5)`: every covering word on 9 symbols has at least 408469 letters. -/
theorem covers_boundC_9 :
    HStatement 9 1 38 10 → ∀ w : List (Fin 9), Covers w → 408469 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_9 hH)

/-- `H(10; 47/200, 88/25)`: every covering word on 10 symbols has at least 4033377 letters. -/
theorem covers_boundC_10 :
    HStatement 10 47 704 200 → ∀ w : List (Fin 10), Covers w → 4033377 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_10 hH)

/-- `H(11; 7/80, 37/10)`: every covering word on 11 symbols has at least 43917898 letters. -/
theorem covers_boundC_11 :
    HStatement 11 7 296 80 → ∀ w : List (Fin 11), Covers w → 43917898 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_11 hH)

/-- `H(12; 19/500, 266/125)`: every covering word on 12 symbols has at least 522622354
letters. -/
theorem covers_boundC_12 :
    HStatement 12 19 1064 500 → ∀ w : List (Fin 12), Covers w → 522622354 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_12 hH)

/-- `H(13; 61/400, 149/50)`: every covering word on 13 symbols has at least 6746626424
letters. -/
theorem covers_boundC_13 :
    HStatement 13 61 1192 400 → ∀ w : List (Fin 13), Covers w → 6746626424 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_13 hH)

/-- `H(14; 19/400, 171/50)`: every covering word on 14 symbols has at least 93891137847
letters. -/
theorem covers_boundC_14 :
    HStatement 14 19 1368 400 → ∀ w : List (Fin 14), Covers w → 93891137847 ≤ w.length :=
  fun hH => (SuperpermBridge.hunter_le_ssuper_iff (by norm_num)).mp (superperm_boundC_14 hH)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_length_ge_boundC
#print axioms SuperpermLowerBounds.covers_boundC_8
#print axioms SuperpermLowerBounds.covers_boundC_9
#print axioms SuperpermLowerBounds.covers_boundC_10
#print axioms SuperpermLowerBounds.covers_boundC_11
#print axioms SuperpermLowerBounds.covers_boundC_12
#print axioms SuperpermLowerBounds.covers_boundC_13
#print axioms SuperpermLowerBounds.covers_boundC_14

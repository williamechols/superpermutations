import LowerBounds.SModel
import LowerBounds.SRun
import LowerBounds.SBridgeTheoremC
import W9.SearchCEq

/-!
# 408,470 for 9 symbols from one window certificate

It applies Jakub Halfar's Theorem C
(`TheoremC.lean`, `SBridgeTheoremC.lean`) and the soundness of his window search (`SSound.lean`,
`SModel.lean`), all unchanged, to a new pair of constants on 9 symbols:

  `c = 111/1000`, `b = 5978/1000`      (`cn = 111`, `bn = 5978`, `q = 1000`).

The window bound for these constants says that every window with `r` pieces and total deficit `δ`
has `2 r + 10 + (111/1000) δ ≤ 6 δ + 5978/1000`.  Theorem C then gives

  `hpv 9 + ⌈(2 · 7! - 14 - 5978/1000) / (46 - 8 · 111/1000)⌉ = 408246 + ⌈222.99…⌉ = 408470`.

The hypothesis is one equation: the window search, or its compiled copy (`W9/SearchC.lean`, equal to
it by `W9/SearchCEq.lean`), answers `false` for these constants.

Everything in this file is checked by the kernel; it uses no `native_decide`.
-/

namespace SuperpermLowerBounds

/-- The three arithmetic conditions of Theorem C. -/
theorem conditionsC_9_111_5978_1000 : ConditionsC 9 111 5978 1000 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The value of the bound. -/
theorem boundC_9_111_5978_1000 : boundC 9 111 5978 1000 = 408470 := by decide

/-- The window bound for model chains on 9 symbols, from the search. -/
theorem modelStatement_9_111_5978_1000_of_search {fuel : ℕ}
    (h : S.search 9 5889 2000 10000 12000 5978 fuel = false) : ModelStatement 9 111 5978 1000 :=
  modelStatement_of_search (k := 9) (cn := 111) (bn := 5978) (q := 1000) (A := 5889) (q2 := 2000)
    (C1 := 10000) (C2 := 12000) (fuel := fuel)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_9 h

/-- **One search that answers `false` gives 408,470** (the search of `SSearch.lean`). -/
theorem covers_boundC_9_of_search {fuel : ℕ}
    (h : S.search 9 5889 2000 10000 12000 5978 fuel = false) :
    ∀ w : List (Fin 9), SuperpermutationBounds.Covers w → 408470 ≤ w.length :=
  boundC_9_111_5978_1000 ▸ covers_length_ge_boundC_of_model (by decide)
    conditionsC_9_111_5978_1000 (modelStatement_9_111_5978_1000_of_search h)

/-- The same from the compiled copy of the search. -/
theorem covers_boundC_9_of_searchC {fuel : ℕ}
    (h : S.searchC 9 5889 2000 10000 12000 5978 fuel = false) :
    ∀ w : List (Fin 9), SuperpermutationBounds.Covers w → 408470 ≤ w.length :=
  covers_boundC_9_of_search ((S.searchC_eq 9 5889 2000 10000 12000 5978 fuel).symm.trans h)

/-- The same for `Hunter.Ssuper 9`. -/
theorem superperm_boundC_9_of_searchC {fuel : ℕ}
    (h : S.searchC 9 5889 2000 10000 12000 5978 fuel = false) : 408470 ≤ Hunter.Ssuper 9 :=
  boundC_9_111_5978_1000 ▸ superperm_boundC_of_model (by decide) conditionsC_9_111_5978_1000
    (modelStatement_9_111_5978_1000_of_search
      ((S.searchC_eq 9 5889 2000 10000 12000 5978 fuel).symm.trans h))

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_boundC_9_of_search
#print axioms SuperpermLowerBounds.covers_boundC_9_of_searchC

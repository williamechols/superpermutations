import AlmanacDefs
import LowerBounds.SModel
import LowerBounds.SRun
import LowerBounds.SBridgeTheoremC
import LowerBounds.SGen.C11_917_41392_10000

/-!
# S(11) ≥ 43,917,904, checked by the Lean kernel alone

Every word over 11 symbols that contains all 39,916,800 permutations as contiguous parts has at
least 43,917,904 letters. The proof has no `native_decide`.

It applies Jakub Halfar's Theorem C (`TheoremC.lean`, `SBridgeTheoremC.lean`) and the soundness of his
window search (`SSound.lean`, `SModel.lean`), all unchanged, to a new pair of constants on 11 symbols:

  `c = 917/10000`, `b = 41392/10000`      (`cn = 917`, `bn = 41392`, `q = 10000`).

The window bound for these constants says that every window with `r` pieces and total deficit `δ`
has `2 r + 14 + (917/10000) δ ≤ 8 δ + 41392/10000`.  Theorem C then gives

  `hpv 11 + ⌈(2 · 9! - 18 - 4.1392) / (78 - 10 · 0.0917)⌉ = 43908488 + ⌈9415.13…⌉ = 43917904`.

That the window bound holds is the equation `S.search 11 79083 20000 140000 160000 41392 2538 = false`
(`A = q (k - 3) - cn = 79083`, `q2 = 2 q = 20000`, `C1 = 2 q (k - 4) = 140000`,
`C2 = 2 q (k - 3) = 160000`).  The search has 32,458 states; the files of `LowerBounds/SGen/`,
written by Halfar's generator `s_plan2.py`, cut it into 266 lemmas that the kernel evaluates by
`decide +kernel` (`SGen.search_C11_917_41392_10000`).
-/

namespace SuperpermLowerBounds
namespace K11

/-- The three arithmetic conditions of Theorem C. -/
theorem conditionsC : ConditionsC 11 917 41392 10000 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The value of the bound. -/
theorem boundC_eq : boundC 11 917 41392 10000 = 43917904 := by decide

/-- The window bound for model chains on 11 symbols, from the search evaluated by the kernel. -/
theorem modelStatement : ModelStatement 11 917 41392 10000 :=
  modelStatement_of_search (k := 11) (cn := 917) (bn := 41392) (q := 10000) (A := 79083)
    (q2 := 20000) (C1 := 140000) (C2 := 160000) (fuel := 2538)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    S.runSearch_11 SGen.search_C11_917_41392_10000

/-- Every covering word on 11 symbols has at least 43,917,904 letters. -/
theorem covers_43917904 :
    ∀ w : List (Fin 11), SuperpermutationBounds.Covers w → 43917904 ≤ w.length :=
  boundC_eq ▸ covers_length_ge_boundC_of_model (by decide) conditionsC modelStatement

/-- The same for `Hunter.Ssuper 11`. -/
theorem ssuper_43917904 : 43917904 ≤ Hunter.Ssuper 11 :=
  boundC_eq ▸ superperm_boundC_of_model (by decide) conditionsC modelStatement

/-- The Almanac's statement. -/
theorem lowerBoundAt_11_43917904 : Almanac.LowerBoundAt 11 43917904 := by
  intro w hw
  apply covers_43917904 w
  intro p hl hn
  obtain ⟨s, t, h⟩ := hw p hn hl
  exact ⟨s, t, h.symm⟩

end K11
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K11.lowerBoundAt_11_43917904

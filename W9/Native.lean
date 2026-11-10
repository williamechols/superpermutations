import W9.SearchC

/-!
# The window search on 9 symbols for `c = 111/1000`, `b = 5978/1000`, evaluated as compiled code

**Trusted here.**  The theorem of this file is proved by `native_decide`: Lean does not check the
computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.S.searchC_9_111_5978_1000._native.native_decide.ax_1_1`, listed by
`#print axioms`).  So this file trusts, in addition to the kernel: the Lean compiler (from
`LowerBounds/SSearch.lean` and `W9/SearchC.lean` to C), the C compiler of the Lean toolchain, the Lean runtime, and
that the shared library that Lake builds from these two files and loads (the library
`WSearchEngine` of `lakefile.toml`, with `precompileModules`) was compiled from them as they are.

What is evaluated: `S.searchC 9 5889 2000 10000 12000 5978 1200`, the compiled copy
(`W9/SearchC.lean`) of Halfar's window search with `q = 1000`, `cn = 111`, `bn = 5978`:
`A = q (k - 3) - cn = 5889`, `q2 = 2 q = 2000`, `C1 = 2 q (k - 4) = 10000`,
`C2 = 2 q (k - 3) = 12000`, fuel 1200 pieces.  That the copy is equal to the search of
`SSearch.lean` is proved by the kernel in `W9/SearchCEq.lean`, and that the answer `false` of that
search means what is claimed is proved by the kernel in `SSound.lean` and `SModel.lean`.

Reference: a C program that shares no code with these files (`tools/window.c`) visits
25,214,918 states for this search, the deepest with 1,065 pieces, and finds no violating window;
the least `bn` that passes is exactly 5978.  The same program gives Halfar's counts for his
certificates (886 states for `9 21 630 250`, 50,100 for `9 1 38 10`, 827,022 for `8 41 1188 100`).

This file imports `W9/SearchC.lean` only.
-/

namespace SuperpermLowerBounds
namespace S

/-- **Evaluated.**  The compiled window search on 9 symbols with `c = 111/1000` and
`b = 5978/1000` finds no violating window. -/
theorem searchC_9_111_5978_1000 : searchC 9 5889 2000 10000 12000 5978 1200 = false := by
  native_decide

end S
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.S.searchC_9_111_5978_1000

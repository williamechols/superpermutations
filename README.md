# S(9) ≥ 408,470

A superpermutation on 9 symbols is a word that contains each of the 362,880 permutations of the symbols as a
contiguous part. This repository proves in Lean 4 that every superpermutation on 9 symbols has at least
**408,470** letters. One finite search is evaluated by `native_decide`; everything else is checked by the
kernel.

```lean
-- AlmanacSolution.lean
theorem lower_nine : Almanac.LowerBoundAt 9 408470 := SuperpermLowerBounds.W9.lowerBoundAt_9_408470
```

`Almanac.LowerBoundAt 9 408470` is the statement of the Superpermutation Almanac (`AlmanacDefs.lean`):
`∀ w : List (Fin 9), (∀ p, p.Nodup → p.length = 9 → p <:+: w) → 408470 ≤ w.length`. Its axioms are
`propext`, `Classical.choice`, `Quot.sound` and the one axiom that `native_decide` records
(`SuperpermLowerBounds.S.searchC_9_111_5978_1000._native.native_decide.ax_1_1`).

Before this, the best bound was Jakub Halfar's 408,469 (his Theorem C, checked by the kernel alone). The
shortest known word has 408,731 letters (rumstd).

## How the proof goes

The proof is Halfar's Theorem C
([github.com/jhalfar/superpermutations](https://github.com/jhalfar/superpermutations), `proofs/lean/lower/`),
used unchanged, with a new pair of constants.

A path through all permutations is cut into blocks (a permutation followed by its rotations), blocks joined by
steps of cost 2 form a piece, and pieces joined by steps of cost exactly 3 form a chain. A piece with fewer
than `k - 1` blocks is partial, and its deficit is the number of blocks it lacks. A *window* is a chain that
starts and ends with a partial piece. Theorem C says: if every window with `r` pieces and total deficit `δ`
satisfies

    2 r + 2 (k - 4) + c δ ≤ (k - 3) δ + b,

then every superpermutation on `k` symbols has at least

    hpv(k) + ⌈ (2 (k-2)! - 2 (k-2) - b) / (k² - 4k + 1 - c (k-1)) ⌉

letters, where `hpv(k) = k! + (k-1)! + (k-2)! + k - 3`. A larger `c` gives a larger bound, and a finite search
decides which `c` can be had.

1. **The constants.** Halfar's certificate for 9 symbols has `c = 21/250`, `b = 630/250`. Its search has 886
   states and gives 408,469. Here `c = 111/1000` and `b = 5978/1000`, and the formula is
   `408246 + ⌈222.99…⌉ = 408470` (`W9/Bound.lean`: `conditionsC_9_111_5978_1000`,
   `boundC_9_111_5978_1000`, both by `decide`).
2. **The search.** That the window bound holds for these constants is one equation: Halfar's window search
   `S.search 9 5889 2000 10000 12000 5978 fuel` answers `false`. His `modelStatement_of_search` and
   `covers_length_ge_boundC_of_model` turn that equation into the bound; both are checked by the kernel. The
   search has 25,214,918 states, and its deepest window has 1,065 pieces. That is about 30,000 times his, and
   too much for the kernel, which needs 12 to 15 ms for a state.
3. **A compiled copy.** `LowerBounds/SSearch.lean` is written for the kernel, with recursors in place of
   pattern matching, and Lean does not compile it. `W9/SearchC.lean` defines the same functions again by
   pattern matching. `W9/SearchCEq.lean` proves, with the kernel, that every copy is equal to its original:
   `searchC_eq : searchC k A q2 C1 C2 bn fuel = search k A q2 C1 C2 bn fuel`. It uses only the equations
   that `SSearch.lean` proves after each definition.
4. **The evaluation** (`W9/Native.lean`):

   ```lean
   theorem S.searchC_9_111_5978_1000 : S.searchC 9 5889 2000 10000 12000 5978 1200 = false := by
     native_decide
   ```

`W9/Main.lean` puts the parts together and proves the Almanac's statement.

The constant `c = 111/1000` is close to the least that gives 408,470 (it needs `c > 0.11098`). The search
grows by a factor of about ten for each 0.005 in `c`, and 408,471 would need `c ≈ 0.142`.

## Trust

The Lean kernel and the three standard axioms for everything except one equation. For
`S.searchC_9_111_5978_1000` the Lean compiler, the C compiler of the Lean toolchain and the Lean runtime are
trusted as well. `lakefile.toml` puts `LowerBounds.SSearch` and `W9.SearchC` in a library of their own,
`WSearchEngine`, with `precompileModules = true`, so the evaluation runs compiled code. There is no `sorry`,
no `implemented_by` or `extern`, no macro and no axiom of our own.

Two C programs in `tools/` were used to find the constants and to check the result outside Lean; the proof
does not use them. They share no code with the Lean files.

* `tools/window.c` is the window search. It visits 25,214,918 states for these constants, finds no violating
  window, and shows that 5978 is the least `bn` that passes for `cn = 111`, `q = 1000`. It gives Halfar's
  state counts for his certificates (886 for `9 21 630 250`, 50,100 for `9 1 38 10`, 827,022 for
  `8 41 1188 100`).
* `tools/linesearch.c` is the line search of Halfar's Theorem D. Every chain on 9 symbols satisfies
  `18 r ≤ 53 δ + 176` (6,902,019,342 chains, the largest surplus exactly 176), which gives 408,470 by another
  route. It gives Halfar's count of 776,981,464 chains for his line `4 r ≤ 9 δ + 56` on 8 symbols.

```sh
gcc -O2 -DN=9 -o win9 tools/window.c && ./win9 111 1000
gcc -O2 -DN=9 -o line9 tools/linesearch.c && ./line9 18 53 0
```

## Building

Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```sh
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_nine\n' > Axioms.lean
lake env lean Axioms.lean
```

The evaluation of the search (`W9.Native`) took 12 minutes on one thread of a desktop machine that was busy
with other work. The rest is the build of about 180 modules on top of the compiled Mathlib.

## Credits and licences

* Theorem C, the window search `SSearch.lean` and the proof that its answer `false` means what is claimed
  are **Jakub Halfar's**
  ([github.com/jhalfar/superpermutations](https://github.com/jhalfar/superpermutations), commit `a93638e`,
  Apache-2.0). They are in `LowerBounds/` and `Superperm/`.
* `Hunter/` is the Hunter–Raudvere library
  ([github.com/urdvr/superpermutations-hunter](https://github.com/urdvr/superpermutations-hunter), commit
  `d452221`, Apache-2.0).
* `PreimageChain/` is Xiaolong Liu's preimage-chain library
  ([github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds),
  commit `8474c74`, CC BY 4.0).
* `Challenge.lean` (`Covers`) is Jay Pantone's
  ([github.com/jaypantone/superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80),
  commit `c8fb7ff`, Apache-2.0).
* New here: the constants `c = 111/1000`, `b = 5978/1000`, the compiled copy of the window search with its
  equality proof, and the two C programs. The port of the vendored files to Lean 4.35 is the one of
  [S(7) ≥ 5,897](https://github.com/williamechols/superpermutations/tree/lean-s7-5897); `NOTICE` lists the
  changed files.

The new files are under the Apache License 2.0 (`LICENSE`). The third-party files keep their licences
(`LICENSES/`, `NOTICE`).

The new files were written by Claude (Anthropic) working for William Echols.

# S(11) ≥ 43,917,904, checked by the Lean kernel alone

A superpermutation on 11 symbols is a word that contains each of the 39,916,800 permutations of the symbols as
a contiguous part. This repository proves in Lean 4 that every superpermutation on 11 symbols has at least
**43,917,904** letters, with no `native_decide`: every finite computation is evaluated by the kernel
(`decide +kernel`).

```lean
-- AlmanacSolution.lean
theorem lower_eleven : Almanac.LowerBoundAt 11 43917904 := SuperpermLowerBounds.K11.lowerBoundAt_11_43917904
```

`Almanac.LowerBoundAt 11 43917904` is the statement of the Superpermutation Almanac (`AlmanacDefs.lean`):
`∀ w : List (Fin 11), (∀ p, p.Nodup → p.length = 11 → p <:+: w) → 43917904 ≤ w.length`. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

Before this, the best bound was Jakub Halfar's 43,917,903 (his Theorem C, also checked by the kernel alone).
The shortest known word has 43,930,534 letters (Jakub Halfar).

## How the proof goes

The proof is Halfar's Theorem C
([github.com/jhalfar/superpermutations](https://github.com/jhalfar/superpermutations), `proofs/lean/lower/`),
used unchanged, with a new pair of constants and a certificate written by his own generator.

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

1. **The constants.** Halfar's best certificate for 11 symbols has `c = 91/1000`, `b = 4016/1000`. Its search
   has 14,992 states and gives 43,917,903. Here `c = 917/10000` and `b = 41392/10000`, and the formula is
   `43908488 + ⌈9415.13…⌉ = 43917904` (`K11/Main.lean`: `conditionsC`, `boundC_eq`, both by `decide`).
2. **The search.** That the window bound holds for these constants is one equation: Halfar's window search
   `S.search 11 79083 20000 140000 160000 41392 2538` answers `false`. The search has 32,458 states, and its
   deepest window has 2,538 pieces.
3. **The certificate** (`LowerBounds/SGen/`, 84 generated files). One evaluation of 32,458 states is too much
   for the kernel, so Halfar's generator `tools/s_plan2.py` cuts the search into 266 lemmas of at most 591
   states, each proved by `decide +kernel`, with the state at every cut written out. His `SCut.lean`,
   `SLit.lean` and `SDec.lean` put the parts together: `SGen.search_C11_917_41392_10000`. The generator
   decides only where to cut. A wrong cut or a wrong state makes a lemma fail; it cannot make a false
   statement pass.
4. **The bound** (`K11/Main.lean`). His `modelStatement_of_search` and `covers_length_ge_boundC_of_model`
   turn the equation into the bound, and the last theorem states it in the Almanac's form.

The constant `c = 917/10000` is close to the least that gives 43,917,904 (it needs `c > 0.091689`). The search
grows very fast in `c`: 14,992 states at 0.091, 32,458 here, 7.8 million at 0.09251 (which gives 43,917,905),
158 million at 0.093.

## Trust

The Lean kernel with its arithmetic on natural numbers, and the three standard axioms. There is no
`native_decide`, no `Lean.ofReduceBool`, no `implemented_by` or `extern`, no `sorry` and no axiom of our
own. The generated files of `LowerBounds/SGen/` are not trusted: every lemma in them is checked by the
kernel.

`tools/` holds what was used outside Lean; the proof does not use it.

* `tools/s_plan2.py` and `tools/s_ksim.py` are Halfar's generator and its Python copy of the search. To write
  the certificate again, copy both to the root of the repository and run

  ```sh
  python3 s_plan2.py 11 917 41392 10000 C11_917_41392_10000 --leaf 500 --band 300 --per-file 3000
  ```

  It writes the same 84 files to `LowerBounds/SGen/`.
* `tools/window.c` (with `tools/tables.h`) is a C version of the window search that shares no code with the
  Lean files or with the generator. It was used to choose the constants. It visits 32,458 states for them,
  finds no violating window, and shows that 41392 is the least `bn` that passes for `cn = 917`, `q = 10000`.
  It gives Halfar's state counts for his certificates (14,992 for `11 91 4016 1000`, 886 for `9 21 630 250`,
  827,022 for `8 41 1188 100`). For 11 symbols it needs about 1.3 GB of memory.

  ```sh
  gcc -O2 -DN=11 -o win11 tools/window.c && ./win11 917 10000
  ```

## Building

Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```sh
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_eleven\n' > Axioms.lean
lake env lean Axioms.lean
```

With the vendored libraries already compiled, the 84 certificate files and the final theorem built in under four
minutes on a 12-thread desktop machine that was busy with other work.

## Credits and licences

* Theorem C, the window search `SSearch.lean`, the proof that its answer `false` means what is claimed, the
  lemmas that assemble a cut search, and the generator are **Jakub Halfar's**
  ([github.com/jhalfar/superpermutations](https://github.com/jhalfar/superpermutations), commit `a93638e`,
  Apache-2.0). They are in `LowerBounds/`, `Superperm/` and `tools/`.
* `Hunter/` is the Hunter–Raudvere library
  ([github.com/urdvr/superpermutations-hunter](https://github.com/urdvr/superpermutations-hunter), commit
  `d452221`, Apache-2.0).
* `PreimageChain/` is Xiaolong Liu's preimage-chain library
  ([github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds),
  commit `8474c74`, CC BY 4.0).
* `Challenge.lean` (`Covers`) is Jay Pantone's
  ([github.com/jaypantone/superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80),
  commit `c8fb7ff`, Apache-2.0).
* New here: the constants `c = 917/10000`, `b = 41392/10000`, the certificate generated for them, `K11/Main.lean`
  and `tools/window.c`. The port of the vendored files to Lean 4.35 is the one of
  [S(7) ≥ 5,897](https://github.com/williamechols/superpermutations/tree/lean-s7-5897); `NOTICE` lists the
  changed files.

The new files are under the Apache License 2.0 (`LICENSE`). The third-party files keep their licences
(`LICENSES/`, `NOTICE`).

The new files were written by Claude (Anthropic) working for William Echols.

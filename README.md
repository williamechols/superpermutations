# S(7) ≥ 5,897, checked by the Lean kernel alone

A superpermutation on 7 symbols is a word that contains each of the 5,040 permutations of the symbols as a
contiguous part. This repository proves in Lean 4 that every superpermutation on 7 symbols has at least
**5,897** letters, with no `native_decide`: every finite computation is evaluated by the kernel
(`decide +kernel`).

```lean
-- AlmanacSolution.lean
theorem lower_seven : Almanac.LowerBoundAt 7 5897 := SuperpermLowerBounds.K5897.lowerBoundAt_7_5897
```

`Almanac.LowerBoundAt 7 5897` is the statement of the Superpermutation Almanac (`AlmanacDefs.lean`):
`∀ w : List (Fin 7), (∀ p, p.Nodup → p.length = 7 → p <:+: w) → 5897 ≤ w.length`. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

Before this, the best bound checked by the kernel alone was Jakub Halfar's 5,895 (his general Theorem B).
Larger bounds, Justin Lebar's 5,898 and Halfar's 5,899 and 5,900, evaluate their searches with
`native_decide`. The shortest known word has 5,905 letters (Andrei Teodorescu).

## How the proof goes

Everything rests on Halfar's model of *standard configurations*
([github.com/jhalfar/superpermutations](https://github.com/jhalfar/superpermutations), `proofs/lean/n7/`),
whose first level is checked by the kernel. Its Theorems W and N (`covers_length_gt_of_no_stdConfig`) say
that `S(7) ≥ 5884 + D + 1` as soon as no valid configuration has cost at most `5! + D`. For `D = 14` (5,899)
Halfar's proof needs sequences, rings, hanging items and five profiles, and chain caps that are nearly
exact up to 84 holes. Its searches visit 1.1·10¹¹ nodes, which is why they are compiled.

At `D = 12` the coarse part of his argument is enough.

1. **Accounting** (`K5897/Final.lean`; Halfar's Lemmas ACC and FAM with new constants). A configuration
   of cost at most 132 gives a family of class-disjoint chains (*trails*) of weight `Σ (holes + 6) ≤ 78`
   and value `Σ (rows − holes − 5) ≥ 55`.
2. **Knapsack** (`K5897/Arith.lean`). Take chain caps `T(x) ≈ 6.64 + 1.74 x` for chains with `x ≤ 72`
   holes (`K5897/Caps.lean`). Then every such family has value at most 54. A certificate table is checked
   by `decide +kernel`.
3. **Caps** (`K5897/Search.lean`). A chain on 7 symbols with `x ≤ 72` holes has at most `T(x)` rows. The
   caps are much looser than the true maxima, so the pruning rule of Halfar's search (Rule F0: a minimal
   counterexample cut after any row leaves a suffix within the caps) cuts the search down to 12,976 nodes.

The finite search is the engine of Halfar's kernel-only proof of `S(6) = 872`
(`proofs/lean/small/K6/`), rewritten here for 7 symbols:

* `K5897/Engine.lean`: tables read from big numbers with shifts, and the used classes as a bit set.
* `K5897/Enc.lean`, `K5897/EngineOK.lean`: a word is the Lehmer rank of its code. Six scans of the
  5,040 words, evaluated by the kernel, check the tables against the arithmetic of Halfar's `PSearch.lean`
  (`PS.encA`).
* `K5897/Sound.lean`, `K5897/Cap.lean`: the completeness of the search, and the bridge to Halfar's
  statement `PS.PStmt`. These are ports of `K6/Sound.lean` and `K6/Cap.lean`. From `PS.PStmt` Halfar's
  `seqCap_level`, `wcap_of_seqCap` and `chainCapK_of_wcap` give the caps.
* `K5897/CapEval.lean`: the search itself. The kernel evaluates it in about 5 seconds.

## Trust

The Lean kernel with its arithmetic on natural numbers, and the three standard axioms. There is no
`native_decide`, no `Lean.ofReduceBool`, no `implemented_by` or `extern`, no `sorry` and no axiom of our
own. The tables in `K5897/Tab.lean`, `K5897/Caps.lean` and `K5897/CapTab.lean` are not trusted. They were
written by `tools/gen_tables.py`, and a wrong entry makes a kernel check fail. `tools/f0.c` is the C version
of the search that was used to choose the caps; the proof does not use it.

## Building

Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```sh
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_seven\n' > Axioms.lean
lake env lean Axioms.lean
```

A clean build of the 220 modules on top of the compiled Mathlib takes about 10 minutes on 8 cores. The
largest process uses about 12 GB.

## Credits and licences

* The model of standard configurations, Theorems W and N, the search engine `PSearch.lean` with its
  completeness proof and Rule F0, the accounting lemmas, and the kernel engine that `K5897/Engine.lean`,
  `Sound.lean` and `Cap.lean` port are **Jakub Halfar's**
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
* New here: the observation that the family bound suffices at defect 12 with steep caps, the caps and the
  knapsack certificate, the 7-symbol tables and encoding with their checks, the 7-symbol port of the
  kernel engine, and the port of all the files above to Lean 4.35 and the current Mathlib. Five files
  needed small changes for the port; `NOTICE` lists them, and each is marked in the source.

The new files are under the Apache License 2.0 (`LICENSE`). The third-party files keep their licences
(`LICENSES/`, `NOTICE`).

The new files were written by Claude (Anthropic) working for William Echols.

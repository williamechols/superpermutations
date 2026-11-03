/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Defs
import Hunter.Appendix
-- No proof file imports `Hunter.Statements`, so every proof file is importable here.
-- These leaves pull in the whole proof tree transitively (GB2→B2→{WP,Pathrule,Reductions,More}, GB2→Recursion;
-- Greedy→{More,Recursion}; Unwind→Pathrule→Structure→{Spine,Exitless}; SPrime→Excess→
-- Recursion→Confinement→Exitless).
import Hunter.ProofsReductions
import Hunter.ProofsGB2
import Hunter.ProofsGreedy
import Hunter.ProofsGreedy2
import Hunter.ProofsUnwind
import Hunter.ProofsUnwind2
import Hunter.ProofsSPrime
import Hunter.ProofsDeficit
import Hunter.ProofsWindow
-- `ProofsHrev` transitively pulls in `ProofsUnwind4` and `ProofsPu`; `ProofsPhi` and `ProofsLstar` add the φ-form and `L* = Ssuper` bridges.
-- None of these import `Hunter.Statements`, so there is no build cycle.
import Hunter.ProofsHrev
import Hunter.ProofsPhi
import Hunter.ProofsLstar
import Hunter.ProofsLink2
import Hunter.ProofsHeadline

/-!
# Statement skeleton for Hunter, *A New Lower Bound for Superpermutations*

All 57 numbered statements below are proved and **wired** to the proof development: each
theorem's body is a proved `Hunter.Proved.*` (or proof-tree) term of the same type.  Items
whose proved version carries an **extra guard** (`3 ≤ k`, `2 ≤ k`, `1 ≤ k`) / an extra
structural precondition (`S ⊆ V(P)`) / a corrected statement (the scaffold
`StronglyExitless ↔ IsUnionOfCycles` is **false** unguarded) are amended with that guard + an
`AMENDED from paper/scaffold` docstring + an `AMBIGUITIES.md` entry; the original unamended
statements are preserved verbatim in the docstrings.  All 57 declarations are axiom-clean and
**no `sorry` remains** anywhere in the project (`imp_reduced`, the §7 remark, is proved by the
`ImpRed` surgery below).  See `STATUS.md` and the executable `AxiomCheck.lean` audit.

Faithful Lean 4 statements of every Theorem / Lemma / Proposition / Claim / Corollary /
Reduction / Bound and numbered display fact in the digest's statement inventory (`DIGEST.md`
§3), in paper order, followed by scaffolding statements. Definitions live in `Hunter/` and
`Hunter/Appendix.lean`; proofs are wired from the `Proofs*.lean` modules.

Faithfulness conventions honoured (see `AMBIGUITIES.md`):
* `iExitless k ℓ = 0` when no exitless path of `ℓ` vertices exists — so every claim about
  `i_k` carries the existence guard `HasExitlessPath k ℓ` (or `0 < ℓ ≤ …` on the base
  interval where such a path provably exists).
* `MinThrough` uses truncated ℕ subtraction; the weight bookkeeping (`clm-eqq`,
  `lem-weightrule`) is stated over `ℤ` to avoid truncation.
* Per the digest verdict, the two **Reductions** use take23's `≥` form (not main's `=`).
* Guards `k ≥ 3` are added where the paper works only for `k` large / where `ℓ₀`, `j`'s
  recursion, and the arithmetic need it; these are flagged in the docstrings and
  `AMBIGUITIES.md`.

The `min_{X∈𝒳_k}{…}` / `min_{p*∈…}{…}` optima of the paper are rendered as `sInf` of the
corresponding value set (nonempty in the paper's regime, so the `sInf ∅` junk does not
bite the intended claim).
-/

namespace Hunter

open List
open scoped Classical

/-! ## Headline results (`DIGEST.md` §3, "Headline results") -/

/-- **thm1v1** — Theorem 1, `main_version.tex` §1 l.93.  The main lower bound on
superpermutation length:
`L*(k) ≥ (1 + 1/k + 1/(k(k−1)) + 1/((k−1)(k(k−1)(k−2)−k)))·k! + k + O(1)`.
The `+ O(1)` slack is stated as: some absolute constant `C` and threshold `k₀` with the
bound holding within `C` for all `k ≥ k₀`.  [**PROVED — UNCONDITIONAL**] — follows from
`thm1v2` via `L*(k) = L(k) + k`.  **WIRED** to `Hunter.ProofsHeadline.thm1v1_unconditional`:
Theorem 2 is now proved (`Hunter.Proved.thm2_unconditional`, residual `TightJumpFreeAll`
discharged as `Hunter.Proved.tightJumpFree`) and the last reduction leaf `hproof`/`proof_thm1v2`
is assembled in-tree (`ProofsHeadline.proof_thm1v2_all`).  Axiom-clean. -/
theorem thm1v1 :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsHeadline.thm1v1_unconditional

/-- **eq-weak** — `main_version.tex` §1 l.95.  The weaker, more comparable form:
`L*(k) ≥ k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)! + O((k−6)!)`.  [**PROVED — UNCONDITIONAL**];
the `O((k−6)!)` slack is a constant multiple of `(k−6)!`.  **WIRED** to
`Hunter.ProofsHeadline.eq_weak_unconditional` (same closure as `thm1v1`).  Axiom-clean. -/
theorem eq_weak :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  ProofsHeadline.eq_weak_unconditional

/-- **thm1v2** — Theorem, `main_version.tex` §"Outline" l.191.  The real theorem (thm1v1
minus the trivial `+k`):
`L(k) ≥ (1 + 1/k + 1/(k(k−1)) + 1/((k−1)(k(k−1)(k−2)−k)))·k! + O(1)`.
[**PROVED — UNCONDITIONAL**].  All former inputs are now discharged in-tree: `thm2`
(`Hunter.Proved.thm2_unconditional`), `b1`/`b2`, `prp-Xk-se`, the two reductions
(`red_pstar_closed`, `red_R_closed`) and the subproblem solutions; the §6.4 analytic assembly
is `ProofsHeadline.proof_thm1v2_all`.  **WIRED** to
`Hunter.ProofsHeadline.thm1v2_unconditional`.  Axiom-clean. -/
theorem thm1v2 :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsHeadline.thm1v2_unconditional

/-- **thm2** — Theorem 2, `main_version.tex` §"Outline" l.198 (+ appendix).  The crux
lower bound: `j_k(ℓ) ≤ i_k(ℓ)` for all `ℓ` (in the support of `i_k`). The source draft's
appendix proof was unwritten; this development supplies the missing argument. Guarded by
`HasExitlessPath k ℓ` because `i_k(ℓ) = 0` on the empty set (see `AMBIGUITIES.md` §E2);
`k ≥ 3` is added (the paper works for `k` large, and `j`/`ℓ₀` are only meaningful there).
[**PROVED** — `Hunter.Proved.thm2_unconditional`, via the rigidity/chart route; no longer a
gap.  Axiom-clean.] -/
theorem thm2 {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ := Hunter.Proved.thm2_unconditional k ℓ hk hℓ

/-- **thm2-equality** (a.k.a. **thm2-restated**) — `main_version.tex` §"Solving" l.679.
The equality clause of Theorem 2: `i_k(ℓ) = j_k(ℓ)` for `0 < ℓ ≤ k(k−1)(k−2)` (needs both
the `≥` from thm2 and the `≤` from `greedy-g`).  [PROVED: full-range greedy witness
(`ProofsGreedy2`) + `thm2_base_unconditional`].  This supplies the
exact value `i_k(k(k−1)(k−2)) = k²(k−2)−3`. -/
theorem thm2_equality {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) (hex : HasExitlessPath k ℓ) :
    iExitless k ℓ = j k ℓ := Hunter.Proved.thm2_equality hk hℓ0 hℓ hex

/-! ## thm2 — useful bounded-range corollaries

The following four theorems predate the final all-length closure and retain useful sharper
coverage information, including equality and explicit greedy witnesses. They are all proved
axiom-cleanly and wired to the proof tree. -/

/-- **thm2_small** — Theorem 2 (`j_k(ℓ) ≤ i_k(ℓ)`) holds for **all** `ℓ` when `3 ≤ k ≤ 4`.
The small cases are closed outright by the level-`≥3` confinement being exact there.  Wired to
`Hunter.ProofsRecursion.thm2_small`. -/
theorem thm2_small {k ℓ : ℕ} (hk : 3 ≤ k) (hk4 : k ≤ 4) (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  ProofsRecursion.thm2_small hk hk4 hex

/-- **thm2_upto** — Theorem 2 (`j_k(ℓ) ≤ i_k(ℓ)`) holds for every `0 < ℓ ≤ k²(k−2)` and all
`k ≥ 3`: the base region `k(k−1)(k−2)` extended by the entire first recursion interval.
It strictly extends `thm2_base_unconditional`. Wired to `Hunter.ProofsExcess.thm2_upto`. -/
theorem thm2_upto {k ℓ : ℕ} (hk : 3 ≤ k) (hhi : ℓ ≤ k ^ 2 * (k - 2))
    (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  ProofsExcess.thm2_upto hk hhi hex

/-- **thm2_equality_le_kk** — the equality clause `i_k(ℓ) = j_k(ℓ)` holds unconditionally for
`0 < ℓ ≤ k(k−1)` (`k ≥ 3`).  Both directions are closed here: `≥` from the base-region thm2
and `≤` from the greedy construction on the 2-cycle range.  Wired to
`Hunter.Proved.thm2_equality_le_kk` (`Hunter/ProofsGreedy.lean`). -/
theorem thm2_equality_le_kk {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    iExitless k ℓ = j k ℓ :=
  Proved.thm2_equality_le_kk hk hℓ0 hℓ

/-- **greedy_g_le_kk** — the greedy witness realizing `j_k` exists for `0 < ℓ ≤ k(k−1)`
(`k ≥ 3`): an exitless path of `ℓ` vertices and weight exactly `j_k(ℓ)`. This useful restricted
form predates the full-base-region theorem `greedy_g`. Wired to
`Hunter.Proved.greedy_g_le_kk` (`Hunter/ProofsGreedy.lean`). -/
theorem greedy_g_le_kk {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1)) :
    ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ ∧ p.wtP = j k ℓ :=
  Proved.greedy_g_le_kk hk hℓ0 hℓ

/-! ## Bounds (`DIGEST.md` §3, "Bounds") -/

/-- **b1** — Bound 1, `main_version.tex` §"Outline" l.183.
`L(k) ≥ min_{X∈𝒳_k} { (|Comps(X)|−1) + MinThrough(X) + w(X) }`.  [PROVED] — from
`prp-wPgivenX` and the definition of `𝒳_k`.  The `min` is rendered as `sInf` of the value
set over `𝒳_k`.

**WIRED** to `Hunter.Proved.b1_final`.  **AMENDED from paper: added guard `2 ≤ k`** — the
`prp-wPgivenX`/`𝒳_k` machinery it is built on needs `k ≥ 2` (the transformation `F` and the
weight rule are vacuous/degenerate for `k ≤ 1`).  Paper works for `k` large.  See
`AMBIGUITIES.md` §"Final-integration amendments". -/
theorem b1 {k : ℕ} (hk : 2 ≤ k) :
    L k ≥ sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} :=
  Proved.b1_final hk

/-- **b2** — Bound 2, `main_version.tex` §"Getting Bounds" l.536 / take23 l.649.
`L(k) ≥ min_{p*∈𝒳'_k} { w(p*) + R_k·(k!−|p*|) }` (equivalently
`= R_k·k! + min_{p*}{ w(p*) − R_k|p*| }`).  [PROVED] — from b1, prp-Xk-se, prp-gives-b2.
Stated in the first (nonnegative) form; `R_k`-mixed, hence over `ℝ`.

**WIRED** to `Hunter.Proved.b2_final` (`Hunter/ProofsGB2.lean`).  **AMENDED from paper: added
guard `2 ≤ k`** (inherited from b1/prp-gives-b2).  This is the strongest *unconditional*
lower bound at this stage of the reduction: Bound 2 holds outright for every `k ≥ 2`, without
using Theorem 2. See `AMBIGUITIES.md` §"Final-integration amendments". -/
theorem b2 {k : ℕ} (hk : 2 ≤ k) :
    (L k : ℝ) ≥ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} :=
  Proved.b2_final hk

/-! ## §"A Path Transformation" (§4) — `X = f(P,S)`, generic valid `(P,S)` -/

/-- **clm-degree** — `degree rule`, `main_version.tex` §4 l.234.  For a valid `(P,S)`,
`Comps(f(P,S))` is a set of directed paths and directed cycles — i.e. every vertex has
in-degree ≤ 1 and out-degree ≤ 1 in `X = f(P,S)`.  [PROVED] — Step 1 caps out-degree,
Step 2 caps in-degree. -/
theorem clm_degree {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    ∀ v : Vtx k, (outV (fPS P S) v).card ≤ 1 ∧ (intoV (fPS P S) v).card ≤ 1 :=
  Proved.clm_degree hS

/-- **clm-eqq** — `eqq`, `main_version.tex` §4 l.244.  The exact weight bookkeeping for
`X = f(P,S)`:
`w(P) = w(X) + Σ_{e₁∈E₁}(w(e₁)−1) − I + Σ_{e₂∈E₂} w(e₂)`.
[PROVED (from the construction; a formal proof must track the Step-1/Step-2 weight deltas —
a likely sign/`I`-error site)].  Stated over `ℤ` (the `−1`, `−I` can under-truncate in ℕ).

**WIRED** to `Hunter.Proved.clm_eqq_amended` (`Hunter/ProofsStructure.lean`).  **AMENDED from
paper: added guard `1 ≤ k` and the precondition `hSV : S ⊆ P.vertsFinset`** — the weight
bookkeeping is over the vertices of `P`, so the removed-edge sets are only accounted correctly
when `S` sits inside `V(P)` (the paper's notion of a *valid* `(P,S)` includes this; the Lean
`SPrecond` did not spell it out).  See `AMBIGUITIES.md` §"Final-integration amendments". -/
theorem clm_eqq {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hk : 1 ≤ k)
    (hSV : S ⊆ P.vertsFinset) (hS : SPrecond P S) :
    (P.wtP : ℤ) = (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ E2removed P S, (ew k e.1 e.2 : ℤ) :=
  Proved.clm_eqq_amended hk hSV hS

/-- **clm-e2** — `e2`, `main_version.tex` §4 l.261.  `E₂ = out(P, H(X) ∖ H(P))`.
[PROVED] — from clm-degree.  (`H(·)` = heads = out-degree-0 vertices.) -/
theorem clm_e2 {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    E2removed P S = out P.edges (heads (fPS P S) \ heads P.edges) :=
  Proved.clm_e2 hS

/-- **clm-e1** — `e1`, `main_version.tex` §4 l.267.  `into(P, T(X) ∖ T(P)) ⊆ E₁`.
[PROVED].  (`T(·)` = tails = in-degree-0 vertices.) -/
theorem clm_e1 {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    into P.edges (tails (fPS P S) \ tails P.edges) ⊆ E1removed P S :=
  Proved.clm_e1 hS

/-- **lem-weightrule** — `weight rule`, `main_version.tex` §4 l.281.
`w(P) ≥ w(X) + Σ_{e₁∈into(P,T(X)∖T(P))}(w(e₁)−1) − I + Σ_{e₂∈out(P,H(X)∖H(P))} w(e₂)`.
[PROVED] — from clm-eqq, clm-e2, clm-e1 and `w(e₁) ≥ 1`.  Over `ℤ`.

**WIRED** to `Hunter.Proved.lem_weightrule` fed the amended `clm-eqq` (`Proved.clm_eqq_amended`).
**AMENDED from paper: added guard `1 ≤ k` and precondition `hSV : S ⊆ P.vertsFinset`** —
inherited from `clm-eqq`, which it discharges.  See `AMBIGUITIES.md`
§"Final-integration amendments". -/
theorem lem_weightrule {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hk : 1 ≤ k)
    (hSV : S ⊆ P.vertsFinset) (hS : SPrecond P S) :
    (P.wtP : ℤ) ≥ (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ into P.edges (tails (fPS P S) \ tails P.edges), ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ out P.edges (heads (fPS P S) \ heads P.edges), (ew k e.1 e.2 : ℤ) :=
  Proved.lem_weightrule hS (Proved.clm_eqq_amended hk hSV hS)

/-! ## §"Constructing S" (§5) — `X = F(P)` -/

/-- **prp-wPgivenX** — `wP given X`, `main_version.tex` §5 l.305.  For any Hamiltonian `P`,
`X = F(P)`: `w(P) ≥ (|Comps(X)|−1) + MinThrough(X) + w(X)`.  [PROVED] — the core of §4–5
(cor-pathfirst, lem-weightrule, the naive head bound, lem-pathrule).

**WIRED** to `Hunter.Proved.prp_wPgivenX_final` (`Hunter/ProofsB2.lean`).  **AMENDED from
paper: added guard `2 ≤ k`** (the §4–5 chain it composes is only meaningful for `k ≥ 2`).
See `AMBIGUITIES.md` §"Final-integration amendments". -/
theorem prp_wPgivenX {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    P.wtP ≥ (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) :=
  Proved.prp_wPgivenX_final hP hk

/-- **prp-Xk-se (necessity)** — `Xk is strongly exitless`, `main_version.tex` §5 l.315, ⟹.
If `X ∈ 𝒳_k` then `V(X) = V(𝒮_k)` and `Comps(X)` is a set of strongly exitless paths.
[PROVED] — from cor-exitlessrule and `V(F(P)) = V(𝒮_k)`.

**WIRED** to `Hunter.Proved.prp_Xk_se_necessity_final` (`Hunter/ProofsB2.lean`).  **AMENDED
from paper: added guard `2 ≤ k`** (needs cor-exitlessrule, itself `k ≥ 2`).  See
`AMBIGUITIES.md` §"Final-integration amendments". -/
theorem prp_Xk_se_necessity {k : ℕ} {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k)
    (hX : X ∈ Xk k) :
    vertsOf X = Finset.univ ∧ IsUnionOfStronglyExitlessPaths X :=
  Proved.prp_Xk_se_necessity_final hk hX

/-- **prp-Xk-se (sufficiency)** — `main_version.tex` §5 l.315, ⟸.  If `V(X) = V(𝒮_k)` and
`Comps(X)` is a set of strongly exitless paths, then `X ∈ 𝒳_k`.  The paper's "unwinding"
`P(p₁,…,p_n)` construction (`ADD DIAGRAM`, `DIGEST.md` §5.1(4)), now fully formalized.

**WIRED** to `Hunter.Proved.prp_Xk_se_sufficiency` (`Hunter/ProofsUnwind4.lean`).  **AMENDED
from paper/scaffold: added guard `2 ≤ k`** (consistent with `prp_Xk_se_necessity`'s `2 ≤ k`;
the verbatim statement is degenerate for `k ≤ 1`, where `𝒮_k` has `≤ 1` vertex).  See
`AMBIGUITIES.md` §"Final-consolidation amendments".

Original (unamended) statement, preserved for the record:
```
theorem prp_Xk_se_sufficiency {k : ℕ} {X : Finset (Vtx k × Vtx k)}
    (hspan : vertsOf X = Finset.univ) (hse : IsUnionOfStronglyExitlessPaths X) :
    X ∈ Xk k := sorry
```
-/
theorem prp_Xk_se_sufficiency {k : ℕ} (hk : 2 ≤ k) {X : Finset (Vtx k × Vtx k)}
    (hspan : vertsOf X = Finset.univ) (hse : IsUnionOfStronglyExitlessPaths X) :
    X ∈ Xk k :=
  Proved.prp_Xk_se_sufficiency hk hspan hse

/-- **clm-rule1** — `Rule 1`, `main_version.tex` §5 l.326.  For Hamiltonian `P`, `X=F(P)`:
`v ∈ C₋₁` with `out(X,v) ≠ ∅` ⟹ `out(X,v) = out(P,v)`.  [PROVED] — `v ∉ S(P)`. -/
theorem clm_rule1 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∈ Cm1 P) (hne : outV (F P) v ≠ ∅) :
    outV (F P) v = outV P.edges v :=
  Proved.clm_rule1 hP hv hne

/-- **clm-rule2** — `Rule 2`, `main_version.tex` §5 l.332.  `v ∉ C₋₁` ⟹
`out(X,v) = {(v→σv)}`.  [PROVED].  (The `\edit` "0 out-edges" caveat is not an exception:
if `v ∉ C₋₁` then `v ∈ S(P)`, so the 1-edge is always present.) -/
theorem clm_rule2 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∉ Cm1 P) :
    outV (F P) v = {(v, sigma v)} :=
  Proved.clm_rule2 hP hv

/-- **clm-rule2.5** — `Rule 2.5`, `main_version.tex` §5 l.339.  `v ∉ C₀` ⟹
`into(X,v) = {(σ⁻¹v→v)}`.  [ASSERTED equivalent to clm-rule2 — must be proved as a genuine
equivalence].  `σ⁻¹` is `sigmaInv`. -/
theorem clm_rule2_5 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∉ C0 P) :
    intoV (F P) v = {(sigmaInv v, v)} :=
  Proved.clm_rule2_5 hP hv

/-- **clm-rule2.75** — `Rule 2.75`, `main_version.tex` §5 l.342.  For each 1-cycle `c`, `X`
contains a path of 1-edges covering all of `c` from `c ∩ C₀` to `c ∩ C₋₁` — i.e. every
`u ∉ C₋₁` has its 1-edge `(u→σu) ∈ X`.  [ASSERTED equivalent to clm-rule2]. -/
theorem clm_rule2_75 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hu : u ∉ Cm1 P) :
    (u, sigma u) ∈ F P :=
  Proved.clm_rule2_75 hP hu

/-- **clm-rule3** — `Rule 3`, `main_version.tex` §5 l.347.  `u ∈ C₋₁` with `out(X,u) ≠ ∅`
⟹ `out(X,u) = {(u→v)}` for some `v ∈ C₀`.  [PROVED] — clm-rule1, clm-rule2.5. -/
theorem clm_rule3 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hu : u ∈ Cm1 P) (hne : outV (F P) u ≠ ∅) :
    ∃ v, v ∈ C0 P ∧ outV (F P) u = {(u, v)} :=
  Proved.clm_rule3 hP hu hne

/-- **rmk-rule3** — `main_version.tex` §5 l.362.  The "second case" `v = σ(u)` of clm-rule3
never occurs: the `C₀`-target of `u ∈ C₋₁`'s out-edge is never `σ(u)`.  [PROVED]. -/
theorem rmk_rule3 {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {u v : Vtx k}
    (hu : u ∈ Cm1 P) (h : (u, v) ∈ F P) : v ≠ sigma u :=
  Proved.rmk_rule3 hP hu h

/-- **lem-walking** — `walking`, `main_version.tex` §5 l.374.  **Central lemma.**  For a
directed walk `D` in `X = F(P)` and `u,v ∈ C₀ ∪ C₋₁`: if `u` is reached before `v` in `D`
then `u` is reached before `v` in `P`.  [PROVED] — clm-rule1/2/3. -/
theorem lem_walking {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian)
    {D : List (Vtx k)} (hD : IsWalk (F P) D) {u v : Vtx k}
    (hu : u ∈ C0 P ∪ Cm1 P) (hv : v ∈ C0 P ∪ Cm1 P)
    (huD : u ∈ D) (hvD : v ∈ D) (hlt : D.idxOf u < D.idxOf v) :
    P.pos u < P.pos v :=
  Proved.lem_walking hP hD hu hv huD hvD hlt

/-- **lem-pathrule** — `path rule`, `main_version.tex` §5 l.393.  `Comps(F(P))` is a set of
**paths** (no directed cycle): every component is the vertex set of a path-component.
[PROVED] — clm-degree, lem-walking, clm-rule2.75. -/
theorem lem_pathrule {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) :
    ∀ C ∈ Comps (F P), ∃ p : HPath k, p.vertsFinset = C ∧ IsPathComponent p (F P) :=
  Proved.lem_pathrule hP

/-- **cor-exitlessrule** — `exitless rule`, `main_version.tex` §5 l.424.  `Comps(F(P))` is a
set of **strongly exitless** paths.  [PROVED] — lem-pathrule + clm-rule2. -/
theorem cor_exitlessrule {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) :
    IsUnionOfStronglyExitlessPaths (F P) :=
  Proved.cor_exitlessrule hP

/-- **clm-ordering** — `ordering rule`, `main_version.tex` §5 l.431.  For `p ∈ Comps(F P)`
and `v ∈ C₀ ∪ C₋₁`: if `v` is reached before `u` in `p` then `v` is reached before `u` in
`P`.  [PROVED] — lem-walking (maximal-counterexample).  (The paper's `C₁` is a typo for
`C₋₁`.) -/
theorem clm_ordering {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian)
    {p : HPath k} (hp : IsPathComponent p (F P)) {v u : Vtx k}
    (hv : v ∈ C0 P ∪ Cm1 P) (hvp : v ∈ p.verts) (hup : u ∈ p.verts)
    (hlt : p.pos v < p.pos u) : P.pos v < P.pos u :=
  Proved.clm_ordering hP hp hv hvp hup hlt

/-- **cor-pathfirst** — `path first`, `main_version.tex` §5 l.455.  For `p ∈ Comps(F P)`,
`p[1]` is the first vertex of `p` reached by `P`.  [PROVED] — clm-ordering. -/
theorem cor_pathfirst {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian)
    {p : HPath k} (hp : IsPathComponent p (F P)) {u : Vtx k} (hu : u ∈ p.verts) :
    P.pos p.first ≤ P.pos u :=
  Proved.cor_pathfirst hP hp hu

/-! ## §"Getting Bounds" (§6) — preliminaries on (strongly) exitless graphs -/

/-- **clm-prefix** — `main_version.tex` §6 l.508.  If `p` is exitless then its
`(|p|−1)`-vertex prefix `p[1..|p|−1]` is exitless.  [PROVED].  (Rendered as: there is an
`HPath` on `p.verts.dropLast` that is exitless; needs `|p| ≥ 2`.) -/
theorem clm_prefix {k : ℕ} {p : HPath k} (hp : p.Exitless) (h2 : 2 ≤ p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.dropLast ∧ q.Exitless :=
  Proved.clm_prefix hp h2

/-- **clm-1cyclesubset** — `main_version.tex` §6 l.513.  If `p` is strongly exitless then
`∀ v ∈ p, c(v) ⊆ V(p)` (`p` is a disjoint union of full 1-cycles, so `|p| = tk`).
[PROVED]. -/
theorem clm_1cyclesubset {k : ℕ} {p : HPath k} (hp : p.StronglyExitless) :
    p.IsUnionOfCycles :=
  Proved.clm_1cyclesubset hp

/-- **clm-phi (necessity)** — `main_version.tex` §6 l.523, ⟹.  Every strongly exitless
path is `φ(c⃗,v⃗)` for some pointed sequence of 1-cycles.  [PROVED — as
`Hunter.Proved.clm_phi_necessity_amended` in `Hunter/ProofsExitless.lean`].

**AMENDED from paper: added guard `1 ≤ k`.**  The unguarded statement is *false at `k = 0`*:
the single vertex `[] : Vtx 0` is `StronglyExitless` (its only vertex is fixed by `σ`), yet
`IsPhiForm` forces `p.verts` to be a `flatten` of length-`k = 0` blocks, i.e. `= []`, while
`p.verts = [[]] ≠ []`.  The exitless-track proof (`clm_phi_necessity_amended`) closes it for
`1 ≤ k`; the paper's data concerns `k ≥ 3`. See `AMBIGUITIES.md` §"Integration-stage
amendments".

Original (unamended, false at `k = 0`) statement, preserved for the record:
```
theorem clm_phi_necessity {k : ℕ} {p : HPath k} (hp : p.StronglyExitless) :
    IsPhiForm p := sorry
```
-/
theorem clm_phi_necessity {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    IsPhiForm p :=
  Proved.clm_phi_necessity_amended hk hp

/-- **clm-phi (sufficiency)** — `main_version.tex` §6 l.523, ⟸.  Every `φ(c⃗,v⃗)` is a
strongly exitless path.  The paper's proof body said `\edit{to complete}` (`DIGEST.md`
§5.1(6)); now proved.

**WIRED** to `Hunter.Proved.clm_phi_sufficiency` (`Hunter/ProofsPhi.lean`) — **verbatim** to
the paper, no guard (at `k = 0`, `IsPhiForm p` forces `p.verts = []`, contradicting `p.ne`,
so that case is vacuous). -/
theorem clm_phi_sufficiency {k : ℕ} {p : HPath k} (hp : IsPhiForm p) :
    p.StronglyExitless :=
  Proved.clm_phi_sufficiency hp

/-! ## §"Getting Bounds" (§6.2) — reducing to subproblems -/

/-- **prp-gives-b2** — `gives b2`, `main_version.tex` §6.2 l.541 / take23 l.654.  For
`X ∈ 𝒳_k`:
`(|Comps(X)|−1) + MinThrough(X) + w(X) ≥ R_k·k! + min_{p*∈Comps(X)}{ w(p*) − R_k|p*| }`.
[PROVED] — prp-Xk-se + MinThrough expansion + def `R_k` (take23's clean proof).  Over `ℝ`;
the inner `min` is `sInf` over the path-components of `X`.

**WIRED** to `Hunter.Proved.prp_gives_b2_amended` (`Hunter/ProofsGB2.lean`).  **AMENDED from
paper: added guard `2 ≤ k`** (needs prp-Xk-se).  See `AMBIGUITIES.md`
§"Final-integration amendments". -/
theorem prp_gives_b2 {k : ℕ} {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k) (hX : X ∈ Xk k) :
    ((numComps X : ℝ) - 1) + (MinThrough X : ℝ) + (wEdges X : ℝ)
      ≥ Rk k * (k.factorial : ℝ)
        + sInf {q : ℝ | ∃ p, IsPathComponent p X ∧
            q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)} :=
  Proved.prp_gives_b2_amended hk hX

/-- **prp-Xkcomps** — `Xk comps`, `main_version.tex` §6.2 l.614.  `𝒳'_k` is exactly the set
of **all** strongly exitless paths of `𝒮_k`.  Main's proof was "WIP" and take23 deleted the
statement while still referencing it (`DIGEST.md` §5.2(b2)); now closed (the `⊇` direction is
the "reverse unwinding" `hrev`, discharged in `Hunter/ProofsHrev.lean`).

**WIRED** to `Hunter.Proved.prp_Xkcomps_closed` (`Hunter/ProofsHrev.lean`).  **AMENDED from
paper/scaffold: added guard `2 ≤ k`** (inherited from `prp_Xk_se`; degenerate for `k ≤ 1`).
See `AMBIGUITIES.md` §"Final-consolidation amendments".

Original (unamended) statement, preserved for the record:
```
theorem prp_Xkcomps {k : ℕ} : Xk' k = {p : HPath k | p.StronglyExitless} := sorry
```
-/
theorem prp_Xkcomps {k : ℕ} (hk : 2 ≤ k) : Xk' k = {p : HPath k | p.StronglyExitless} :=
  Proved.prp_Xkcomps_closed hk

/-! ## §"Getting Bounds" (§6.3) — reducing the subproblems (take23's `≥` forms) -/

/-- **red-p\*** — `Reduction`, take23 l.736 (`≥`; main l.640 over-claims `=`).  For any
`r > 1`:
`min_{p*∈𝒳'_k}{ w(p*) − r|p*| } ≥ min_ℓ{ i_k(ℓ) − r·ℓ }`.  [PROVED in `≥` form] — def of
`i_k`.  The RHS `min` ranges over `ℓ` **in the support of `i_k`** (`HasExitlessPath` guard),
per the `i_k = 0`-on-empty convention.

**WIRED** to `Hunter.Proved.red_pstar_closed` (`Hunter/ProofsHrev.lean`).  **AMENDED from
paper/scaffold: added guard `2 ≤ k`** (needs `prp_Xkcomps` and `𝒳'_k` nonemptiness, both
`k ≥ 2`).  See `AMBIGUITIES.md` §"Final-consolidation amendments".

Original (unamended) statement, preserved for the record:
```
theorem red_pstar {k : ℕ} {r : ℝ} (hr : 1 < r) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} := sorry
```
-/
theorem red_pstar {k : ℕ} {r : ℝ} (hr : 1 < r) (hk : 2 ≤ k) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
  Proved.red_pstar_closed hr hk

/-- **red-R** — `Reduction`, take23 l.744 (`≥`; main l.650 over-claims `=`).
`R_k ≥ min_{ℓ>k}{ (i_k(ℓ)−(k−1)+1)/(ℓ−k) } = min_{ℓ>k}{ (i_k(ℓ)−k+2)/(ℓ−k) }`.
[PROVED in `≥` form] — via the extension `p_u := σ^{−(k−1)}(u),…,σ⁻¹(u),u,p[1],…` with
`|p_u| = |p|+k`, `w(p_u) = w(p)+(k−1)+w(u→p[1])`.  RHS `min` guarded to `ℓ > k` in the
support of `i_k`.

**WIRED** to `Hunter.Proved.red_R_closed` (`Hunter/ProofsHrev.lean`).  **AMENDED from
paper/scaffold: added guard `3 ≤ k`** (genuinely needed: the non-spanning strongly-exitless
component witnessing the reduction is a single 1-cycle `orbitPath u` with `|orbitPath u| = k`,
and `k ≤ k!−k` fails for `k ≤ 2` — for `k ≤ 2` there is only one 1-cycle, so every strongly
exitless component is spanning).  See `AMBIGUITIES.md` §"Final-consolidation amendments".

Original (unamended) statement, preserved for the record:
```
theorem red_R {k : ℕ} :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} := sorry
```
-/
theorem red_R {k : ℕ} (hk : 3 ≤ k) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} :=
  Proved.red_R_closed hk

/-! ## §"Solving the reduction" (§6.4) -/

/-- **greedy-g** — `main_version.tex` §6.4 l.681.  The greedy path `g_ℓ` realizes `j_k`:
for `0 < ℓ ≤ k(k−1)(k−2)` there is an exitless path with `ℓ` vertices and weight `j_k(ℓ)`
(giving the upper bound `i_k(ℓ) ≤ j_k(ℓ)`).  [PROVED — `ProofsGreedy2`: explicit
two-level construction, full base region, cross-loop distinctness via `marker_pins`].
Stated as existence rather than constructing `g_ℓ`. -/
theorem greedy_g {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) :
    ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ ∧ p.wtP = j k ℓ := Hunter.Proved.greedy_g hk hℓ0 hℓ

/-- **j-at-pivot** — display fact, `DIGEST.md` §2.9 / `main_version.tex` §6.4.
`j_k(k(k−1)(k−2)) = k²(k−2) − 3`.  [PROVED — arithmetic on `j_k`'s base formula]. -/
theorem j_at_pivot {k : ℕ} (hk : 3 ≤ k) :
    j k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 :=
  Proved.j_at_pivot hk

/-- **prop1** — `claim 1`, `main_version.tex` §6.4 l.734.  Over `k < ℓ ≤ k(k−1)(k−2)`, the
subproblem-1 ratio `(j_k(ℓ)−k+2)/(ℓ−k)` is minimized at the right endpoint
`ℓ = k(k−1)(k−2)`.  [ASSERTED — "we simply considered"; Carter's `\dc{of what?}` — minimand
identified from subprob1-comp].  Guard `k < ℓ` (the ratio needs `ℓ > k`). -/
theorem prop1 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h1 : k < ℓ) (h2 : ℓ ≤ k * (k - 1) * (k - 2)) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  Hunter.Proved.prop1 hk h1 h2

/-- **prop2** — `claim 2`, `main_version.tex` §6.4 l.736.  Over each interval
`tℓ₀+k < ℓ ≤ (t+1)ℓ₀+k` (`t ≥ 1`), the ratio `(j_k(ℓ)−k+2)/(ℓ−k)` is minimized at the right
endpoint `ℓ = (t+1)ℓ₀+k`.  [PROVED via the explicit `Δ(ℓ')` computation]. -/
theorem prop2 {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ} (ht : 1 ≤ t)
    (h1 : t * ell0 k + k < ℓ) (h2 : ℓ ≤ (t + 1) * ell0 k + k) :
    ((j k ((t + 1) * ell0 k + k) : ℝ) - (k : ℝ) + 2) /
        ((((t + 1) * ell0 k + k : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  Proved.prop2 hk ht h1 h2

/-- **prop3** — `main_version.tex` §6.4 l.738.  All intervals share the same optimal value,
so (evaluating with `j_k`) the global optimum of the ratio over all `ℓ > k` is at
`ℓ = k(k−1)(k−2)`.  [ASSERTED — "readily seen using induction"]. -/
theorem prop3 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) :
    ((j k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  Proved.prop3 hk h

/-- **prop4** — `main_version.tex` §6.4 l.740.  Since `j_k = i_k` on `(0,k(k−1)(k−2)]`
(thm2-equality), the optimum for `i_k` is also at `ℓ = k(k−1)(k−2)`: the ratio
`(i_k(ℓ)−k+2)/(ℓ−k)` over `ℓ > k` is minimized there.  [ASSERTED] — needs thm2 (both
bounds).  Existence-guarded on `ℓ` and on the pivot.  [**PROVED — UNCONDITIONAL**]: with
thm2 proved, both directions are available.  **WIRED** to
`Hunter.ProofsHeadline.prop4_closed` (`prop3` + `thm2_unconditional` + `thm2_equality`). -/
theorem prop4 {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ) (hex : HasExitlessPath k ℓ)
    (hpivot : HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  ProofsHeadline.prop4_closed hk h hex hpivot

/-- **subprob1-comp** — `main_version.tex` §6.4 l.792.  The explicit decomposition of the
subproblem-1 ratio (with `ℓ' = ℓ − tℓ₀`, `r₂ = (ℓ' mod k)/k`, `r₃ = (ℓ' mod k(k−1))/(k(k−1))`):
`(j_k(ℓ)−k+2)/(ℓ−k) = (1 + 1/k + 1/(k(k−1))) + (t+1)/((k−1)(ℓ−k)) + (r₂+r₃)/(ℓ−k)`.
[PROVED].  Stated under the hypotheses pinning `ℓ'` to the base interval and the recursion
unfolding `j_k(ℓ) = t(j_k(ℓ₀)+3) + j_k(ℓ')` (interpretation-heavy: the ℓ-dependent
auxiliaries `t, ℓ', r₂, r₃` are the paper's, left semi-informal there).

**AMENDED from paper: corrected the remainder term** (`Hunter/PROGRESS-reductions.md`,
"STATEMENT DISCREPANCIES").  With `ℓ' = ℓ − tℓ₀`, unfolding `j_k(ℓ)` via `hjrec` and the base
formula produces the *ceiling* remainders `⌈ℓ'/d⌉ − ℓ'/d`.  The identity is
`⌈ℓ'/d⌉ − ℓ'/d = ((d − ℓ' mod d) mod d)/d`, **not** `(ℓ' mod d)/d` (these agree only when
`d ∣ ℓ'`).  So each `(ℓ' mod d)/d` is replaced by `((d − ℓ' mod d) mod d)/d` for
`d ∈ {k, k(k−1)}`.  See `AMBIGUITIES.md` §"Integration-stage amendments".

**WIRED** (final consolidation) to `Hunter.Proved.subprob1_comp` (`Hunter/ProofsPu.lean`) —
the corrected-remainder identity, proved by real arithmetic on the `j`-recursion unfolding.
(This supersedes the earlier note that no proof term existed.)

Original (paper-as-stated, false for generic `ℓ'`) remainder term, preserved for the record:
```
        + ((((ℓ - t * ell0 k) % k : ℕ) : ℝ) / (k : ℝ)
            + (((ℓ - t * ell0 k) % (k * (k - 1)) : ℕ) : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)))
          / ((ℓ : ℝ) - (k : ℝ))
```
-/
theorem subprob1_comp {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ}
    (hle : t * ell0 k ≤ ℓ) (hklt : k < ℓ)
    (hℓ'1 : k < ℓ - t * ell0 k) (hℓ'2 : ℓ - t * ell0 k ≤ k * (k - 1) * (k - 2))
    (hjrec : j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k)) :
    ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))
      = (1 + 1 / (k : ℝ) + 1 / ((k : ℝ) * ((k : ℝ) - 1)))
        + ((t : ℝ) + 1) / (((k : ℝ) - 1) * ((ℓ : ℝ) - (k : ℝ)))
        + ((((k - (ℓ - t * ell0 k) % k) % k : ℕ) : ℝ) / (k : ℝ)
            + (((k * (k - 1) - (ℓ - t * ell0 k) % (k * (k - 1))) % (k * (k - 1)) : ℕ) : ℝ)
                / ((k : ℝ) * ((k : ℝ) - 1)))
          / ((ℓ : ℝ) - (k : ℝ)) :=
  Proved.subprob1_comp hk hle hklt hℓ'1 hℓ'2 hjrec

/-- **subprob2-comp** — `main_version.tex` §6.4 l.802.  The subproblem-2 quantity splits
as (with `ℓ' = ℓ − tℓ₀`):
`j_k(ℓ) − R·ℓ = (t(j_k(ℓ₀)+3) − R·tℓ₀) + (j_k(ℓ') − R·ℓ')`, reducing minimization to
subproblem 1.  [PROVED].  Stated under `t·ℓ₀ ≤ ℓ` and the recursion unfolding of `j_k`. -/
theorem subprob2_comp {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ} (R : ℝ) (hle : t * ell0 k ≤ ℓ)
    (hjrec : j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k)) :
    (j k ℓ : ℝ) - R * (ℓ : ℝ)
      = ((t : ℝ) * ((j k (ell0 k) : ℝ) + 3) - R * (t : ℝ) * (ell0 k : ℝ))
        + ((j k (ℓ - t * ell0 k) : ℝ) - R * (((ℓ - t * ell0 k : ℕ) : ℝ))) :=
  Hunter.Proved.subprob2_comp hk R hle hjrec

/-- **proof-thm1v2** — `main_version.tex` §6.4 l.821.  Combining the two subproblems at
`ℓ₁ = ℓ₂ = k(k−1)(k−2)`:
`L(k) ≥ i_k(ℓ₂) + ((i_k(ℓ₁)−k+2)/(ℓ₁−k))·(k!−ℓ₂)`,
which evaluates to `(1 + 1/k + 1/(k(k−1)) + 1/((k−1)(k(k−1)(k−2)−k)))·k! + O(1)`.  [**PROVED —
UNCONDITIONAL**].  **WIRED** to `Hunter.ProofsHeadline.proof_thm1v2_all`: the concrete inner
min `gInner k r_P = min_{p*∈𝒳'_k}{w(p*) − r_P|p*|}` is bounded below by `i_k(P) − r_P·P` via
`prp_Xkcomps` + `prop4` (case `|p*| > k`) and the trivial edge bound (case `|p*| = k`), then
combined with `b2_gInner` and `gInner_mono`.  Axiom-clean. -/
theorem proof_thm1v2 {k : ℕ} (hk : 3 ≤ k)
    (hpivot : HasExitlessPath k (k * (k - 1) * (k - 2))) :
    (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
      + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
          (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
        * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)) :=
  ProofsHeadline.proof_thm1v2_all k hk hpivot

/-! ## §"Further Comments" (§7) — forward-looking, NOT used in thm1 -/

/-! ### `imp_reduced` — supporting development (`ImpRed`)

The §7 "reduced path" remark is proved here by an explicit list surgery (Egan's 2-opt-style
reroute): the triangle-equality vertex `v'` is deleted from its position and re-inserted
between `v` and `v''`.  Deletion never increases the weight (`pathW_splice`, via the overlap
**triangle inequality** `ew_triangle`, proved from `wt_spec`'s overlap characterization);
insertion is weight-*preserving* by the triangle *equality* `htri` (`pathW_insert_eq`); the
result is a permutation of `P`'s vertices (hence Hamiltonian and `Nodup`), and the edge
`(v,v'')` is gone because `v`'s new (unique, out-degree ≤ 1) successor is `v' ≠ v''`. -/
namespace ImpRed

variable {k : ℕ}

/-- The path weight of a raw vertex list (`= wtP` on `p.verts`). -/
noncomputable def pathW (l : List (Vtx k)) : ℕ := (l.zipWith (ew k) l.tail).sum

@[simp] theorem pathW_nil : pathW ([] : List (Vtx k)) = 0 := by simp [pathW]

@[simp] theorem pathW_single (a : Vtx k) : pathW [a] = 0 := by simp [pathW]

theorem pathW_cons2 (a b : Vtx k) (t : List (Vtx k)) :
    pathW (a :: b :: t) = ew k a b + pathW (b :: t) := by
  simp only [pathW, List.tail_cons, List.zipWith_cons_cons, List.sum_cons]

/-- The master append/junction lemma: splitting the weight at a marked vertex `x`. -/
theorem pathW_append_cons (l : List (Vtx k)) (x : Vtx k) (m : List (Vtx k)) :
    pathW (l ++ x :: m) = pathW (l ++ [x]) + pathW (x :: m) := by
  induction l with
  | nil => simp
  | cons a l' ih =>
    cases l' with
    | nil =>
      show pathW (a :: x :: m) = pathW (a :: x :: []) + pathW (x :: m)
      rw [pathW_cons2, pathW_cons2, pathW_single]; omega
    | cons b l'' =>
      show pathW (a :: b :: (l'' ++ x :: m)) = pathW (a :: b :: (l'' ++ [x])) + pathW (x :: m)
      rw [pathW_cons2, pathW_cons2]
      show ew k a b + pathW ((b :: l'') ++ x :: m)
         = ew k a b + pathW ((b :: l'') ++ [x]) + pathW (x :: m)
      rw [ih]; omega

/-- The overlap edge weight is subadditive (triangle inequality), for `1 ≤ k`. -/
theorem ew_triangle (hk : 1 ≤ k) (u v w : Vtx k) :
    ew k u w ≤ ew k u v + ew k v w := by
  have hu : u.1.length = k := u.2.length
  have hv : v.1.length = k := v.2.length
  obtain ⟨h1a, _h1b, h1c⟩ := wt_spec (u := u.1) (v := v.1) hk (le_of_eq hu)
  obtain ⟨_h2a, _h2b, h2c⟩ := wt_spec (u := v.1) (v := w.1) hk (le_of_eq hv)
  show wt k u.1 w.1 ≤ wt k u.1 v.1 + wt k v.1 w.1
  set d1 := wt k u.1 v.1 with hd1
  set d2 := wt k v.1 w.1 with hd2
  by_cases hsum : d1 + d2 ≤ k
  · apply wt_le (by omega) hsum
    calc u.1.drop (d1 + d2)
        = (u.1.drop d1).drop d2 := by rw [← List.drop_drop]
      _ = (v.1.take (k - d1)).drop d2 := by rw [h1c]
      _ = (v.1.drop d2).take ((k - d1) - d2) := by rw [List.drop_take]
      _ = (w.1.take (k - d2)).take ((k - d1) - d2) := by rw [h2c]
      _ = w.1.take (min ((k - d1) - d2) (k - d2)) := by rw [List.take_take]
      _ = w.1.take (k - (d1 + d2)) := by congr 1; omega
  · have hle := (wt_spec (u := u.1) (v := w.1) hk (le_of_eq hu)).2.1
    omega

/-- Removing a vertex `b` from between `p` and `s` does not increase the path weight. -/
theorem pathW_splice (p s : List (Vtx k)) (b : Vtx k) (hk : 1 ≤ k) :
    pathW (p ++ s) ≤ pathW (p ++ b :: s) := by
  induction p with
  | nil =>
    cases s with
    | nil => simp
    | cons d s' => simp only [List.nil_append, pathW_cons2]; omega
  | cons c p' ih =>
    cases p' with
    | nil =>
      simp only [List.cons_append, List.nil_append]
      cases s with
      | nil => simp only [pathW_cons2, pathW_single]; omega
      | cons d s' =>
        simp only [pathW_cons2]
        have htri := ew_triangle hk c b d
        omega
    | cons e p'' =>
      simp only [List.cons_append, pathW_cons2] at ih ⊢
      omega

/-- Inserting `v'` between `v` and `v''` preserves the path weight, given the triangle
equality `w(v→v'') = w(v→v') + w(v'→v'')`. -/
theorem pathW_insert_eq {v v' v'' : Vtx k}
    (htri : ew k v v'' = ew k v v' + ew k v' v'') (pre suf : List (Vtx k)) :
    pathW (pre ++ v :: v' :: v'' :: suf) = pathW (pre ++ v :: v'' :: suf) := by
  rw [pathW_append_cons pre v (v' :: v'' :: suf),
      pathW_append_cons pre v (v'' :: suf),
      pathW_cons2 v v' (v'' :: suf), pathW_cons2 v' v'' suf,
      pathW_cons2 v v'' suf]
  omega

/-- An edge `(a,b)` of a path splits its vertex list as `A ++ a :: b :: B`. -/
theorem zip_tail_split : ∀ {L : List (Vtx k)} {a b : Vtx k},
    (a, b) ∈ L.zip L.tail → ∃ A B, L = A ++ a :: b :: B
  | [], _a, _b, h => by simp at h
  | [_c], _a, _b, h => by simp at h
  | c :: d :: t, a, b, h => by
      rw [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], t, rfl⟩
      · have h' : (a, b) ∈ (d :: t).zip (d :: t).tail := by rwa [List.tail_cons]
        obtain ⟨A', B', hAB⟩ := zip_tail_split h'
        exact ⟨c :: A', B', by rw [List.cons_append, ← hAB]⟩

/-- Reverse direction: consecutive `a :: b` in the vertex list gives an edge (as a zip pair). -/
theorem append_mem_zip_tail : ∀ (C : List (Vtx k)) (a b : Vtx k) (D : List (Vtx k)),
    (a, b) ∈ (C ++ a :: b :: D).zip (C ++ a :: b :: D).tail
  | [], a, b, D => by
      rw [List.nil_append, List.tail_cons, List.zip_cons_cons]; simp
  | c :: C', a, b, D => by
      have ih := append_mem_zip_tail C' a b D
      obtain ⟨m0, M', hM⟩ := List.exists_cons_of_ne_nil
        (show C' ++ a :: b :: D ≠ [] by simp)
      rw [List.cons_append, List.tail_cons, hM, List.zip_cons_cons, List.mem_cons]
      right
      rwa [hM, List.tail_cons] at ih

/-- If `q.verts = C ++ a :: b :: D` then `(a,b)` is an edge of `q`. -/
theorem mem_edges_of_split {q : HPath k} {C D : List (Vtx k)} {a b : Vtx k}
    (hq : q.verts = C ++ a :: b :: D) : (a, b) ∈ q.edges := by
  rw [ProofsSpine.mem_edges_iff, hq]
  exact append_mem_zip_tail C a b D

/-- Core surgery: given `P.verts = p ++ v' :: s` and the "deleted" list `p ++ s` presented as
`pre ++ v :: v'' :: suf`, insert `v'` between `v` and `v''` to obtain the required `P'`. -/
theorem assemble (hk : 1 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    {v v' v'' : Vtx k} (htri : ew k v v'' = ew k v v' + ew k v' v'')
    (hv'nev'' : v' ≠ v'')
    {p s pre suf : List (Vtx k)}
    (hLdef : P.verts = p ++ v' :: s)
    (hMeq : p ++ s = pre ++ v :: v'' :: suf) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧ (v, v'') ∉ P'.edges ∧ P'.wtP ≤ P.wtP := by
  have hne : pre ++ v :: v' :: v'' :: suf ≠ [] :=
    List.ne_nil_of_mem (a := v) (by simp)
  have hperm1 : P.verts ~ v' :: (p ++ s) := by rw [hLdef]; exact List.perm_middle
  have hperm2 : (pre ++ v :: v' :: v'' :: suf) ~ v' :: (p ++ s) := by
    have hrw : pre ++ v :: v' :: v'' :: suf = (pre ++ [v]) ++ v' :: (v'' :: suf) := by simp
    have heq : (pre ++ [v]) ++ (v'' :: suf) = p ++ s := by rw [hMeq]; simp
    rw [hrw]
    calc (pre ++ [v]) ++ v' :: (v'' :: suf)
        ~ v' :: ((pre ++ [v]) ++ (v'' :: suf)) := List.perm_middle
      _ = v' :: (p ++ s) := by rw [heq]
  have hPL' : P.verts ~ (pre ++ v :: v' :: v'' :: suf) := hperm1.trans hperm2.symm
  have hnodup : (pre ++ v :: v' :: v'' :: suf).Nodup := hPL'.nodup P.nodup
  refine ⟨⟨pre ++ v :: v' :: v'' :: suf, hne, hnodup⟩, ?_, ?_, ?_⟩
  · intro u; exact hPL'.mem_iff.mp (hP u)
  · intro hcontra
    have hvv' : (v, v') ∈ (⟨pre ++ v :: v' :: v'' :: suf, hne, hnodup⟩ : HPath k).edges :=
      mem_edges_of_split (C := pre) (D := v'' :: suf) rfl
    have hsub : ({(v, v'), (v, v'')} : Finset (Vtx k × Vtx k)) ⊆
        outV (⟨pre ++ v :: v' :: v'' :: suf, hne, hnodup⟩ : HPath k).edges v := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · rw [outV, mem_out]; exact ⟨hvv', Finset.mem_singleton_self v⟩
      · rw [outV, mem_out]; exact ⟨hcontra, Finset.mem_singleton_self v⟩
    have hpair : ((v, v') : Vtx k × Vtx k) ≠ (v, v'') := by simp [hv'nev'']
    have hle := ProofsSpine.path_out_le_one
      (⟨pre ++ v :: v' :: v'' :: suf, hne, hnodup⟩ : HPath k) v
    have h2le : 2 ≤
        (outV (⟨pre ++ v :: v' :: v'' :: suf, hne, hnodup⟩ : HPath k).edges v).card := by
      calc 2 = ({(v, v'), (v, v'')} : Finset (Vtx k × Vtx k)).card :=
              (Finset.card_pair hpair).symm
        _ ≤ _ := Finset.card_le_card hsub
    omega
  · show pathW (pre ++ v :: v' :: v'' :: suf) ≤ P.wtP
    have e1 : pathW (pre ++ v :: v' :: v'' :: suf) = pathW (p ++ s) := by
      rw [pathW_insert_eq htri pre suf, ← hMeq]
    have e3 : P.wtP = pathW (p ++ v' :: s) := by
      change pathW P.verts = _; rw [hLdef]
    rw [e1, e3]
    exact pathW_splice p s v' hk

/-- The exact statement of `imp_reduced` (proved). -/
theorem imp_reduced_proof {P : HPath k} (hP : P.IsHamiltonian) {v v' v'' : Vtx k}
    (htri : ew k v v'' = ew k v v' + ew k v' v'') (hedge : (v, v'') ∈ P.edges) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧ (v, v'') ∉ P'.edges ∧ P'.wtP ≤ P.wtP := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rw [ProofsSpine.edges_eq_empty_zero P] at hedge
    exact absurd hedge (Finset.notMem_empty _)
  have ew_pos : ∀ (x y : Vtx k), 1 ≤ ew k x y := fun x y => by
    rw [ew]; exact (wt_spec hk (le_of_eq x.2.length)).1
  have hv'nev : v' ≠ v := by
    rintro rfl; have := ew_pos v' v'; omega
  have hv'nev'' : v' ≠ v'' := by
    rintro rfl; have := ew_pos v' v'; omega
  have hzip : (v, v'') ∈ P.verts.zip P.verts.tail := ProofsSpine.mem_edges_iff.mp hedge
  obtain ⟨A, B, hAB⟩ := zip_tail_split hzip
  have hv'mem : v' ∈ P.verts := hP v'
  rw [hAB, List.mem_append, List.mem_cons, List.mem_cons] at hv'mem
  rcases hv'mem with hv'A | hv'eqv | hv'eqv'' | hv'B
  · obtain ⟨A1, A2, hA⟩ := List.mem_iff_append.mp hv'A
    refine assemble hk hP htri hv'nev'' (p := A1) (s := A2 ++ v :: v'' :: B)
      (pre := A1 ++ A2) (suf := B) ?_ ?_
    · rw [hAB, hA]; simp
    · simp
  · exact absurd hv'eqv hv'nev
  · exact absurd hv'eqv'' hv'nev''
  · obtain ⟨B1, B2, hB⟩ := List.mem_iff_append.mp hv'B
    refine assemble hk hP htri hv'nev'' (p := A ++ v :: v'' :: B1) (s := B2)
      (pre := A) (suf := B1 ++ B2) ?_ ?_
    · rw [hAB, hB]; simp
    · simp

end ImpRed

/-- **imp-reduced** — `Remark`, `main_version.tex` §7 l.862.  The triangle-equality "reduced
path" remark (Egan-relevant): if `w(v→v'') = w(v→v') + w(v'→v'')` and `(v→v'') ∈ E(P)`,
there is a Hamiltonian `P'` without that edge with `w(P') ≤ w(P)`.  Iterating removes all
`σ^i` (`i>1`) edges (a "reduced" `P`).  [PROVED] — via the `ImpRed` surgery above (delete `v'`,
re-insert between `v` and `v''`); axiom-clean.  (Formerly [SKETCH]/`sorry`.) -/
theorem imp_reduced {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {v v' v'' : Vtx k}
    (htri : ew k v v'' = ew k v v' + ew k v' v'') (hedge : (v, v'') ∈ P.edges) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧ (v, v'') ∉ P'.edges ∧ P'.wtP ≤ P.wtP :=
  ImpRed.imp_reduced_proof hP htri hedge

/-! ## Appendix (proof of thm2) — auxiliary facts the digest flags -/

/-- **prp-periodicedges** — `main_version.tex` appendix l.989.  For an exitless path `p`,
edge `(p[t]→p[t+1])` has weight 1 iff `k ∤ t` — the backbone fact (weight-1 edges are
exactly within-1-cycle steps). [**DRAFT GAP — PROVED HERE**]. 0-based indexing: the edge
`vert i → vert (i+1)` is the paper's `t = i+1`, so `w = 1 ⟺ k ∤ (i+1)` (off-by-one per
`AMBIGUITIES.md` §B2). -/
theorem prp_periodicedges {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {i : ℕ} (hi : i + 1 < p.numVerts) :
    ew k (p.vert i) (p.vert (i + 1)) = 1 ↔ ¬ (k ∣ (i + 1)) :=
  Proved.prp_periodicedges hk hp hi

/-- **prp-1edgebound** — `main_version.tex` appendix l.993.  An exitless path of length `ℓ`
has `ℓ−1` `1+`-edges (trivially: all `ℓ−1` edges have weight ≥ 1).  [PROVED]. -/
theorem prp_1edgebound {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 1 = p.numVerts - 1 :=
  Proved.prp_1edgebound hk hp

/-- **prp-2edgebound** — `main_version.tex` appendix l.997.  An exitless path of length `ℓ`
has exactly `⌈ℓ/k⌉−1` `2+`-edges.  [PROVED from prp-periodicedges]. -/
theorem prp_2edgebound {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 2 = p.numVerts ⌈/⌉ k - 1 :=
  Proved.prp_2edgebound hk hp

/-- **prp-3edgebound** — `main_version.tex` appendix l.1001.  An exitless path of length `ℓ`
has `≥ ⌈ℓ/(k(k−1))⌉−1` `3+`-edges — the "can't stay in a 2-cycle forever" fact, source of
the exact value `i(k(k−1)(k−2)) = k²(k−2)−3` and the `1/(k(k−1))` term.
[**DRAFT GAP — PROVED HERE**; see `DIGEST.md` §5.4(2)]. -/
theorem prp_3edgebound {k : ℕ} (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 3 ≥ p.numVerts ⌈/⌉ (k * (k - 1)) - 1 :=
  Proved.prp_3edgebound hk hp

/-! ## Scaffolding (a): the conditional main theorem — spine modulo the appendix -/

/-- **thm2 → thm1v2** (conditional main theorem).  Assuming Theorem 2 (both the lower bound
and the equality-on-small-`ℓ`), the paper's §4–§6 spine yields `thm1v2`.  This is the
paper's real contribution modulo the unwritten appendix (`DIGEST.md` §6.4 strategy: prove
`thm1v2` conditional on thm2, then attack thm2 separately).  [**PROVED — UNCONDITIONAL**]: the
conclusion is now `thm1v2` itself, closed outright (`ProofsHeadline.thm1v2_unconditional`), so
the two Theorem-2 hypotheses `hthm2`/`hthm2eq` are no longer needed (kept for the paper's
statement shape). -/
theorem thm2_imp_thm1v2
    (_hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (_hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsHeadline.thm1v2_unconditional

/-! ## Scaffolding (b): bridge facts (theorems, not definitions — `AMBIGUITIES.md` §Z5) -/

/-- **bridge: StronglyExitless ↔ IsUnionOfCycles** — the two recorded characterizations of
"strongly exitless" agree.  `⟹` is clm-1cyclesubset; `⟸` reassembles
`StronglyExitless = Exitless ∧ σ(last) ∈ V(p)` from `IsUnionOfCycles` and `Exitless`.

**WIRED** to `Hunter.Proved.bridge_stronglyExitless_iff_unionOfCycles`
(`Hunter/ProofsPhi.lean`).  **AMENDED from scaffold: added guard `p.Exitless`.**  The
unguarded iff (the original scaffold form below) is **FALSE**: `IsUnionOfCycles` constrains
only the vertex *set*, not the traversal order, so a path may be a union of full 1-cycles yet
step out of a 1-cycle mid-traversal (explicit counterexample at `k = 3`; see the `ProofsPhi`
module docstring).  Under `p.Exitless` the equivalence holds.  See `AMBIGUITIES.md`
§"Final-consolidation amendments".

Original (scaffold-as-stated, **false** without the guard), preserved for the record:
```
theorem bridge_stronglyExitless_iff_unionOfCycles {k : ℕ} (p : HPath k) :
    p.StronglyExitless ↔ p.IsUnionOfCycles := sorry
```
-/
theorem bridge_stronglyExitless_iff_unionOfCycles {k : ℕ} {p : HPath k} (hexit : p.Exitless) :
    p.StronglyExitless ↔ p.IsUnionOfCycles :=
  Proved.bridge_stronglyExitless_iff_unionOfCycles hexit

/-- **bridge: compMinto agrees with minto** — on a path-component, the component-level
`compMinto` equals the path's `minto`.  (`AMBIGUITIES.md` §C4.) -/
theorem bridge_compMinto_eq_minto {k : ℕ} {p : HPath k} {X : Finset (Vtx k × Vtx k)}
    (hp : IsPathComponent p X) : compMinto X p.vertsFinset = p.minto :=
  Proved.bridge_compMinto_eq_minto hp

/-- **bridge: L\*(k) = L(k) + k** — the library's `Lstar := L + k` equals the direct
superpermutation minimum `Ssuper` (Hunter's `L*(k) = k + L(k)`).  (`AMBIGUITIES.md` §E1.)

**WIRED** to `Hunter.Proved.bridge_Lstar_eq_Ssuper` (`Hunter/ProofsLstar.lean`) — verbatim
(the `1 ≤ k` guard was already present in the scaffold). -/
theorem bridge_Lstar_eq_Ssuper {k : ℕ} (hk : 1 ≤ k) : Lstar k = Ssuper k :=
  Proved.bridge_Lstar_eq_Ssuper hk

/-- **bridge: w(E(p)) = w(p)** — the edge-set weight of a path's edges equals its path
weight.  (`AMBIGUITIES.md` §Z5.) -/
theorem bridge_wEdges_edges_eq_wtP {k : ℕ} (p : HPath k) : wEdges p.edges = p.wtP :=
  Proved.bridge_wEdges_edges_eq_wtP p

/-!
## Audit summary

**57 theorems** total (53 skeleton items + 4 coverage theorems `thm2_small`, `thm2_upto`,
`thm2_equality_le_kk`, `greedy_g_le_kk`), all proved, wired to the proof tree, and
axiom-clean (`[propext, Classical.choice, Quot.sound]`); `sorry` count = 0.  Theorem 2 is
`Hunter.Proved.thm2_unconditional` (the rigidity/chart route); the headline forms `thm1v1`,
`thm1v2`, `eq_weak` are wired to `ProofsHeadline.*_unconditional`; `imp_reduced` (the §7
remark, not used on the thm1 path) is proved by the `ImpRed` module above.

**The headline superpermutation lower bound `L(k) ≥ coeff(k)·k! − O(1)` (and its `L*` form
`thm1v1`) is formally closed, unconditionally, for all `k`.**

This file contains proof *terms* and no `def`s.  See `AxiomCheck.lean` for the executable
axiom audit.
-/

end Hunter

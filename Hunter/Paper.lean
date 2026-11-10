/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Statements
import Hunter.Pointwise
import Hunter.ProofsChart
import Hunter.ProofsChartEq
import Hunter.ProofsClosure3
import Hunter.ProofsRigidity2
import Hunter.ProofsRigid
import Hunter.ProofsInduction
import Hunter.ProofsPotential
import Hunter.ProofsRecursion
import Hunter.ProofsConfinement
import Hunter.ProofsReductions
import Hunter.ProofsHeadline
import Hunter.ProofsPu

/-! # The paper, as a single Lean chain

This file restates the numbered items of `paper/hunter_bound.tex` ("A New Lower Bound for
Superpermutations", Hunter--Raudvere) **in paper order and paper vocabulary**, and proves each
one by wiring it to the research development.  It is the paper-facing façade: reading this
file top to bottom is reading the paper.

Conventions bridging paper and formalization:
* paper `w(u→v)` = `ew k u v`; `σ, τ, α` = `sigma, tau, alpha`; blocks = rotation classes.
* paper `i_k(ℓ)` = `iExitless k ℓ`, **undefined off the support** in the paper; here
  `sInf ∅ = 0`, so every statement carries the support guard `HasExitlessPath k ℓ`.
* paper `j_k` = `j`, `ℓ₀` = `ell0 k`, `q_k` = `coeff k`, `S(k)` = `Ssuper k`, `L(k)` = `L k`.
* paper excess `E` = `ProofsRecursion.excess`, opened blocks `b = ⌈ℓ/k⌉` = `numVerts ⌈/⌉ k`,
  `G(E)` = `ProofsInduction.G k E`, dictionary `D(b)` = `ProofsPotential.Dfr k b`.

Item numbering (`Lemma 1` … `Corollary 28`) follows the revised paper.  Where the paper's
single statement corresponds to several Lean declarations, each clause is stated separately.
Two corollaries at the end (`S(3) ≥ 9`, `S(4) ≥ 33`) are *stated* by the paper but were not
previously exposed by the development; they are proved here.
-/

namespace Hunter.Paper

open scoped Classical
open List
open ProofsRecursion (excess)
open ProofsInduction (G)
open ProofsPotential (Dfr)

/-! ## §2  The overlap graph and exitless paths -/

/-- **Lemma 1 (Overlap successors), weight-1 clause.**  The unique weight-1 successor is the
left rotation `σ`. -/
theorem overlap_weight_one_iff {k : ℕ} (hk : 1 ≤ k) {u v : Vtx k} :
    ew k u v = 1 ↔ v = sigma u :=
  ProofsExitless.ew_eq_one_iff hk

/-- **Lemma 1, weight-2 clause** (word level).  A successor overlapping in all but two
symbols is `σ²(u)` or the door `τ(u)`. -/
theorem overlap_weight_two {k : ℕ} (hk : 2 ≤ k) {u v : List ℕ}
    (hu : IsPermWord k u) (hv : IsPermWord k v) (hover : u.drop 2 = v.take (k - 2)) :
    v = u.rotate 2 ∨ v = door u :=
  ProofsConfinement.wt_two_word_cases hk hu hv hover

/-- **Lemma 1, weight-3 clause** (word level).  A successor of the exit `x = c b z A'`
overlapping in all but three symbols is one of the six arrangements `A' ++ π{z,b,c}` —
the paper's `T₁,…,T₆`. -/
theorem overlap_weight_three {A' : List ℕ} {z b c : ℕ}
    (hx : IsPermWord (A'.length + 3) (ProofsClosure3.finalExit A' z b c))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (ProofsClosure3.finalExit A' z b c).drop 3 = v.take (A'.length + 3 - 3)) :
    v = A' ++ [z, b, c] ∨ v = A' ++ [z, c, b] ∨ v = A' ++ [b, z, c] ∨
      v = A' ++ [b, c, z] ∨ v = A' ++ [c, z, b] ∨ v = A' ++ [c, b, z] :=
  ProofsClosure3.w3_six_cases A' z b c hx hv hover

/-- **Remark 2 (improper `σ²`).**  At a block boundary of an exitless path, a weight-2
continuation is forced to be the door — an exitless path never takes `σ²`. -/
theorem remark_sigma_sq {k : ℕ} (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1))
    (hw : ew k (p.vert i) (p.vert (i + 1)) = 2) :
    (p.vert (i + 1) : List ℕ) = door (p.vert i : List ℕ) :=
  ProofsChart.s1_door_determinism hk hp hi hd hw

/-- **Lemma 4 (Block structure), full-blocks clause.**  A strongly exitless path is a
disjoint union of whole rotation classes. -/
theorem block_structure_cycles {k : ℕ} {p : HPath k} (hp : p.StronglyExitless) :
    p.IsUnionOfCycles :=
  Hunter.clm_1cyclesubset hp

/-- **Lemma 4, length clause.**  `k` divides the vertex count of a strongly exitless path
(`|p| = bk`). -/
theorem block_structure_dvd {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless) :
    k ∣ p.numVerts :=
  Proved.dvd_numVerts_of_stronglyExitless hk hp

/-- **Lemma 4, boundary-position clause.**  In an exitless path the edge `p[t] → p[t+1]`
has weight 1 exactly when `k ∤ t` — the `≥2`-jumps sit exactly at the block boundaries. -/
theorem block_structure_boundaries {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {i : ℕ} (hi : i + 1 < p.numVerts) :
    ew k (p.vert i) (p.vert (i + 1)) = 1 ↔ ¬ (k ∣ (i + 1)) :=
  Hunter.prp_periodicedges hk hp hi

/-- **Proposition 5.**  `S(k) = k + L(k)`: the superpermutation problem is the
minimum-weight Hamiltonian path problem in the overlap graph. -/
theorem S_eq_k_add_L {k : ℕ} (hk : 1 ≤ k) : Ssuper k = L k + k := by
  rw [← Proved.bridge_Lstar_eq_Ssuper hk]; exact lstar_eq k

/-! ## §3  Hunter's transformation and Bounds 1 and 2 -/

/-- **Lemma 6 (Degree rule).**  Every vertex of `X = f(P,S)` has in- and out-degree at
most 1, so `Comp(X)` is a set of directed paths and cycles. -/
theorem degree_rule {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hS : SPrecond P S) :
    ∀ v : Vtx k, (outV (fPS P S) v).card ≤ 1 ∧ (intoV (fPS P S) v).card ≤ 1 :=
  Hunter.clm_degree hS

/-- **Lemma 7 (Boundary sets), heads clause.**  `E₂ = out(P, H(X) ∖ H(P))`. -/
theorem boundary_sets_heads {k : ℕ} {P : HPath k} {S : Finset (Vtx k)}
    (hS : SPrecond P S) :
    E2removed P S = out P.edges (heads (fPS P S) \ heads P.edges) :=
  Hunter.clm_e2 hS

/-- **Lemma 7, tails clause.**  `into(P, T(X) ∖ T(P)) ⊆ E₁`. -/
theorem boundary_sets_tails {k : ℕ} {P : HPath k} {S : Finset (Vtx k)}
    (hS : SPrecond P S) :
    into P.edges (tails (fPS P S) \ tails P.edges) ⊆ E1removed P S :=
  Hunter.clm_e1 hS

/-- **Lemma 8 (Weight rule), exact identity.**
`w(P) = w(X) + Σ_{E₁}(w(e)−1) − I + Σ_{E₂} w(e)`, over `ℤ`. -/
theorem weight_rule_eq {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hk : 1 ≤ k)
    (hSV : S ⊆ P.vertsFinset) (hS : SPrecond P S) :
    (P.wtP : ℤ) = (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ E1removed P S, ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ E2removed P S, (ew k e.1 e.2 : ℤ) :=
  Hunter.clm_eqq hk hSV hS

/-- **Lemma 8, restriction inequality** — the form Bound 1 consumes. -/
theorem weight_rule_ge {k : ℕ} {P : HPath k} {S : Finset (Vtx k)} (hk : 1 ≤ k)
    (hSV : S ⊆ P.vertsFinset) (hS : SPrecond P S) :
    (P.wtP : ℤ) ≥ (wEdges (fPS P S) : ℤ)
      + ∑ e ∈ into P.edges (tails (fPS P S) \ tails P.edges), ((ew k e.1 e.2 : ℤ) - 1)
      - (indicatorI P S : ℤ)
      + ∑ e ∈ out P.edges (heads (fPS P S) \ heads P.edges), (ew k e.1 e.2 : ℤ) :=
  Hunter.lem_weightrule hk hSV hS

/-- **Lemma 9 (Structure of `F(P)`), clause (i).**  Away from block exits, the out-edge is
the 1-edge. -/
theorem structure_F_one_edges {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) {v : Vtx k}
    (hv : v ∉ Cm1 P) :
    outV (F P) v = {(v, sigma v)} :=
  Hunter.clm_rule2 hP hv

/-- **Lemma 9, clause (iii) (Walking rule).**  Walk order in `F(P)` refines `P`-order on
`C₀ ∪ C₋₁`. -/
theorem structure_F_walking {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian)
    {D : List (Vtx k)} (hD : IsWalk (F P) D) {u v : Vtx k}
    (hu : u ∈ C0 P ∪ Cm1 P) (hv : v ∈ C0 P ∪ Cm1 P)
    (huD : u ∈ D) (hvD : v ∈ D) (hlt : D.idxOf u < D.idxOf v) :
    P.pos u < P.pos v :=
  Hunter.lem_walking hP hD hu hv huD hvD hlt

/-- **Lemma 9, clause (iv).**  `Comp(F(P))` is a set of strongly exitless *paths* (no
cycles). -/
theorem structure_F_components {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian) :
    IsUnionOfStronglyExitlessPaths (F P) :=
  Hunter.cor_exitlessrule hP

/-- **Lemma 9, clause (v).**  Each component starts at its first `P`-vertex. -/
theorem structure_F_first {k : ℕ} {P : HPath k} (hP : P.IsHamiltonian)
    {p : HPath k} (hp : IsPathComponent p (F P)) {u : Vtx k} (hu : u ∈ p.verts) :
    P.pos p.first ≤ P.pos u :=
  Hunter.cor_pathfirst hP hp hu

/-- **Lemma 10 (`𝒳_k` = strongly-exitless coverings), necessity.** -/
theorem Xk_characterization_necessity {k : ℕ} {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k)
    (hX : X ∈ Xk k) :
    vertsOf X = Finset.univ ∧ IsUnionOfStronglyExitlessPaths X :=
  Hunter.prp_Xk_se_necessity hk hX

/-- **Lemma 10, sufficiency** — the splice construction. -/
theorem Xk_characterization_sufficiency {k : ℕ} (hk : 2 ≤ k)
    {X : Finset (Vtx k × Vtx k)}
    (hspan : vertsOf X = Finset.univ) (hse : IsUnionOfStronglyExitlessPaths X) :
    X ∈ Xk k :=
  Hunter.prp_Xk_se_sufficiency hk hspan hse

/-- **Lemma 10, component form.**  `𝒳'_k` is exactly the strongly exitless paths. -/
theorem Xk'_eq_stronglyExitless {k : ℕ} (hk : 2 ≤ k) :
    Xk' k = {p : HPath k | p.StronglyExitless} :=
  Hunter.prp_Xkcomps hk

/-- **Theorem 11 (Bound 1).**
`L(k) ≥ min_{X∈𝒳_k} { (|Comp(X)|−1) + MinThrough(X) + w(X) }`. -/
theorem bound1 {k : ℕ} (hk : 2 ≤ k) :
    L k ≥ sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} :=
  Hunter.b1 hk

/-- **Theorem 12 (Bound 2).**
`L(k) ≥ min_{p*∈𝒳'_k} { w(p*) + R_k·(k! − |p*|) }`, over `ℝ`. -/
theorem bound2 {k : ℕ} (hk : 2 ≤ k) :
    (L k : ℝ) ≥ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} :=
  Hunter.b2 hk

/-! ## §4  The reduction to `i_k` and the function `j_k` -/

/-- **Proposition 13 (Reduction of the offset).**  For `r > 1`,
`min_{p*∈𝒳'_k}{w(p*) − r|p*|} ≥ min_{ℓ∈𝒟_k}{i_k(ℓ) − rℓ}`.  (The paper drops the `r > 1`
hypothesis as unused; the wired research lemma retains it, harmlessly.) -/
theorem reduction_offset {k : ℕ} {r : ℝ} (hr : 1 < r) (hk : 2 ≤ k) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
  Hunter.red_pstar hr hk

/-- **Proposition 14 (Reduction of the ratio).**
`R_k ≥ min_{k<ℓ, ℓ∈𝒟_k} (i_k(ℓ) − k + 2)/(ℓ − k)`. -/
theorem reduction_ratio {k : ℕ} (hk : 3 ≤ k) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} :=
  Hunter.red_R hk

/-- **Proposition 14, the `p_u`-extension.**  Prepending the `σ`-orbit of an outside
vertex `u` realizing `minto(p)` extends a strongly exitless `p` to an exitless path of
`|p| + k` vertices and weight `(k−1) + minto(p) + w(p)`. -/
theorem pu_extension {k : ℕ} (hk : 2 ≤ k) {p : HPath k} (hSE : p.StronglyExitless)
    {u : Vtx k} (hu : u ∉ p.verts) (hmin : ew k u p.first = p.minto) :
    ∃ q : HPath k, q.Exitless ∧ q.numVerts = p.numVerts + k ∧
      q.wtP = (k - 1) + p.minto + p.wtP :=
  ProofsPu.pu_exists hk hSE hu hmin

/-! ## §5  The exitless-path inequality (Theorem 2)

The paper's rigidity–closure machinery.  Paper `n = k−1`, `m = k−2`, `N = (k−1)(k−2)`.
The word-level statements below use the paper's normal form: a run start
`s = a₁⋯a_m b c` is `A' ++ [z, b, c]` (with `A' ++ [z]` the `a`-letters), the run exit is
`finalExit A' z b c = c :: b :: z :: A'`, and the chart is
`chartWord A' z b c j i = C_{j,i} = τ₂^i τ₃^j (s)`. -/

/-- **Lemma 15 (Block-locality).**  A block-aligned suffix of an exitless path is
exitless — the truncation license for the excess induction. -/
theorem block_locality_suffix {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {B : ℕ} (hBdvd : k ∣ B) (hBlt : B < p.numVerts) :
    ∃ q : HPath k, q.verts = p.verts.drop B ∧ q.Exitless :=
  ProofsChart.suffix_exitless hk hp hBdvd hBlt

/-- **Lemma 15, excess splitting.**  Excess is additive across a block-aligned split. -/
theorem block_locality_excess_split {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {B : ℕ} (hBdvd : k ∣ B) (hBlt : B < p.numVerts) {q : HPath k}
    (hq : q.verts = p.verts.drop B) :
    excess p = (∑ j ∈ Finset.range B, ProofsChart.perEdgeExc p j) + excess q :=
  ProofsChart.excess_split hk hp hBdvd hBlt hq

/-- **Lemma 16 (Weight-two map), determinism.**  A weight-2 boundary into a *fresh* class
is the map `τ₂` (word level: `bwt` is the boundary weight from the block exit). -/
theorem tau2_deterministic {k : ℕ} (hk : 2 ≤ k) {u v : List ℕ}
    (hu : IsPermWord k u) (hv : IsPermWord k v)
    (hw2 : ProofsRigidity2.bwt k u v = 2) (hfresh : rotClass v ≠ rotClass u) :
    v = ProofsRigidity2.tau2 k u :=
  ProofsRigidity2.fresh_w2_forced hk hu hv hw2 hfresh

/-- **Lemma 16, period `k − 1`.**  `τ₂^{k−1}` returns to the starting block, so a maximal
weight-2 run spans at most `k − 1` blocks. -/
theorem tau2_period {k : ℕ} (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) (b c : ℕ) :
    (ProofsRigidity2.tau2 k)^[k - 1] (A ++ [b, c]) = A ++ [b, c] :=
  ProofsRigidity2.tau2_period hk hA b c

/-- **Lemma 17 (Weight-three full continuation).**  Among the six weight-3 successors of a
completed run's exit, the unique one whose induced run is disjoint from the current run is
`T₁ = τ₃` (the paper's collision analysis: `T₃,T₄,T₆` revisit at once, `T₂,T₅` collide at
iterate `m−1`).  `runW (A.rotate 1) b c 0` *is* `τ₃` of the run start. -/
theorem tau3_forced {As : List ℕ} {a₁ b c : ℕ}
    (he : IsPermWord (As.length + 3) (c :: b :: a₁ :: As))
    {v : List ℕ} (hv : IsPermWord (As.length + 3) v)
    (hover : (c :: b :: a₁ :: As).drop 3 = v.take (As.length))
    (hvfresh : ¬ ProofsRigidity2.RunVisited (a₁ :: As) b c (rotClass v))
    (hlast : ¬ ProofsRigidity2.RunVisited (a₁ :: As) b c
      (rotClass ((ProofsRigidity2.tau2 (As.length + 3))^[As.length] v))) :
    v = ProofsRigidity2.runW ((a₁ :: As).rotate 1) b c 0 :=
  ProofsRigidity2.forced_step he hv hover hvfresh hlast

/-- **Proposition 18 (Edge counts), weight-1 clause.**  All `ℓ − 1` edges have weight ≥ 1. -/
theorem edge_count_one {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 1 = p.numVerts - 1 :=
  Hunter.prp_1edgebound hk hp

/-- **Proposition 18, weight-2 clause.**  Exactly `⌈ℓ/k⌉ − 1` edges have weight ≥ 2. -/
theorem edge_count_two {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 2 = p.numVerts ⌈/⌉ k - 1 :=
  Hunter.prp_2edgebound hk hp

/-- **Proposition 18, weight-3 clause.**  At least `⌈ℓ/(k(k−1))⌉ − 1` edges have
weight ≥ 3. -/
theorem edge_count_three {k : ℕ} (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) :
    edgeCountGe p 3 ≥ p.numVerts ⌈/⌉ (k * (k - 1)) - 1 :=
  Hunter.prp_3edgebound hk hp

/-- **Equation (3) of the paper.**  The opened-block weight identity
`w(p) = (ℓ−1) + (b−1) + E` with `b = ⌈ℓ/k⌉`. -/
theorem weight_identity {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) :
    p.wtP = (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p :=
  ProofsRecursion.wtP_decompose hk hp

/-- **Lemma 19 (Rigidity), chart-identification clause** (word level).  A block sequence
over the tight window `N = (k−1)(k−2)` with pairwise distinct classes, weight-2 boundaries
inside runs and weight-3 boundaries between the `k−2` runs **is the deterministic chart**
`C_{j,i}`.  (In the research development the paper's "excess ≤ k−3 forces excess = k−3 and
all boundary weights tight" pigeonhole is `ProofsRigidity2.runlen_pigeonhole` /
`boundary_exact`; this clause is the uniqueness conclusion.) -/
theorem rigidity_chart {A' : List ℕ} {z b c : ℕ} {q : ℕ → List ℕ}
    (hperm : ∀ s, IsPermWord (A'.length + 3) (q s))
    (hstart : q 0 = A' ++ [z, b, c])
    (hdist : ∀ s t, s < (A'.length + 2) * (A'.length + 1) →
        t < (A'.length + 2) * (A'.length + 1) → s ≠ t → rotClass (q s) ≠ rotClass (q t))
    (hw2 : ∀ j i, j ≤ A'.length → i < A'.length + 1 →
        ProofsRigidity2.bwt (A'.length + 3) (q (j * (A'.length + 2) + i))
          (q (j * (A'.length + 2) + i + 1)) = 2)
    (hw3 : ∀ j, j < A'.length →
        ProofsRigidity2.bwt (A'.length + 3) (q (j * (A'.length + 2) + (A'.length + 1)))
          (q (j * (A'.length + 2) + (A'.length + 1) + 1)) = 3) :
    ∀ j i, j ≤ A'.length → i ≤ A'.length + 1 →
      q (j * (A'.length + 2) + i) = ProofsClosure3.chartWord A' z b c j i :=
  ProofsChartEq.tight_is_chart hperm hstart hdist hw2 hw3

/-- **Corollary 20 (Small-`ℓ` equality).**  `i_k(ℓ) = j_k(ℓ)` on the whole base region. -/
theorem base_region_equality {k ℓ : ℕ} (hk : 3 ≤ k) (hℓ0 : 0 < ℓ)
    (hℓ : ℓ ≤ k * (k - 1) * (k - 2)) (hex : HasExitlessPath k ℓ) :
    iExitless k ℓ = j k ℓ :=
  Hunter.thm2_equality hk hℓ0 hℓ hex

/-- **Corollary 20, the pivot value.**  `i_k(k(k−1)(k−2)) = k²(k−2) − 3` — the chart's
weight. -/
theorem pivot_value {k : ℕ} (hk : 3 ≤ k) :
    iExitless k (k * (k - 1) * (k - 2)) = k ^ 2 * (k - 2) - 3 := by
  have hpos : 0 < k * (k - 1) * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    positivity
  rw [Hunter.thm2_equality hk hpos le_rfl (Proved.hasExitlessPath_pivot k hk),
    Hunter.j_at_pivot hk]

/-- **Lemma 21 (Closure).**  Every successor of the chart's final exit landing in a class
the chart has not visited costs at least 4 — the extra unit past the window floor. -/
theorem closure {A' : List ℕ} {z b c : ℕ} (hn : 1 ≤ A'.length)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hvis : ¬ ProofsClosure3.VisitedByChart A' z b c (rotClass v)) :
    4 ≤ wt (A'.length + 3) (ProofsClosure3.finalExit A' z b c) v :=
  ProofsClosure3.chart_closure A' z b c hn hs hv hvis

/-- **The threshold `G` matches the paper's definition** `G(E) = (E+1)(k−1) − ⌊E/(k−2)⌋`. -/
theorem G_matches (k E : ℕ) : G k E = (E + 1) * (k - 1) - E / (k - 2) := rfl

/-- **Lemma 22 (Excess-to-weight dictionary).**  With `b = ⌈ℓ/k⌉` and `D = Dfr`,
`j_k(ℓ) = D(b) + (ℓ−1) + (b−1)` — the identity `ℓ + b − 2 + D(b) = j_k(ℓ)` in ℕ form. -/
theorem dictionary {k : ℕ} (hk : 4 ≤ k) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    j k ℓ = Dfr k (ℓ ⌈/⌉ k) + (ℓ - 1) + (ℓ ⌈/⌉ k - 1) :=
  ProofsRigid.j_frontier_eq hk ℓ hℓ

/-- **Lemma 22, the `D ↔ G` inversion.**  `D(b) ≤ E ↔ b ≤ G(E)`. -/
theorem dictionary_inversion {k : ℕ} (hk : 4 ≤ k) {b : ℕ} (hb : 1 ≤ b) (E : ℕ) :
    Dfr k b ≤ E ↔ b ≤ G k E :=
  ProofsInduction.Dfr_le_iff_le_G hk b hb E

/-- **Theorem 23 (Excess bound), the induction's conclusion.**  Every exitless path
satisfies `b ≤ G(E)` at the honest opened-block count — the paper's strong induction on
excess, machine-checked. -/
theorem opened_blocks_le_G {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    (h0 : 0 < p.numVerts) :
    p.numVerts ⌈/⌉ k ≤ G k (excess p) :=
  (ProofsRigid.blockCeil_iff_G hk).mp (Proved.excessBlockCeilAll k hk) p hp h0

/-- **Theorem 23 (Hunter's Theorem 2).**  `i_k(ℓ) ≥ j_k(ℓ)` for every supported length,
every `k ≥ 3`. -/
theorem exitless_inequality {k ℓ : ℕ} (hk : 3 ≤ k) (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  Hunter.thm2 hk hex

/-! ## §6  The coefficient and factorial forms -/

/-- **Lemma 24 (Periodicity).**  `j_k(ℓ₀) + 3 = q_k·ℓ₀` — the exact identity that makes
`φ(ℓ) = j_k(ℓ) − q_kℓ` periodic with period `ℓ₀`. -/
theorem periodicity {k : ℕ} (hk : 3 ≤ k) :
    (j k (ell0 k) : ℝ) + 3 = coeff k * ((ell0 k : ℕ) : ℝ) := by
  -- the ℕ value of `j` at `ℓ₀`, via the base branch and the two ceiling evaluations
  have hle : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [ell0_eq]; omega
  have hj0 : j k (ell0 k) = ell0 k + ((k - 1) * (k - 2) - 1) + (k - 2) - 3 := by
    rw [j_base (Or.inl hle), ProofsPu.cd_ell0_k hk, ProofsPu.cd_ell0_kk hk]
  have hD := ProofsReductions.D_pos hk
  have hratio := ProofsReductions.ratio_eq_coeff hk
  -- `coeff k · (P − k) = I − k + 2` from the pivot-ratio identity
  have hq : coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ))
      = (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2 := by
    rw [← hratio, div_mul_cancel₀]
    exact ne_of_gt hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  -- product helper facts, phrased so `omega` can treat the products as atoms
  have hp2 : 2 * 1 ≤ (m + 2) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (m + 3) * 2 ≤ (m + 3) * ((m + 2) * (m + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hassoc : (m + 3) * (m + 2) * (m + 1) = (m + 3) * ((m + 2) * (m + 1)) :=
    Nat.mul_assoc _ _ _
  have hsub : (m + 3) ≤ (m + 3) * (m + 2) * (m + 1) := by omega
  -- cast `ℓ₀` to ℝ
  have hcast0 : ((ell0 (m + 3) : ℕ) : ℝ)
      = ((m + 3 : ℕ) : ℝ) * (((m + 3 : ℕ) : ℝ) - 1) * (((m + 3 : ℕ) : ℝ) - 2)
        - ((m + 3 : ℕ) : ℝ) := by
    rw [ell0_eq]
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    rw [Nat.cast_sub hsub]
    push_cast; ring
  -- the ℕ identity `j(ℓ₀) + (k + 4) = k²(k−2)` (no truncation for k ≥ 3)
  have hval : j (m + 3) (ell0 (m + 3)) + ((m + 3) + 4) = (m + 3) ^ 2 * (m + 1) := by
    rw [hj0, ell0_eq]
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    have h1 : 1 ≤ (m + 2) * (m + 1) := by omega
    have h2 : 3 ≤ (m + 3) * (m + 2) * (m + 1) - (m + 3) + ((m + 2) * (m + 1) - 1)
        + (m + 1) := by omega
    zify [hsub, h1, h2]
    ring
  -- assemble over ℝ
  rw [hcast0, hq]
  have hIcast : ((m + 3 : ℕ) : ℝ) ^ 2 * (((m + 3 : ℕ) : ℝ) - 2)
      = (((m + 3) ^ 2 * (m + 1) : ℕ) : ℝ) := by push_cast; ring
  rw [hIcast]
  have hvalR : ((j (m + 3) (ell0 (m + 3)) : ℕ) : ℝ) + (((m + 3) : ℕ) : ℝ) + 4
      = ((((m + 3) ^ 2 * (m + 1) : ℕ)) : ℝ) := by exact_mod_cast hval
  linarith

/-- **Lemma 25 (The optimum sits at the chart length).**  The subproblem-1 ratio is
minimized at the pivot `ℓ₁ = k(k−1)(k−2)` (stated, as in the reduction's use, at the
`i_k`-level over supported lengths — the composition of the paper's Lemma 25 with
Theorem 2). -/
theorem ratio_minimized_at_pivot {k : ℕ} (hk : 3 ≤ k) {ℓ : ℕ} (h : k < ℓ)
    (hex : HasExitlessPath k ℓ) (hpivot : HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ))
      ≤ ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ)) :=
  ProofsHeadline.prop4_closed hk h hex hpivot

/-- **Lemma 25, the pivot ratio is exactly `q_k`.** -/
theorem pivot_ratio_eq_coeff {k : ℕ} (hk : 3 ≤ k) :
    ((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
        (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)) = coeff k := by
  rw [pivot_value hk, ProofsReductions.castI hk, ProofsReductions.castP (by omega),
    ProofsReductions.ratio_eq_coeff hk]

/-- **Theorem 26 (Hunter's bound), superpermutation form.**  For every `k ≥ 3`,
`S(k) ≥ q_k·k! + k + (k−2) − q_k·k` — the paper's exact pointwise inequality. -/
theorem hunters_bound {k : ℕ} (hk : 3 ≤ k) :
    (Ssuper k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) + ((k : ℝ) - 2)
      - coeff k * (k : ℝ) := by
  have h := superperm_length_ge_hunterPointwise hk
  have hD := ProofsReductions.D_pos hk
  have hq : coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ))
      = (k : ℝ) ^ 2 * ((k : ℝ) - 2) - 3 - (k : ℝ) + 2 := by
    rw [← ProofsReductions.ratio_eq_coeff hk, div_mul_cancel₀]
    exact ne_of_gt hD
  have e1 : coeff k * ((k.factorial : ℝ) - (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2))
      = coeff k * (k.factorial : ℝ)
        - coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) := by ring
  have e2 : coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ))
      = coeff k * ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) - coeff k * (k : ℝ) := by ring
  linarith [h, hq, e1, e2]

/-- **Theorem 26, Hamiltonian-path form.**  `L(k) ≥ q_k·k! + (k−2) − q_k·k`. -/
theorem hunters_bound_L {k : ℕ} (hk : 3 ≤ k) :
    (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) + ((k : ℝ) - 2) - coeff k * (k : ℝ) := by
  have hS := hunters_bound hk
  rw [S_eq_k_add_L (by omega)] at hS
  push_cast at hS
  linarith

/-- **Corollary 27 (Factorial form), exact version.**  With `d = k² − 3k + 1`, for every
`k ≥ 3`:
`S(k) ≥ k! + (k−1)! + (k−2)! + ((k−2)! − (k−2))/d + k − 3`.
This is Theorem 26 with the coefficient expanded exactly; the fraction is the exact
improvement over `HPV(k) = k! + (k−1)! + (k−2)! + k − 3`, zero for `k = 3, 4` and positive
from `k = 5`. -/
theorem factorial_exact {k : ℕ} (hk : 3 ≤ k) :
    (Ssuper k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
      + (((k - 2).factorial : ℝ) - ((k : ℝ) - 2)) / ((k : ℝ) ^ 2 - 3 * (k : ℝ) + 1)
      + (k : ℝ) - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have h := hunters_bound (k := m + 3) (by omega)
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have f2 : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have f3 : ((m + 3).factorial : ℝ) = ((m : ℝ) + 3) * ((m + 2).factorial : ℝ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  set x : ℝ := ((m + 1).factorial : ℝ) with hx
  have key : coeff (m + 3) * (((m + 3).factorial : ℝ)) + ((m : ℝ) + 3)
        + (((m : ℝ) + 3) - 2) - coeff (m + 3) * ((m : ℝ) + 3)
      = ((m + 3).factorial : ℝ) + ((m + 2).factorial : ℝ) + x
        + ((x - (((m : ℝ) + 3) - 2)) / (((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1))
        + ((m : ℝ) + 3) - 3 := by
    rw [f3, f2, coeff]
    push_cast
    have hne1 : ((m : ℝ) + 3) ≠ 0 := by positivity
    have hne2 : ((m : ℝ) + 3 - 1) ≠ 0 :=
      ne_of_gt (by linarith : (0 : ℝ) < (m : ℝ) + 3 - 1)
    have hne3 : ((m : ℝ) + 3) * ((m : ℝ) + 3 - 1) * ((m : ℝ) + 3 - 2) - ((m : ℝ) + 3) ≠ 0 := by
      rw [show ((m : ℝ) + 3) * ((m : ℝ) + 3 - 1) * ((m : ℝ) + 3 - 2) - ((m : ℝ) + 3)
          = ((m : ℝ) + 3) * ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 1) from by ring]
      positivity
    have hne4 : ((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1 ≠ 0 := by
      rw [show ((m : ℝ) + 3) ^ 2 - 3 * ((m : ℝ) + 3) + 1
          = (m : ℝ) ^ 2 + 3 * (m : ℝ) + 1 from by ring]
      positivity
    have hne5 : (1 + (m : ℝ) * 3 + (m : ℝ) ^ 2) ≠ 0 := by positivity
    field_simp
    linear_combination mul_inv_cancel₀ hne5
  push_cast at h ⊢
  linarith [h, key.ge, key.le]

/-- **Corollary 27, clean form.**  For every `k ≥ 6`, with no error term:
`S(k) ≥ k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)!`. -/
theorem factorial_clean {k : ℕ} (hk : 6 ≤ k) :
    (Ssuper k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
      + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
  have h := factorial_exact (k := m + 6) (by omega)
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2] at h
  rw [e1, e2, e4, e5]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have f2 : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have f3 : ((m + 3).factorial : ℝ) = ((m : ℝ) + 3) * ((m + 2).factorial : ℝ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have f4 : ((m + 4).factorial : ℝ) = ((m : ℝ) + 4) * ((m + 3).factorial : ℝ) := by
    rw [show m + 4 = (m + 3) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  set x : ℝ := ((m + 1).factorial : ℝ) with hx
  have hxpos : (0 : ℝ) ≤ x := by positivity
  have hD : ((m : ℝ) + 6) ^ 2 - 3 * ((m : ℝ) + 6) + 1 = (m : ℝ) ^ 2 + 9 * (m : ℝ) + 19 := by
    ring
  have hDpos : (0 : ℝ) < (m : ℝ) ^ 2 + 9 * (m : ℝ) + 19 := by positivity
  have hDne : ((m : ℝ) ^ 2 + 9 * (m : ℝ) + 19) ≠ 0 := ne_of_gt hDpos
  -- the surplus of the exact form over the clean form is a nonnegative fraction
  have sur : (((m + 4).factorial : ℝ) - (((m : ℝ) + 6) - 2))
        / (((m : ℝ) + 6) ^ 2 - 3 * ((m : ℝ) + 6) + 1) + ((m : ℝ) + 6) - 3
      - (((m + 2).factorial : ℝ) - 2 * x)
      = (x * (7 * (m : ℝ) + 24)
          + ((m : ℝ) ^ 3 + 12 * (m : ℝ) ^ 2 + 45 * (m : ℝ) + 53))
        / ((m : ℝ) ^ 2 + 9 * (m : ℝ) + 19) := by
    rw [f4, f3, f2, hD]
    field_simp
    ring
  have surpos : (0 : ℝ) ≤ (x * (7 * (m : ℝ) + 24)
      + ((m : ℝ) ^ 3 + 12 * (m : ℝ) ^ 2 + 45 * (m : ℝ) + 53))
    / ((m : ℝ) ^ 2 + 9 * (m : ℝ) + 19) := by positivity
  push_cast at h ⊢
  linarith [h, sur.ge, sur.le, surpos]

/-- **Corollary 27, earlier asymptotic version** (superseded by `factorial_exact` /
`factorial_clean`, retained for the record):
`S(k) ≥ k! + (k−1)! + (k−2)! + (k−4)! − 2(k−5)! − C(k−6)!` for all large `k`. -/
theorem factorial_form :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Ssuper k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ)
        + ((k - 2).factorial : ℝ) + ((k - 4).factorial : ℝ)
        - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) := by
  obtain ⟨C, k₀, h⟩ := Hunter.eq_weak
  refine ⟨C, max k₀ 1, fun k hk => ?_⟩
  have h1 : (1 : ℕ) ≤ k := le_trans (le_max_right k₀ 1) hk
  rw [← Proved.bridge_Lstar_eq_Ssuper h1]
  exact h k (le_trans (le_max_left k₀ 1) hk)

/-- **Corollary 28 (Pointwise consequences), `k = 3`.**  New here: the development
previously exposed only `k = 5,…,8`. -/
theorem pointwise_3 : 9 ≤ Ssuper 3 := by
  have h := superperm_length_ge_hunterPointwise (k := 3) (by omega)
  by_contra hnot
  have hn : Ssuper 3 ≤ 8 := by omega
  have hr : (Ssuper 3 : ℝ) ≤ 8 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

/-- **Corollary 28, `k = 4`.**  Also new; the bound is exactly `33 = S(4)`. -/
theorem pointwise_4 : 33 ≤ Ssuper 4 := by
  have h := superperm_length_ge_hunterPointwise (k := 4) (by omega)
  by_contra hnot
  have hn : Ssuper 4 ≤ 32 := by omega
  have hr : (Ssuper 4 : ℝ) ≤ 32 := by exact_mod_cast hn
  norm_num [coeff] at h
  linarith

/-- **Corollary 28, `k = 5,6,7,8`.** -/
theorem pointwise_5 : 153 ≤ Ssuper 5 := superperm_length_ge_5_153
theorem pointwise_6 : 869 ≤ Ssuper 6 := superperm_length_ge_6_869
theorem pointwise_7 : 5888 ≤ Ssuper 7 := superperm_length_ge_7_5888
theorem pointwise_8 : 46103 ≤ Ssuper 8 := superperm_length_ge_8_46103

end Hunter.Paper

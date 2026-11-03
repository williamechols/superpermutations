/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsWP
import Hunter.ProofsPathrule
import Hunter.ProofsReductions
import Hunter.ProofsMore

/-!
# Bound 2 and the composition closures (`Hunter/ProofsB2.lean`)

This file is the **composition hub**: it feeds the now-proved keystone `lem_pathrule`
(`Hunter.Proved.lem_pathrule`, proved outright in `Hunter/ProofsPathrule.lean`) into the
hypothesis-carrying theorems of the WP track (`Hunter/ProofsWP.lean`) and reductions track,
producing the tightest currently-derivable versions with the smallest possible remaining
hypothesis lists.

It does NOT `import Hunter.Statements` (build cycle); all Statements types are reconstructed
verbatim.  Helper lemmas live in `namespace Hunter.ProofsB2`; the delivered targets live in
`namespace Hunter.Proved` with the type copied verbatim (or `_final` / `_of_*` variants that
enumerate their remaining hypotheses).

Zero `sorry`, zero new axioms.  See `PROGRESS-b2.md` for the per-target ledger.
-/

namespace Hunter

open scoped Classical

namespace Proved

variable {k : ℕ}

/-! ## 1. Composition closures — feeding `lem_pathrule` into the WP track -/

/-- **prp-wPgivenX (final)** — the WP-track `prp_wPgivenX` with its cross-track hypothesis
`h_pathrule` **discharged** by the now-proved `Hunter.Proved.lem_pathrule`.  The only
remaining hypothesis is the guard `2 ≤ k` (needed so `vertsOf (F P) = univ`, i.e. no isolated
vertices; consistent with the paper's Hamiltonian-`P`, `k ≥ 3` regime).  **No cross-track
hypotheses remain.** -/
theorem prp_wPgivenX_final {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    P.wtP ≥ (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P) :=
  Hunter.Proved.prp_wPgivenX hP hk (Hunter.Proved.lem_pathrule hP)

/-- **b1 (final)** — Bound 1 with the WP-track `b1_unconditional`'s `h_pathrule` hypothesis
**discharged** by `Hunter.Proved.lem_pathrule` (quantified over all Hamiltonian `P`).  The
only remaining hypothesis is the guard `2 ≤ k`.  **No cross-track hypotheses remain.** -/
theorem b1_final (hk : 2 ≤ k) :
    L k ≥ sInf {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} :=
  Hunter.Proved.b1_unconditional hk (fun _ hP => Hunter.Proved.lem_pathrule hP)

/-! ## 2. Re-exposed outright §5 results (no hypotheses beyond the logged guards)

`cor_exitlessrule` and `prp_Xk_se_necessity` are already proved outright / fully-discharged in
`Hunter/ProofsPathrule.lean`.  We re-expose the necessity direction under the canonical name so
the dashboard below can cite a single hypothesis-free fact. -/

/-- **prp-Xk-se (necessity, final)** — for `2 ≤ k`, `X ∈ 𝒳_k` forces `V(X) = V(𝒮_k)` and
`Comps(X)` is a set of strongly exitless paths.  Fully discharged (no cross-track hypotheses);
re-exposed from `Hunter.Proved.prp_Xk_se_necessity_amended'`.  The guard `2 ≤ k` is genuinely
necessary (the verbatim statement is false at `k ≤ 1`). -/
theorem prp_Xk_se_necessity_final {X : Finset (Vtx k × Vtx k)} (hk : 2 ≤ k) (hX : X ∈ Xk k) :
    vertsOf X = Finset.univ ∧ IsUnionOfStronglyExitlessPaths X :=
  Hunter.Proved.prp_Xk_se_necessity_amended' hk hX

end Proved

/-! ## 3. Bound 2 from Bound 1 — the `prp_gives_b2` composition (`take23` §"Getting Bounds")

We assemble the verbatim `b2` from `b1_final` and `prp_gives_b2` (taken as an explicit
hypothesis over all `X ∈ 𝒳_k`), following take23 l.657–696.  The argument:

* `b1_final` gives `L(k) ≥ sInf S` with `S` the ℕ-valued `X_VALUE` set; since `S` is nonempty
  (⟸ `𝒳_k` nonempty) the ℕ-infimum is **attained** at some `X*` (`Nat.sInf_mem`);
* `prp_gives_b2` at `X*` gives `X*_VALUE ≥ R_k·k! + sInf I_{X*}` where `I_{X*}` ranges over the
  path-components of `X*`;
* every path-component of `X* ∈ 𝒳_k` lies in `𝒳'_k`, so `I_{X*}` shifts into the `b2` set,
  giving `R_k·k! + sInf I_{X*} ≥ sInf B`.

Remaining hypotheses: `2 ≤ k`, `prp_gives_b2` (`hgb2`), `𝒳_k` nonempty (`hne_Xk`), and
`BddBelow` of the `b2` value set (`hBddB`, the `sInf ∅ = 0` junk-guard). -/
namespace ProofsB2

open Hunter.Proved

variable {k : ℕ}

/-- `𝒳_k` nonempty ⟹ the `b1` value set is nonempty. -/
theorem b1Set_nonempty (hne_Xk : (Xk k).Nonempty) :
    {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X}.Nonempty := by
  obtain ⟨X, hX⟩ := hne_Xk
  exact ⟨_, X, hX, rfl⟩

/-- For `X ∈ 𝒳_k` (with `2 ≤ k`), `Comps X` is nonempty, hence the inner (per-component) value
set of `prp_gives_b2` is nonempty. -/
theorem innerSet_nonempty (hk : 2 ≤ k) {X : Finset (Vtx k × Vtx k)} (hX : X ∈ Xk k) :
    {q : ℝ | ∃ p, IsPathComponent p X ∧ q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)}.Nonempty := by
  obtain ⟨P, hP, rfl⟩ := hX
  have h1 : 1 ≤ numComps (F P) := ProofsWP.one_le_numComps_F hP hk
  have hne : (Comps (F P)).Nonempty := Finset.card_pos.mp h1
  obtain ⟨C, hC⟩ := hne
  obtain ⟨p, _, hpc⟩ := Hunter.Proved.lem_pathrule hP C hC
  exact ⟨_, p, hpc, rfl⟩

/-- `1 ≤ numComps X` for `X ∈ 𝒳_k`, `2 ≤ k`. -/
theorem one_le_numComps (hk : 2 ≤ k) {X : Finset (Vtx k × Vtx k)} (hX : X ∈ Xk k) :
    1 ≤ numComps X := by
  obtain ⟨P, hP, rfl⟩ := hX
  exact ProofsWP.one_le_numComps_F hP hk

end ProofsB2

namespace Proved

variable {k : ℕ}

/-- **b2 (from `prp_gives_b2`)** — Bound 2, verbatim type.  Composed from `b1_final` and
`prp_gives_b2` (`hgb2`).  Remaining hypotheses: `2 ≤ k`; `hgb2` (= `prp_gives_b2`, still open,
its proof lives elsewhere); `hne_Xk` (`𝒳_k` nonempty, ⟸ a Hamiltonian path exists / greedy);
`hBddB` (the `b2` value set is bounded below — the `sInf ∅ = 0` junk-guard, finite regime).
No other cross-track hypotheses. -/
theorem b2_of_gives_b2 (hk : 2 ≤ k)
    (hgb2 : ∀ X : Finset (Vtx k × Vtx k), X ∈ Xk k →
      ((numComps X : ℝ) - 1) + (MinThrough X : ℝ) + (wEdges X : ℝ)
        ≥ Rk k * (k.factorial : ℝ)
          + sInf {q : ℝ | ∃ p, IsPathComponent p X ∧
              q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)})
    (hne_Xk : (Xk k).Nonempty)
    (hBddB : BddBelow {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))}) :
    (L k : ℝ) ≥ sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} := by
  -- b1: `L k ≥ sInf S` over ℕ, attained at some `X*`.
  have hb1 := b1_final (k := k) hk
  set S : Set ℕ := {m | ∃ X, X ∈ Xk k ∧ m = (numComps X - 1) + MinThrough X + wEdges X} with hS
  have hSne : S.Nonempty := ProofsB2.b1Set_nonempty hne_Xk
  have hmem : sInf S ∈ S := Nat.sInf_mem hSne
  obtain ⟨X, hX, hval⟩ := hmem
  -- cast the ℕ `X_VALUE` to its ℝ form
  have hnc1 : 1 ≤ numComps X := ProofsB2.one_le_numComps hk hX
  have hcastVal : ((sInf S : ℕ) : ℝ)
      = ((numComps X : ℝ) - 1) + (MinThrough X : ℝ) + (wEdges X : ℝ) := by
    rw [hval]; push_cast [Nat.cast_sub hnc1]; ring
  -- gives_b2 at `X`
  have hgives := hgb2 X hX
  set I : Set ℝ := {q : ℝ | ∃ p, IsPathComponent p X ∧
      q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)} with hI
  have hIne : I.Nonempty := ProofsB2.innerSet_nonempty hk hX
  set B : Set ℝ := {q : ℝ | ∃ p, p ∈ Xk' k ∧
      q = (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))} with hB
  -- `sInf B ≤ R_k·k! + sInf I`: every inner value shifts into `B`.
  have hshift : sInf B ≤ Rk k * (k.factorial : ℝ) + sInf I := by
    have h1 : sInf B - Rk k * (k.factorial : ℝ) ≤ sInf I := by
      apply le_csInf hIne
      rintro y ⟨p, hpc, rfl⟩
      have hpXk' : p ∈ Xk' k := ⟨X, hX, hpc⟩
      have hmemB : (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ)) ∈ B :=
        ⟨p, hpXk', rfl⟩
      have hle : sInf B ≤ (p.wtP : ℝ) + Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ)) :=
        csInf_le hBddB hmemB
      have hdist : Rk k * ((k.factorial : ℝ) - (p.numVerts : ℝ))
          = Rk k * (k.factorial : ℝ) - Rk k * (p.numVerts : ℝ) := by ring
      rw [hdist] at hle; linarith
    linarith
  -- assemble: `L ≥ sInf S = X_VALUE ≥ R_k·k! + sInf I ≥ sInf B`.
  have hLcast : (L k : ℝ) ≥ ((sInf S : ℕ) : ℝ) := by exact_mod_cast hb1
  linarith [hLcast, hcastVal.ge, hcastVal.le, hgives, hshift]

end Proved

/-! ## 4. `prp_Xkcomps` (𝒳'_k = strongly exitless paths)

The `⊆` direction is proved **outright**: `cor_exitlessrule`'s strongly-exitless argument
depends only on `IsPathComponent p (F P)` (not on `p` coming from `lem_pathrule`), so we
factor it out and apply it to any path-component appearing in `𝒳'_k`.  The `⊇` direction is
the paper's `P(p₁,…,pₙ)` "unwinding" (`ADD DIAGRAM`); we take it as the explicit hypothesis
`hrev` — the single-path consequence of `prp_Xk_se_sufficiency` via the spanning-cover
construction (a genuine second construction not written down in the source). -/
namespace ProofsB2

open Hunter.Proved

variable {k : ℕ}

/-- **Every path-component of `F(P)` is strongly exitless.**  This is exactly the body of
`cor_exitlessrule`, but stated for an arbitrary `IsPathComponent p (F P)` (the argument never
uses that `p` was produced by `lem_pathrule`).  Reusable for the `⊆` half of `prp_Xkcomps`. -/
theorem stronglyExitless_of_isPathComponent {P p : HPath k} (hP : P.IsHamiltonian)
    (hk2 : 2 ≤ k) (hp : IsPathComponent p (F P)) : p.StronglyExitless := by
  refine ⟨?_, ?_⟩
  · -- Exitless
    rw [HPath.Exitless]
    intro hEE
    obtain ⟨i, hi1, hw, hlt⟩ := hEE
    by_cases hvCm1 : p.vert i ∈ Cm1 P
    · have hi : i < p.numVerts := by omega
      have hviv : p.vert i ∈ p.verts := ProofsExitless.vert_mem p hi
      have hsvV : sigma (p.vert i) ∈ p.verts := by
        have hcyc : sigma (p.vert i) ∈ cyc (p.vert i) :=
          ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma (p.vert i))
        exact HPath.mem_vertsFinset.mp
          (ProofsPathrule.cyc_subset_pc hP hk2 hp (HPath.mem_vertsFinset.mpr hviv) hcyc)
      have hposvi : p.pos (p.vert i) = i := ProofsExitless.pos_vert p hi
      have hlt' : p.pos (p.vert i) < p.pos (sigma (p.vert i)) := by rw [hposvi]; exact hlt
      have hord := Proved.clm_ordering hP hp (Finset.mem_union.mpr (Or.inr hvCm1)) hviv hsvV hlt'
      have hsvC0 : sigma (p.vert i) ∈ C0 P := ProofsPathrule.mem_Cm1_iff.mp hvCm1
      have hle : P.pos (sigma (p.vert i)) ≤ P.pos (p.vert i) :=
        (ProofsPathrule.mem_C0_iff.mp hsvC0) (p.vert i)
          (ProofsStructure.rotClass_sigma (p.vert i)).symm
      omega
    · have h2 := Proved.clm_rule2 hP hvCm1
      have hmem : (p.vert i, p.vert (i + 1)) ∈ outV (F P) (p.vert i) := by
        simp only [outV, mem_out, Finset.mem_singleton]
        exact ⟨hp.1 (ProofsStructure.vert_consec_mem_edges hi1), trivial⟩
      rw [h2, Finset.mem_singleton] at hmem
      have hsucc : p.vert (i + 1) = sigma (p.vert i) := (Prod.ext_iff.mp hmem).2
      rw [hsucc, ew_sigma (show (1 : ℕ) ≤ k by omega) (p.vert i)] at hw
      omega
  · -- `σ(p.last) ∈ p`
    have hcyc : sigma p.last ∈ cyc p.last :=
      ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma p.last)
    exact HPath.mem_vertsFinset.mp
      (ProofsPathrule.cyc_subset_pc hP hk2 hp (HPath.mem_vertsFinset.mpr p.last_mem) hcyc)

/-- **`𝒳'_k ⊆ {strongly exitless paths}`** — proved outright (for `2 ≤ k`).  Every element of
`𝒳'_k` is a path-component of some `X = F(P) ∈ 𝒳_k`, hence strongly exitless by the helper. -/
theorem Xkcomps_subset (hk : 2 ≤ k) :
    Xk' k ⊆ {p : HPath k | p.StronglyExitless} := by
  rintro p ⟨X, ⟨P, hP, rfl⟩, hpc⟩
  exact stronglyExitless_of_isPathComponent hP hk hpc

end ProofsB2

namespace Proved

variable {k : ℕ}

/-- **prp-Xkcomps (amended)** — `𝒳'_k` equals the set of all strongly exitless paths.
**AMENDED with the guard `2 ≤ k`** (consistent with `prp_Xk_se_necessity_amended'`; the
verbatim statement is degenerate at `k ≤ 1`).

The `⊆` direction is proved **outright** (`ProofsB2.Xkcomps_subset`, via
`cor_exitlessrule`'s argument).  The `⊇` direction (`hrev`) is taken as an explicit
hypothesis — the single-path form of `prp_Xk_se_sufficiency`: every strongly exitless path
appears as a component of some spanning `X ∈ 𝒳_k`, which is the paper's unwritten
`P(p₁,…,pₙ)` "unwinding" (`ADD DIAGRAM`).  This is the ONLY remaining hypothesis. -/
theorem prp_Xkcomps_amended (hk : 2 ≤ k)
    (hrev : {p : HPath k | p.StronglyExitless} ⊆ Xk' k) :
    Xk' k = {p : HPath k | p.StronglyExitless} :=
  Set.Subset.antisymm (ProofsB2.Xkcomps_subset hk) hrev

end Proved

/-! ## 5. `red_pstar` tightened, and `𝒳'_k` nonemptiness

`ProofsReductions`' `red_pstar` took `prp_Xkcomps` (`hXk`) and `𝒳'_k`-nonemptiness (`hne`) as
hypotheses.  We discharge `hXk` via `prp_Xkcomps_amended` (leaving its `hrev` half exposed) and
reduce `hne` to `𝒳_k`-nonemptiness (a single Hamiltonian path suffices). -/
namespace ProofsB2

open Hunter.Proved

variable {k : ℕ}

/-- `𝒳_k` nonempty ⟹ `𝒳'_k` nonempty (for `2 ≤ k`): any `X = F(P) ∈ 𝒳_k` has ≥ 1 component,
which (via `lem_pathrule`) is realized by a path-component `p ∈ 𝒳'_k`. -/
theorem Xk'_nonempty_of_Xk_nonempty (hk : 2 ≤ k) (hne_Xk : (Xk k).Nonempty) :
    (Xk' k).Nonempty := by
  obtain ⟨X, hX⟩ := hne_Xk
  obtain ⟨P, hP, rfl⟩ := hX
  have h1 : 1 ≤ numComps (F P) := ProofsWP.one_le_numComps_F hP hk
  obtain ⟨C, hC⟩ := Finset.card_pos.mp h1
  obtain ⟨p, _, hpc⟩ := Hunter.Proved.lem_pathrule hP C hC
  exact ⟨p, F P, ⟨P, hP, rfl⟩, hpc⟩

end ProofsB2

namespace Proved

variable {k : ℕ}

/-- **red-p\* (tightened)** — take23's `≥`-reduction, with `prp_Xkcomps` discharged (down to its
`hrev` = unwinding half) and `𝒳'_k`-nonemptiness reduced to `𝒳_k`-nonemptiness.  Remaining
hypotheses: `1 < r`, `2 ≤ k`, `hrev` (unwinding), `hne_Xk` (`𝒳_k` nonempty, ⟸ a Hamiltonian
path exists / greedy). -/
theorem red_pstar_tightened {r : ℝ} (hr : 1 < r) (hk : 2 ≤ k)
    (hrev : {p : HPath k | p.StronglyExitless} ⊆ Xk' k) (hne_Xk : (Xk k).Nonempty) :
    sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ q = (p.wtP : ℝ) - r * (p.numVerts : ℝ)}
      ≥ sInf {q : ℝ | ∃ ℓ, HasExitlessPath k ℓ ∧ q = (iExitless k ℓ : ℝ) - r * (ℓ : ℝ)} :=
  Hunter.Proved.red_pstar hr (prp_Xkcomps_amended hk hrev)
    (ProofsB2.Xk'_nonempty_of_Xk_nonempty hk hne_Xk)

/-! ## 6. Dashboard — the sharpest currently-derivable headline

`Hunter.Proved.thm1v2` (reductions track) is delivered from four hypotheses; every arithmetic
input beneath it is proved (`prop1`, `prop2`, `prop3`, `subprob2_comp`, the pivot packaging),
so the four hypotheses ARE the minimal remaining set.  We re-expose it verbatim as the
project dashboard, documenting the leaf decomposition.

**Minimal hypothesis set of `thm1v2_current`:**
1. `hthm2` — Theorem 2 lower bound `j_k(ℓ) ≤ i_k(ℓ)` (⟸ `prp_3edgebound`, the appendix GAP);
2. `hthm2eq` — Theorem 2 equality on the base region `0 < ℓ ≤ k(k−1)(k−2)` (⟸ `hthm2` ≥-half
   + `greedy_g` ≤-half);
3. `hproof` — `proof_thm1v2`'s per-`k` reduction output; its own leaves are: `b2`
   (⟸ `b2_of_gives_b2` here + `prp_gives_b2`), `red_pstar` (⟸ `red_pstar_tightened` here
   + unwinding), `red_R` (p_u-extension), the `g`-monotonicity `hg_mono`, and `prop4`
   (⟸ `prop3` [PROVED] + `hthm2`/`hthm2eq`);
4. `hexists` — `HasExitlessPath k (k(k−1)(k−2))` for all `k ≥ 3` (⟸ `greedy_g` existence).

The genuinely open combinatorial leaves are therefore: `prp_3edgebound`, `greedy_g`,
`prp_Xk_se_sufficiency` (the unwinding), `prp_gives_b2`, the `g`-monotonicity, and the
`red_R` p_u-extension.  Nothing on the arithmetic/reduction side remains open. -/
theorem thm1v2_current
    (hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  Hunter.Proved.thm1v2 hthm2 hthm2eq hproof hexists

/-- **thm1v1 (dashboard)** — the superpermutation form, same minimal hypothesis set. -/
theorem thm1v1_current
    (hthm2 : ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ)
    (hthm2eq : ∀ k ℓ, 3 ≤ k → 0 < ℓ → ℓ ≤ k * (k - 1) * (k - 2) → HasExitlessPath k ℓ →
        iExitless k ℓ = j k ℓ)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  Hunter.Proved.thm1v1 hthm2 hthm2eq hproof hexists

end Proved

end Hunter

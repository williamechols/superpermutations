/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta8

/-!
# Theorem 2 — the SYNTHESIS argument (final open lemma)

This file assembles the synthesis argument for the last open input of Hunter's Theorem 2 —
the **excess frontier** `ExcessFrontier k` (`excess q ≥ D(|q|)` for every exitless `q`).
It is built from four research dossiers whose union isolates:

* the **σ-frame** closure architecture (absolute-surplus-induction dossier): carrying the
  surplus `σ(q) = excess q − Dfr(|q|)` and splitting the per-`ℓ₀`-window step on whether the
  prefix is *frontier-tight* (`σ(q) = 0`) or has a *bank* (`σ(q) ≥ 1`).  The bank case is the
  proved floor `windowExcess_ge_km3` (`+ (k−3)`); the tight case needs the single new lemma
  **(MF)** — a frontier-tight prefix forces a heavy top window (payment `≥ k−2`);
* **Lemma A** (relative-exitless-lift dossier): the σ²-exclusion after complete 2-loops — the
  vertex-distinctness advance that a weight-3 marker-preserving boundary leaving a *completely
  traversed* marked 2-loop cannot be `sigmaSqWord`, hence is `alphaWord`.

## What closes here and what is the residual

The **reduction** `(MF) → ExcessFrontier k → thm2` is proved sorry-free below
(`excessFrontier_of_MF`, `thm2_of_MF`): the σ-frame strong induction, mirroring
`ProofsMeta5.excessFrontier_of_amortizedWindow`, with the window step split into the proved
floor (bank case) and (MF) (tight case).

The **residual** is (MF) itself.  All four dossiers independently prove (MF) is logically
equivalent to Theorem 2 modulo the proved inventory (absolute-surplus dossier §5), because the
*amortized cross-window carry* over **incomplete** 2-loops (door-runs of length `s < k−2`,
where Lemma A does **not** apply and `sigmaSqWord` is legal) is provably outside any
window-local / structural potential (`Refutations.windowExcess_false`;
`invariant/results.json` `structural_only: INFEASIBLE`).  Lemma A closes the *complete*-loop
side (the α-characterization everyone flagged as the hard open equality) but not the
incomplete-loop amortization.  Hence Theorem 2 is delivered here **conditional on the single
explicit hypothesis (MF)** (`FrontierTightHeavy k`), everything else sorry-free.

Namespace `Hunter.ProofsSynthesis`.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsSynthesis

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
open ProofsMeta ProofsMeta4 ProofsMeta5 ProofsMeta6 ProofsMeta8
open HPath

variable {k : ℕ}

/-! ## The residual (MF): a frontier-tight prefix forces a heavy top window

`Dfr(ℓ) = j_k(ℓ) − (ℓ−1) − (⌈ℓ/k⌉−1)` is the frontier demand, and `ExcessFrontier k` asserts
`excess q ≥ Dfr(|q|)`, i.e. the surplus `σ(q) := excess q − Dfr(|q|) ≥ 0`.  A prefix is
**frontier-tight** when `σ(q) = 0`, which — since the strong-induction hypothesis already gives
`σ(q) ≥ 0` — is exactly the equality `j_k(|q|) = (|q|−1) + (⌈|q|/k⌉−1) + excess q`.

(MF) is the absolute-surplus dossier's minimal combinatorial fact: for an exitless `p` in the
recursion region whose `ℓ₀`-prefix `q` is frontier-tight, the top `ℓ₀`-window pays the full
`k − 2`.  This is the sole new input the σ-frame induction needs beyond the proved floor. -/

/-- **(MF) — frontier-tight prefix ⇒ heavy top window.**  For an exitless `p` past the base
region and its exitless `(|p|−ℓ₀)`-prefix `q`, if `q` sits exactly on the excess frontier
(`σ(q) = 0`, stated as the frontier equality) then the top `ℓ₀`-window carries the full
`k − 2` units of excess: `excess q + (k − 2) ≤ excess p`. -/
def FrontierTightHeavy (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q →
    excess q + (k - 2) ≤ excess p

/-! ## The σ-frame reduction: `(MF) → ExcessFrontier k`

Strong induction on `|p|`, mirroring `ProofsMeta5.excessFrontier_of_amortizedWindow`.  The base
region is `excess_frontier_base`.  In the recursion region, the exitless prefix `q` of length
`n = |p| − ℓ₀` satisfies the induction hypothesis `σ(q) ≥ 0`; we split:

* **bank case** (`σ(q) ≥ 1`, i.e. the IH bound is strict): the proved floor
  `windowExcess_ge_km3` (`excess q + (k − 3) ≤ excess p`) suffices, the extra unit coming from
  the bank;
* **tight case** (`σ(q) = 0`, i.e. the IH bound is met with equality): (MF) supplies the full
  `excess q + (k − 2) ≤ excess p`.

The `j`/`Dfr`-recursion arithmetic (`j_rec_unfold_one`, the `⌈/⌉` splits) is discharged
verbatim as in the amortized-window reduction. -/

/-- **The σ-frame frontier reduction.**  `FrontierTightHeavy k` (= (MF)) implies the full
`ExcessFrontier k`.  Sorry-free strong induction; the only new input beyond the proved floor
`windowExcess_ge_km3` and base `excess_frontier_base` is (MF), used exactly on frontier-tight
prefixes. -/
theorem excessFrontier_of_MF (hk : 3 ≤ k) (hMF : FrontierTightHeavy k) :
    ExcessFrontier k := by
  have main : ∀ ℓ : ℕ, ∀ p : HPath k, p.Exitless → p.numVerts = ℓ →
      j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro p hpe hpℓ
      have h0 : 0 < p.numVerts := p.numVerts_pos
      by_cases hbaseR : p.numVerts ≤ k * (k - 1) * (k - 2)
      · exact excess_frontier_base hk hpe h0 hbaseR
      · rw [Nat.not_le] at hbaseR
        -- arithmetic facts about ℓ₀ and P = k(k-1)(k-2)  (mirrors ProofsMeta5)
        have he0pos : 0 < ell0 k := ell0_pos hk
        have hm : 2 ≤ (k - 1) * (k - 2) := by
          have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
          omega
        have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
        have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
        have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
        have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
        have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
        -- the prefix window
        set n := p.numVerts - ell0 k with hn
        have hn1 : 1 ≤ n := by rw [hn]; omega
        have hnle : n ≤ p.numVerts := by rw [hn]; omega
        have hnlt : n < p.numVerts := by rw [hn]; omega
        have hNsum : p.numVerts = n + ell0 k := by rw [hn]; omega
        obtain ⟨q, hqv, hqe⟩ := prefix_exitless hpe hn1 hnle
        have hqnv : q.numVerts = n := by
          have hlen : p.verts.length = p.numVerts := rfl
          show q.verts.length = n
          rw [hqv, List.length_take, hlen]; omega
        have hpre : q.verts = p.verts.take (p.numVerts - ell0 k) := by rw [hqv, hn]
        -- strengthened induction hypothesis on the prefix
        have hnltℓ : n < ℓ := by rw [← hpℓ]; exact hnlt
        have hIH := ih n hnltℓ q hqe hqnv
        rw [hqnv] at hIH
        -- j values and ceiling splits (identical to ProofsMeta5)
        have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
        have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
          rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd,
              ceilDiv_ell0 hk]
        have hsplit : p.numVerts ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
          rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
        have hjrec : j k p.numVerts = j k n + j k (ell0 k) + 3 := by
          have hr := j_rec_unfold_one hk hbaseR
          rw [← hn] at hr; exact hr
        -- lower bounds guarding ℕ-subtraction
        have hXn1 : 1 ≤ n ⌈/⌉ k := by
          rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
        have hXe1 : 1 ≤ ell0 k / k :=
          (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
        -- window step: split on whether the prefix is frontier-tight (σ(q) = 0)
        by_cases htight : j k n = (n - 1) + (n ⌈/⌉ k - 1) + excess q
        · -- frontier-tight prefix: (MF) supplies the full k − 2
          have hwin : excess q + (k - 2) ≤ excess p := by
            apply hMF p q hpe hqe hbaseR hpre
            rw [hqnv]; exact htight
          omega
        · -- bank ≥ 1: the proved k − 3 floor suffices
          have hfloor : excess q + (k - 3) ≤ excess p :=
            windowExcess_ge_km3 hk hpe hbaseR hpre
          omega
  intro q hqe h0
  have := main q.numVerts q hqe rfl
  omega

/-! ## Conditional Theorem 2 through the synthesis frontier -/

/-- **`thm2` conditional on (MF).**  The verbatim `Statements.thm2` conclusion
`j_k(ℓ) ≤ i_k(ℓ)` for every `ℓ`, given the single residual hypothesis `FrontierTightHeavy k`.
A sorry-free discharge of (MF) — which by the dossiers' §5 equivalence is exactly as hard as
Theorem 2 — would complete Theorem 2 for all `k`. -/
theorem thm2_of_MF {k ℓ : ℕ} (hk : 3 ≤ k) (hMF : FrontierTightHeavy k)
    (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (excessFrontier_of_MF hk hMF) hℓ

/-- **The global residual.**  `FrontierTightHeavy k` for every `k ≥ 3` — the single hypothesis
whose sorry-free discharge closes Theorem 2 (and, through the §6.2–§6.4 reduction spine, the
headline superpermutation bound) for all `k`. -/
def FrontierTightHeavyAll : Prop := ∀ k, 3 ≤ k → FrontierTightHeavy k

/-- **The wiring bridge to the reduction spine.**  From the global residual `FrontierTightHeavyAll`
this produces the exact `hthm2` hypothesis shape consumed by the §6 reductions
(`Hunter.Proved.thm1v2`, `thm1v1`, `prop4`, `proof_thm1v2`, …): `∀ k ℓ, 3 ≤ k →
HasExitlessPath k ℓ → j_k(ℓ) ≤ i_k(ℓ)`.  Composing this with those (already axiom-clean,
`hthm2`-carrying) `Hunter.Proved.*` deliverables and the *unconditionally proved*
`hthm2eq` (`Proved.thm2_equality`) yields the headline bound conditional on the single residual —
the capstone `_closed` chain the STATUS ledger keeps open only because `thm2` itself is open. -/
theorem thm2_global_of_MF (hMF : FrontierTightHeavyAll) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  fun k _ℓ hk hℓ => thm2_of_MF hk (hMF k hk) hℓ

/-! ## Lemma A — σ²-exclusion after a complete 2-loop (the α-characterization)

This is the genuine harvestable advance of the relative-exitless-lift dossier: the
vertex-distinctness proof that a weight-3 marker-preserving boundary leaving a **completely
traversed** marked 2-loop cannot be `sigmaSqWord`, hence is `alphaWord` — the α weight-3
equality-characterization everyone flagged as the hard open piece, resolved on the
complete-loop side.

**Setup.**  In an exitless path, a *complete 2-loop* rooted at block `t₀` is the maximal
door-run of `k − 1` consecutive blocks `t₀, t₀+1, …, t₀+(k−2)` (the confinement cap: a door-run
has ≤ `k − 1` blocks), all joined by weight-2 **door** boundaries.  The run-marker
`α₁ = (block t₀).getLastD 0` is the **last** symbol of every block-start along the run
(`marker_door_step`), and — since block-starts are duplicate-free permutation words — erasing
that last symbol is `dropLast` (`erase_getLastD`); so the marker-erased **meta-word** determines
the full block-start.  Along the door-run the meta-word rotates by exactly `1` per door
(`metaWord_door_block`), so block `t₀+r` has meta-word `u.rotate r`, where `u = (block t₀)`'s
meta-word has length `k − 1`.

**The σ²-exclusion.**  A `sigmaSqWord` terminator into the next block `t₀+(k−1)` advances the
meta-word by `rotate 2` (`metaWord_sigmaSq_block`), giving `u.rotate ((k−2)+2) = u.rotate k =
u.rotate 1` (since `|u| = k − 1`, `rotate_length`).  That is exactly the meta-word of block
`t₀+1`; and the σ² terminator also preserves the marker (`marker_sigmaSq_step`), so by the
meta-word ⇒ block-start reconstruction the σ² terminator **equals block-start `t₀+1`** — an
already-visited vertex.  But its path position `k·(t₀+(k−1))` differs from `k·(t₀+1)` (as
`k − 1 ≠ 1` for `k ≥ 3`), contradicting `HPath.Nodup` (`vert_inj`).  Hence `sigmaSqWord` is
impossible and the terminator is `alphaWord`.

**k = 5 verification (matches dossier Q-T2, 120/120).**  `|u| = 4`; complete door-run = `k−1 = 4`
blocks `t₀ … t₀+3` with meta-words `u.rot^0 … u.rot^3` (`k−2 = 3` doors).  A σ² terminator into
block `t₀+4` has meta-word `u.rot^{(3)+2} = u.rot^5 = u.rot^{5 mod 4} = u.rot^1` = the meta-word
of block `t₀+1` = **the 2nd block-start `A_1`** (already visited), so σ² is excluded — exactly
the dossier's "the `sigmaSqWord` terminator equals the 2nd block-start `A_1`" finding. -/

/-- Nonempty list reconstruction from its `dropLast` and last symbol. -/
theorem list_dropLast_getLastD (w : List ℕ) (hw : w ≠ []) :
    w = w.dropLast ++ [w.getLastD 0] := by
  rcases List.eq_nil_or_concat w with rfl | ⟨l, a, rfl⟩
  · exact absurd rfl hw
  · rw [List.concat_eq_append, List.dropLast_concat]; simp

/-- **Lemma A (σ²-exclusion core).**  In an exitless path, if blocks `t₀ … t₀+(k−2)` form a
complete door-run (`k − 1` blocks, all weight-2 boundaries) and the boundary into the next block
`t₀+(k−1)` lands on `sigmaSqWord`, a contradiction results: the σ² target is the already-visited
block-start `t₀+1`. -/
theorem lemmaA_sigmaSq_excluded (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ : ℕ)
    (hN : k * (t₀ + (k - 1)) < p.numVerts)
    (hdoor : ∀ r, 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2)
    (hσ : (p.vert (k * (t₀ + (k - 1))) : List ℕ)
        = sigmaSqWord (p.vert (k * (t₀ + (k - 1)) - 1))) :
    False := by
  have hk2 : 2 ≤ k := by omega
  set α₁ : ℕ := (p.vert (k * t₀) : List ℕ).getLastD 0 with hα1def
  set u : List ℕ := (p.vert (k * t₀) : List ℕ).erase α₁ with hudef
  -- `u = dropLast (block t₀)`, so `|u| = k − 1`
  have hu_drop : u = (p.vert (k * t₀) : List ℕ).dropLast := by
    rw [hudef, hα1def]; exact erase_getLastD (p.vert (k * t₀)).2.nodup
  have hulen : u.length = k - 1 := by
    rw [hu_drop, List.length_dropLast, (p.vert (k * t₀)).2.length]
  -- positions of run blocks are below `numVerts`
  have hpos : ∀ s, s ≤ k - 2 → k * (t₀ + s) < p.numVerts := by
    intro s hs
    have : k * (t₀ + s) ≤ k * (t₀ + (k - 1)) :=
      Nat.mul_le_mul (le_refl k) (by omega)
    omega
  -- the door-run: marker constancy + exact meta-word rotation
  have hrun : ∀ r, r ≤ k - 2 →
      (p.vert (k * (t₀ + r)) : List ℕ).getLastD 0 = α₁ ∧
      (p.vert (k * (t₀ + r)) : List ℕ).erase α₁ = u.rotate r := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [Nat.add_zero]
      · rw [Nat.add_zero, List.rotate_zero, hudef]
    | succ r ih =>
      intro hr
      obtain ⟨hmarkr, hmetar⟩ := ih (by omega)
      have hN' : k * (t₀ + (r + 1)) < p.numVerts := hpos (r + 1) (by omega)
      have hw : ew k (p.vert (k * (t₀ + (r + 1)) - 1)) (p.vert (k * (t₀ + (r + 1)))) = 2 :=
        hdoor (r + 1) (by omega) (by omega)
      have hmk : (p.vert (k * (t₀ + (r + 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega]; exact hmarkr
      refine ⟨?_, ?_⟩
      · exact marker_door_step hk2 hp (t := t₀ + (r + 1)) (by omega) hN' hw hmk
      · have hstep := metaWord_door_block hk2 hp (t := t₀ + (r + 1)) (by omega) hN' hw hmk
        rw [show t₀ + (r + 1) - 1 = t₀ + r from by omega, hmetar, List.rotate_rotate] at hstep
        exact hstep
  -- the σ² terminator's meta-word: `u.rotate k = u.rotate 1`
  have hrotk : u.rotate k = u.rotate 1 := by
    calc u.rotate k = u.rotate ((k - 1) + 1) := by congr 1; omega
      _ = (u.rotate (k - 1)).rotate 1 := (List.rotate_rotate u (k - 1) 1).symm
      _ = (u.rotate u.length).rotate 1 := by rw [hulen]
      _ = u.rotate 1 := by rw [List.rotate_length]
  obtain ⟨hmark_km2, hmeta_km2⟩ := hrun (k - 2) (le_refl _)
  have hmk_km2 : (p.vert (k * (t₀ + (k - 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
    rw [show t₀ + (k - 1) - 1 = t₀ + (k - 2) from by omega]; exact hmark_km2
  have hσstep := metaWord_sigmaSq_block hk hp (t := t₀ + (k - 1)) (by omega) hN hσ hmk_km2
  rw [show t₀ + (k - 1) - 1 = t₀ + (k - 2) from by omega, hmeta_km2, List.rotate_rotate,
      show (k - 2) + 2 = k from by omega, hrotk] at hσstep
  -- block `t₀+1` has the same meta-word `u.rotate 1`
  obtain ⟨hmark1, hmeta1⟩ := hrun 1 (by omega)
  have hmark_km1 : (p.vert (k * (t₀ + (k - 1))) : List ℕ).getLastD 0 = α₁ :=
    marker_sigmaSq_step hk hp (t := t₀ + (k - 1)) (by omega) (le_of_lt hN) hσ hmk_km2
  -- reconstruct: both block-starts have the same dropLast and end in α₁, so they are equal
  set A : List ℕ := (p.vert (k * (t₀ + 1)) : List ℕ) with hAdef
  set B : List ℕ := (p.vert (k * (t₀ + (k - 1))) : List ℕ) with hBdef
  have hAdrop : A.erase α₁ = A.dropLast := by
    rw [← hmark1]; exact erase_getLastD (p.vert (k * (t₀ + 1))).2.nodup
  have hBdrop : B.erase α₁ = B.dropLast := by
    rw [← hmark_km1]; exact erase_getLastD (p.vert (k * (t₀ + (k - 1)))).2.nodup
  have hdropeq : A.dropLast = B.dropLast := by
    rw [← hAdrop, ← hBdrop, hmeta1, hσstep]
  have hAne : A ≠ [] := by
    intro h; have hl := (p.vert (k * (t₀ + 1))).2.length; rw [← hAdef, h] at hl
    simp at hl; omega
  have hBne : B ≠ [] := by
    intro h; have hl := (p.vert (k * (t₀ + (k - 1)))).2.length; rw [← hBdef, h] at hl
    simp at hl; omega
  have hABlist : A = B :=
    calc A = A.dropLast ++ [A.getLastD 0] := list_dropLast_getLastD A hAne
      _ = B.dropLast ++ [B.getLastD 0] := by rw [hdropeq, hmark1, hmark_km1]
      _ = B := (list_dropLast_getLastD B hBne).symm
  have hVtxeq : p.vert (k * (t₀ + 1)) = p.vert (k * (t₀ + (k - 1))) :=
    Subtype.ext hABlist
  have hpos1 : k * (t₀ + 1) < p.numVerts := hpos 1 (by omega)
  have hidx : k * (t₀ + 1) = k * (t₀ + (k - 1)) := vert_inj p hpos1 hN hVtxeq
  have hcancel : t₀ + 1 = t₀ + (k - 1) := Nat.eq_of_mul_eq_mul_left (by omega) hidx
  omega

/-- **Lemma A (α-characterization).**  In an exitless path, a weight-3 marker-preserving boundary
leaving a **complete 2-loop** (a `k − 1`-block door-run) is `alphaWord`, never `sigmaSqWord`.
The σ² alternative is excluded by `lemmaA_sigmaSq_excluded` (vertex-distinctness), so the
`boundary_classify` / `weight3_marker_edge_cases` dichotomy collapses to `alphaWord`. -/
theorem lemmaA_alphaWord (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ : ℕ)
    (hN : k * (t₀ + (k - 1)) < p.numVerts)
    (hdoor : ∀ r, 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2)
    (hw : ew k (p.vert (k * (t₀ + (k - 1)) - 1)) (p.vert (k * (t₀ + (k - 1)))) = 3)
    (hmark : (p.vert (k * (t₀ + (k - 1))) : List ℕ).getLastD 0
        = (rho (p.vert (k * (t₀ + (k - 1)) - 1) : List ℕ)).getLastD 0) :
    (p.vert (k * (t₀ + (k - 1))) : List ℕ) = alphaWord (p.vert (k * (t₀ + (k - 1)) - 1)) := by
  have hkpos : 0 < k * (t₀ + (k - 1)) := by
    have : 0 < k := by omega
    have : 0 < t₀ + (k - 1) := by omega
    exact Nat.mul_pos (by omega) (by omega)
  have hi1 : k * (t₀ + (k - 1)) - 1 + 1 = k * (t₀ + (k - 1)) := by omega
  have hcases := weight3_marker_edge_cases hk (p := p) (i := k * (t₀ + (k - 1)) - 1)
    (by rw [hi1]; exact hw) (by rw [hi1]; exact hmark)
  rw [hi1] at hcases
  rcases hcases with hα | hσ
  · exact hα
  · exact absurd (lemmaA_sigmaSq_excluded hk hp t₀ hN hdoor hσ) (by simp)

end ProofsSynthesis

end Hunter

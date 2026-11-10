/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsDeficit

/-!
# Theorem 2 — the window inequality reduced to a pure heavy-edge count

`ProofsDeficit` collapsed the *entire* remaining content of Hunter's Theorem 2 to the single
uniform inequality `WindowExcess k`:

> for every exitless `p` with `|p| > k(k−1)(k−2)` and its exitless length-`(|p|−ℓ₀)` prefix `q`
> (`ℓ₀ = k(k−1)(k−2)−k`):  `excess q + (k−2) ≤ excess p`.

This file **sharpens that residue** by peeling off the `excess` abstraction.  `excess` is a
sum over the layers `r = 3,…,k` of the `≥r`-edge counts; the window inequality is really a
statement about the *first* layer only (`edgeCountGe · 3`, the count of weight-`≥3` edges).
We prove, sorry-free and axiom-clean:

* `edgeCountGe_prefix_le` — every `≥r`-edge count is monotone under taking a prefix.
* `windowExcess_of_windowHeavy3 : WindowHeavy3 k → WindowExcess k` — the reduction.  It uses
  only that the excess of the whole dominates the excess of the prefix *layer by layer*, so the
  extra `(k−2)` demanded of `excess` is already delivered by the `r = 3` layer alone.
* `thm2_of_windowHeavy3` — Theorem 2 for all `ℓ`, conditional on the sharpened residual.

The residual `WindowHeavy3 k` is:

> `edgeCountGe q 3 + (k−2) ≤ edgeCountGe p 3`

for the same `p`, `q` — i.e. **every `ℓ₀`-window of an exitless path contains at least `k−2`
edges of weight `≥3`.**  This is strictly cleaner than `WindowExcess`: no `excess`, no sum over
layers, a bare count of heavy edges in a window.  It is exactly the paper's cut-off claim
("`α` is the only 3-step that can be followed by `(k−2)` 2-steps") stated as a count.

`PROGRESS-window.md` records (a) the numerical `k=5` check that `k−2` is the right count,
(b) the level-2 machinery already delivers `k−3` of those `k−2`, so `WindowHeavy3` is the
eternal `+1` (the meta-confinement on `k−1` letters), and (c) a precise analysis of why the
meta-lift to an `HPath (k−1)` is *not* plain-`Exitless` and what would be needed to close it.

## Numerical sketch at `k = 5` (checked before proving; see `THM2-EVIDENCE.md`)

`k = 5`: `k(k−1)(k−2) = 60`, `ℓ₀ = 60 − 5 = 55`, `k−2 = 3`, `k−3 = 2`.
A window is `ℓ₀ = 55` edges = `55/5 = 11 = (k−1)(k−2)−1` blocks.  Level-2 (`prp_3edgebound`,
via the covering count `⌈ℓ₀/(k(k−1))⌉−1 = ⌈55/20⌉−1 = 3−1 = 2 = k−3`) forces `2` weight-`≥3`
edges per window.  `WindowHeavy3` demands `3 = k−2`: exactly one more.  `THM2-EVIDENCE.md`
measured the recursion gap `i₅−j₅ ∈ {0, +1}` with equality attained — i.e. `WindowHeavy3`
holds with the `≥` we need and no tightness miracle is required.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsWindow

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
  Proved
open HPath

variable {k : ℕ}

/-! ## Prefix stability of `vert` and monotonicity of the `≥r`-edge counts -/

/-- On the common index range, a prefix path agrees with the original: if `q.verts` is the
length-`n` prefix of `p.verts` then `q.vert i = p.vert i` for every `i < n`. -/
theorem prefix_vert_eq {p q : HPath k} {n : ℕ} (hn : q.verts = p.verts.take n)
    (hnle : n ≤ p.numVerts) {i : ℕ} (hi : i < n) : q.vert i = p.vert i := by
  have hNlen : p.verts.length = p.numVerts := rfl
  have hip : i < p.verts.length := by rw [hNlen]; omega
  have hiq : i < q.verts.length := by rw [hn, List.length_take]; omega
  show q.verts.getD i _ = p.verts.getD i _
  rw [List.getD_eq_getElem q.verts _ hiq, List.getD_eq_getElem p.verts _ hip]
  have : q.verts[i] = (p.verts.take n)[i]'(by rw [← hn]; exact hiq) := by
    congr 1
  rw [this, List.getElem_take]

/-- **Prefix-monotonicity of the `≥r`-edge count.**  If `q` is the length-`n` prefix of `p`
(and `q.numVerts = n`), then `edgeCountGe q r ≤ edgeCountGe p r` for every `r`: the window
`[n−1, |p|−2]` only adds edges. -/
theorem edgeCountGe_prefix_le {p q : HPath k} {n : ℕ} (hn : q.verts = p.verts.take n)
    (hnle : n ≤ p.numVerts) (hqn : q.numVerts = n) (r : ℕ) :
    edgeCountGe q r ≤ edgeCountGe p r := by
  rw [edgeCountGe, edgeCountGe, hqn]
  have hfeq :
      (Finset.range (n - 1)).filter (fun i => r ≤ ew k (q.vert i) (q.vert (i + 1)))
        = (Finset.range (n - 1)).filter (fun i => r ≤ ew k (p.vert i) (p.vert (i + 1))) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    rw [prefix_vert_eq hn hnle (show i < n by omega),
        prefix_vert_eq hn hnle (show i + 1 < n by omega)]
  rw [hfeq]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-! ## The sharpened residual and the reduction -/

/-- **The sharpened window inequality.**  Same data as `WindowExcess`, but at the level of the
bare heavy-edge count: every `ℓ₀`-window of an exitless path carries at least `k−2` edges of
weight `≥3` (`edgeCountGe q 3 + (k−2) ≤ edgeCountGe p 3`).

This is `WindowExcess` with the `excess`/multi-layer abstraction stripped away: a pure count of
weight-`≥3` edges, exactly the paper's "`α` is the only 3-step that can be followed by `(k−2)`
2-steps".  `windowExcess_of_windowHeavy3` shows it implies `WindowExcess`, hence (via
`thm2_of_windowExcess`) all of Theorem 2. -/
def WindowHeavy3 (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    edgeCountGe q 3 + (k - 2) ≤ edgeCountGe p 3

/-- **The reduction `WindowHeavy3 k → WindowExcess k`.**  `excess = Σ_{r=3}^{k} edgeCountGe·r`.
Each layer is prefix-monotone (`edgeCountGe_prefix_le`), so `excess p − excess q` dominates the
`r = 3` layer's contribution `edgeCountGe p 3 − edgeCountGe q 3`, which `WindowHeavy3` bounds
below by `k−2`.  Hence `excess q + (k−2) ≤ excess p`. -/
theorem windowExcess_of_windowHeavy3 (hk : 3 ≤ k) (hw : WindowHeavy3 k) :
    WindowExcess k := by
  intro p q hpe hqe hlt hprefix
  have hnle : p.numVerts - ell0 k ≤ p.numVerts := Nat.sub_le _ _
  have hqn : q.numVerts = p.numVerts - ell0 k := by
    have hlen : q.verts.length = (p.verts.take (p.numVerts - ell0 k)).length := by
      rw [hprefix]
    have hN : p.verts.length = p.numVerts := rfl
    rw [List.length_take, hN] at hlen
    show q.verts.length = _
    rw [hlen]; omega
  have hmono : ∀ r, edgeCountGe q r ≤ edgeCountGe p r :=
    fun r => edgeCountGe_prefix_le hprefix hnle hqn r
  have hres : edgeCountGe q 3 + (k - 2) ≤ edgeCountGe p 3 := hw p q hpe hqe hlt hprefix
  rw [excess, excess]
  have h3mem : (3 : ℕ) ∈ Finset.Icc 3 k := by rw [Finset.mem_Icc]; omega
  rw [← Finset.add_sum_erase _ (edgeCountGe p) h3mem,
      ← Finset.add_sum_erase _ (edgeCountGe q) h3mem]
  have hsum : ∑ r ∈ (Finset.Icc 3 k).erase 3, edgeCountGe q r
            ≤ ∑ r ∈ (Finset.Icc 3 k).erase 3, edgeCountGe p r :=
    Finset.sum_le_sum (fun r _ => hmono r)
  omega

/-- **thm2 conditional on the sharpened residual.**  Hunter's Theorem 2 for every `ℓ`,
assuming only `WindowHeavy3 k` ("each `ℓ₀`-window has `≥ k−2` heavy edges"). -/
theorem thm2_of_windowHeavy3 {k ℓ : ℕ} (hk : 3 ≤ k) (hw : WindowHeavy3 k)
    (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_windowExcess hk (windowExcess_of_windowHeavy3 hk hw) hℓ

/-! ## Reusable structural bricks for the (still-open) meta-confinement -/

/-- **Boundary edges are heavy-ish.**  At every block boundary (`k ∣ i+1`) of an exitless path
the edge weight is `≥ 2` (it leaves a fully-traversed 1-cycle, so it is not the `σ`-step). -/
theorem boundary_ge_two (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hin : i + 1 < p.numVerts) (hd : k ∣ (i + 1)) :
    2 ≤ ew k (p.vert i) (p.vert (i + 1)) := by
  have h1 := ew_ge_one hk (p.vert i) (p.vert (i + 1))
  have hne : ew k (p.vert i) (p.vert (i + 1)) ≠ 1 :=
    fun he => (prp_periodicedges hk hp hin).mp he hd
  omega

/-- **Every heavy edge is a block boundary.**  A weight-`≥3` (indeed weight-`≥2`) edge of an
exitless path sits at a block boundary (`k ∣ i+1`): the interior edges of a block are the
forced `σ`-steps of weight `1`.  This is the contrapositive of `prp_periodicedges`, and it is
what lets the heavy-edge count of `WindowHeavy3` be organised block by block (the meta level). -/
theorem heavy_is_boundary (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hin : i + 1 < p.numVerts) (hh : 2 ≤ ew k (p.vert i) (p.vert (i + 1))) :
    k ∣ (i + 1) := by
  by_contra hnd
  have he1 : ew k (p.vert i) (p.vert (i + 1)) = 1 := (prp_periodicedges hk hp hin).mpr hnd
  omega

end ProofsWindow

end Hunter

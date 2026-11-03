/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta

/-!
# Theorem 2 — the LANDING-SITE analysis of meta-heavy boundaries

This file carries out the **landing-site census** for Hunter's residual
`ProofsFinal.JumpLoopEntryFree`: after a *meta-heavy* boundary fires from a **complete** marked
2-loop, where can the new loop-entry word land?  Lemma A (`ProofsMeta.weight3_marker_cases`,
`ProofsSynthesis`) characterized the two *marker-preserving* weight-3 continuations
(`alphaWord` vs `sigmaSqWord`).  The residual killer boundary (`PROGRESS-drift` §3, the exact
`k = 6` block-25 configuration) is instead the **marker-MOVING** weight-3 meta-heavy leaving a
complete 2-loop — the one boundary shape Lemma A does *not* cover (a weight-`≥4` heavy pays
`+2` and is already excluded by `ProofsFinal.excessFrontier_of_jumpLoopEntryFree`; a
marker-preserving weight-3 leaving a complete loop is a complete-`α`, not a meta-heavy).

The new content here is the **weight-3 marker-moving classification** — the landing-word
algebra for that boundary:

* `weight3_markerMove_last` — a weight-3 successor `v` of `x` (overlap `x.drop 3 = v.take (k−3)`)
  whose last symbol is *not* the run marker `a = (rho x).getLastD 0` has its last symbol equal
  to one of the **two** other leading symbols `x₂` or `x₃` (`x.getD 1 0` or `x.getD 2 0`).  So a
  marker-move can send the marker to only **2** of the `k−2` candidate values — the exact
  computational census result (`scratchpad/campaign/landing/census.py`: "2 distinct new markers
  per source", verified for all sources at `k = 5, 6`).

## Honest scope — this does NOT close `JumpLoopEntryFree`

The census (`PROGRESS-landing.md`) settles the residual **negatively and precisely**, exactly as
every prior pass (LP, `sdisc`, `drift`, `rframe`, `final`):

* the landing IS constrained — the marker-move-from-a-complete-loop lemma above, plus the
  vertex-distinctness fact (computationally verified `k = 5, 6, 7`) that such a landing opens a
  2-loop **sharing one 1-cycle** with the source, hence door-completable only to depth `k−4`
  (structurally *incomplete*), the marker-moving analogue of Lemma A's α/σ² split;
* but this structure lives entirely in the **relative** level-`(k−1)` meta-rotation / vertex
  coordinate and is **decoupled** from the *absolute* demand-jump lattice.  The aligned cadence
  advances the block index by a fixed `k−1` per cycle, so `runStart mod (k−1)` is constant
  independent of every word choice; the `ℓ₀`-window folding makes the jump-block residues mixed
  (`{0,1}` at `k = 5, 6`).  No word invariant carries the absolute block coordinate, so the
  landing constraint cannot exclude the killer alignment.  The exclusion, if true, is the
  `HPath(k−1)` meta-lift (absolute-`R`) content, not word-algebraic.

Hence this file adds the *landing lemma* the census produced, sorry-free and axiom-clean, and
documents (it does **not** touch) the residual `ProofsFinal.JumpLoopEntryFree` and its capstone
chain.

Namespace `Hunter.ProofsLanding`.
-/

namespace Hunter

open List

namespace ProofsLanding

variable {k : ℕ}

/-- **Weight-3 marker-MOVING classification** (the marker-moving complement of
`ProofsMeta.weight3_marker_cases`).  A weight-3 successor `v` of `x` — sharing the defining
overlap `x.drop 3 = v.take (k − 3)` — whose last symbol is *not* the run marker
`a = (rho x).getLastD 0 = x₁` moves the marker to one of the **two** other leading symbols
`x₂ = x.getD 1 0` or `x₃ = x.getD 2 0`.  Thus a marker-move from a block-last word `x` can send
the marker to only 2 of the `k − 2` a-priori candidates — the exact `census.py` result. -/
theorem weight3_markerMove_last {x v : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x)
    (hv : IsPermWord k v) (hover : x.drop 3 = v.take (k - 3))
    (hmark : v.getLastD 0 ≠ (rho x).getLastD 0) :
    v.getLastD 0 = x.getD 1 0 ∨ v.getLastD 0 = x.getD 2 0 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, c, s, rfl⟩ : ∃ b c s, t = b :: c :: s := by
    rcases t with _ | ⟨b, _ | ⟨c, s⟩⟩
    · have := hx.length; simp at this; omega
    · have := hx.length; simp at this; omega
    · exact ⟨b, c, s, rfl⟩
  -- lengths and the leading-symbol computations
  have hxlen : (a :: b :: c :: s).length = k := hx.length
  have hslen : s.length = k - 3 := by simp at hxlen; omega
  have hdrop : (a :: b :: c :: s).drop 3 = s := rfl
  -- the marker is `a` (last symbol of `rho x`)
  have hrho : rho (a :: b :: c :: s) = (b :: c :: s) ++ [a] := by
    show (a :: b :: c :: s).rotate 1 = _; simp
  have hmarkval : (rho (a :: b :: c :: s)).getLastD 0 = a := by
    rw [hrho, show (b :: c :: s) ++ [a] = ((b :: c :: s) ++ [a]) by rfl, List.getLastD_concat]
  rw [hmarkval] at hmark
  -- the leading-symbol accessors
  have hg1 : (a :: b :: c :: s).getD 1 0 = b := rfl
  have hg2 : (a :: b :: c :: s).getD 2 0 = c := rfl
  rw [hg1, hg2]
  -- split `v = s ++ r` with `|r| = 3`
  set r := v.drop (k - 3) with hr
  have hvsplit : v = s ++ r := by
    conv_lhs => rw [← List.take_append_drop (k - 3) v]
    rw [← hover, hdrop]
  have hrlen : r.length = 3 := by rw [hr, List.length_drop, hv.length]; omega
  -- nodup facts
  have hnd : (a :: b :: c :: s).Nodup := hx.nodup
  have hab' : a ∉ (b :: c :: s) := (List.nodup_cons.mp hnd).1
  have hbcs : (b :: c :: s).Nodup := (List.nodup_cons.mp hnd).2
  have hbc' : b ∉ (c :: s) := (List.nodup_cons.mp hbcs).1
  have hcs : (c :: s).Nodup := (List.nodup_cons.mp hbcs).2
  have hcs' : c ∉ s := (List.nodup_cons.mp hcs).1
  have has : a ∉ s := fun h => hab' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hbs : b ∉ s := fun h => hbc' (List.mem_cons_of_mem _ h)
  -- destructure the length-3 tail block; its last entry is `v.getLastD 0`
  obtain ⟨x1, x2, x3, hxyz⟩ := List.length_eq_three.mp hrlen
  have hgl : v.getLastD 0 = x3 := by
    rw [hvsplit, hxyz, show s ++ [x1, x2, x3] = (s ++ [x1, x2]) ++ [x3] by simp,
        List.getLastD_concat]
  rw [hgl] at hmark ⊢
  -- `x3 ∈ v = x` as a symbol, and `x3 ∉ s`, so `x3 ∈ {a, b, c}`; `≠ a` gives `{b, c}`.
  have hsymbols : v.toFinset = (a :: b :: c :: s).toFinset := by
    rw [hv.toFinset_eq, hx.toFinset_eq]
  have hx3v : x3 ∈ v := by
    rw [hvsplit, hxyz]; exact List.mem_append_right _ (by simp)
  have hx3mem : x3 = a ∨ x3 = b ∨ x3 = c ∨ x3 ∈ s := by
    have hmem : x3 ∈ (a :: b :: c :: s) := by
      have : x3 ∈ v.toFinset := List.mem_toFinset.mpr hx3v
      rw [hsymbols, List.mem_toFinset] at this; exact this
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at hmem; exact hmem
  -- `x3 ∉ s`: `v` is nodup and `x3` sits in the tail block after `s`
  have hvnd : v.Nodup := hv.nodup
  have hx3ns : x3 ∉ s := by
    rw [hvsplit, hxyz] at hvnd
    have hdisj := (List.nodup_append.mp hvnd).2.2
    intro hmem
    exact hdisj x3 hmem x3 (by simp) rfl
  -- conclude
  rcases hx3mem with h | h | h | h
  · exact absurd h hmark
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hx3ns

/-- **Corollary — the marker-move reaches at most 2 markers.**  Restated as membership in the
2-element candidate list `[x₂, x₃]`: from any block-last word `x`, a marker-moving weight-3
boundary lands with its new marker in `[x.getD 1 0, x.getD 2 0]`.  Since this list has length 2,
a marker-move can send the run marker to only 2 of the `k − 2` candidate values. -/
theorem weight3_markerMove_mem {x v : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x)
    (hv : IsPermWord k v) (hover : x.drop 3 = v.take (k - 3))
    (hmark : v.getLastD 0 ≠ (rho x).getLastD 0) :
    v.getLastD 0 ∈ [x.getD 1 0, x.getD 2 0] := by
  have h := weight3_markerMove_last hk hx hv hover hmark
  rw [List.mem_cons, List.mem_cons]
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end ProofsLanding

end Hunter

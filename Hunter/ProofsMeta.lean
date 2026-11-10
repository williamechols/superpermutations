/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsDeficit

/-!
# Theorem 2 — the meta-confinement layer (`S'_k`, level ≥ 3)

This file builds the **meta-level** algebra behind Hunter's cut-off `S'_k`/`α` argument, the
last mathematically open piece of Theorem 2 (`ExcessFrontier k` in the recursion region).

Context established by the prior tracks (`ProofsSPrime`, `ProofsDeficit`, `Refutations`):

* `ExcessFrontier k → thm2` is fully proved (`ProofsRecursion.thm2_of_frontier`).
* The *per-window* reduction `WindowExcess k` is **FALSE** at `k = 5`
  (`Refutations.windowExcess_false`) — a single `ℓ₀`-window can carry only `k − 3` heavies,
  banking one unit of surplus.  Hence the frontier must be attacked **cumulatively** with an
  amortized potential, not window by window.
* The marker-erasure reduction is built (`ProofsSPrime.door_erase_marker`,
  `alpha_erase_marker`): a **door** boundary erases to `σ` on `k − 1` letters, an **α**
  boundary erases to `door` on `k − 1` letters.

The new content here is the **weight-3 boundary classification** and its marker-erasure — the
concrete "weight-3 at level `k` ↦ weight-2 at level `k − 1`" meta-contraction that
`alpha_erase_marker` only witnessed for the single `alphaWord` shape.  See `PROGRESS-meta.md`
for the amortized-invariant analysis and the corrected α-characterization.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
  Proved
open HPath

variable {k : ℕ}

/-! ## The weight-3 boundary word classification

Analogue of `ProofsConfinement.wt_two_word_cases` one weight-layer up.  A weight-3 successor
`v` of a block-last word `x` has the form `v = x.drop 3 ++ (a permutation of x.take 3)`: the
first `k − 3` symbols are shared and the leading three symbols of `x` reappear, permuted, at the
tail.  Among the six such arrangements, exactly the two that keep the level-2 **marker**
`α₁ = (rho x).getLastD 0` (the first symbol of `x`) as their last symbol survive as
run-continuing boundaries; those two are `alphaWord x` and the σ²-sibling `sigmaSqWord x`. -/

/-- The σ²-sibling of `alphaWord`: the *other* marker-preserving weight-3 successor.  Where
`alphaWord x = x.drop 3 ++ [x₃, x₂, x₁]` reverses the leading three, `sigmaSqWord` cyclically
shifts them, `sigmaSqWord x = x.drop 3 ++ [x₂, x₃, x₁]`.  Its marker-erasure is a `σ²`
(`rotate 2`) on `k − 1` letters (`sigmaSqWord_erase_marker`), the level-`(k−1)` weight-2
partner of the `door` produced by `alphaWord` (`ProofsSPrime.alpha_erase_marker`). -/
def sigmaSqWord (w : List ℕ) : List ℕ :=
  w.drop 3 ++ [w.getD 1 0, w.getD 2 0, w.getD 0 0]

/-- **Weight-3 marker-preserving classification.**  If `v` shares its first `k − 3` symbols with
`x.drop 3` (the defining overlap of a weight-3 successor) and keeps the marker
`α₁ = (rho x).getLastD 0 = x₁` as its last symbol, then `v` is either `alphaWord x` or its
σ²-sibling `sigmaSqWord x`.  These are the only two weight-3 boundaries that continue a
marker-fixed run; the other four move the marker and open a new meta-window. -/
theorem weight3_marker_cases {x v : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x)
    (hv : IsPermWord k v) (hover : x.drop 3 = v.take (k - 3))
    (hmark : v.getLastD 0 = (rho x).getLastD 0) :
    v = alphaWord x ∨ v = sigmaSqWord x := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, c, s, rfl⟩ : ∃ b c s, t = b :: c :: s := by
    rcases t with _ | ⟨b, _ | ⟨c, s⟩⟩
    · have := hx.length; simp at this; omega
    · have := hx.length; simp at this; omega
    · exact ⟨b, c, s, rfl⟩
  -- lengths and the drop/rho computations
  have hxlen : (a :: b :: c :: s).length = k := hx.length
  have hslen : s.length = k - 3 := by simp at hxlen; omega
  have hdrop : (a :: b :: c :: s).drop 3 = s := rfl
  -- the marker is `a` (last symbol of `rho x`)
  have hrho : rho (a :: b :: c :: s) = (b :: c :: s) ++ [a] := by
    show (a :: b :: c :: s).rotate 1 = _; simp
  have hmarkval : (rho (a :: b :: c :: s)).getLastD 0 = a := by
    rw [hrho, show (b :: c :: s) ++ [a] = ((b :: c :: s) ++ [a]) by rfl, List.getLastD_concat]
  rw [hmarkval] at hmark
  -- split `v = s ++ r` with `|r| = 3`, `r` a permutation of `{a,b,c}` ending in `a`
  set r := v.drop (k - 3) with hr
  have hvsplit : v = s ++ r := by
    conv_lhs => rw [← List.take_append_drop (k - 3) v]
    rw [← hover, hdrop]
  have hrlen : r.length = 3 := by rw [hr, List.length_drop, hv.length]; omega
  have hnd : (a :: b :: c :: s).Nodup := hx.nodup
  -- nodup facts about a, b, c, s
  have hab' : a ∉ (b :: c :: s) := (List.nodup_cons.mp hnd).1
  have hbcs : (b :: c :: s).Nodup := (List.nodup_cons.mp hnd).2
  have hbc' : b ∉ (c :: s) := (List.nodup_cons.mp hbcs).1
  have hcs : (c :: s).Nodup := (List.nodup_cons.mp hbcs).2
  have hcs' : c ∉ s := (List.nodup_cons.mp hcs).1
  have has : a ∉ s := fun h => hab' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hbs : b ∉ s := fun h => hbc' (List.mem_cons_of_mem _ h)
  have hbc : b ≠ c := fun h => hbc' (h ▸ List.mem_cons_self ..)
  -- b, c live in the tail block `r`
  have hsymbols : v.toFinset = (a :: b :: c :: s).toFinset := by
    rw [hv.toFinset_eq, hx.toFinset_eq]
  have hbr : b ∈ r := by
    have hbv : b ∈ v := by rw [← List.mem_toFinset, hsymbols]; simp
    rw [hvsplit, List.mem_append] at hbv
    exact hbv.resolve_left hbs
  have hcr : c ∈ r := by
    have hcv : c ∈ v := by rw [← List.mem_toFinset, hsymbols]; simp
    rw [hvsplit, List.mem_append] at hcv
    exact hcv.resolve_left hcs'
  -- destructure the length-3 block and pin its last entry to the marker `a`
  obtain ⟨x1, x2, x3, hxyz⟩ := List.length_eq_three.mp hrlen
  have hz : x3 = a := by
    have hgl : v.getLastD 0 = x3 := by
      rw [hvsplit, hxyz, show s ++ [x1, x2, x3] = (s ++ [x1, x2]) ++ [x3] by simp,
          List.getLastD_concat]
    rw [hgl] at hmark; exact hmark
  rw [hz] at hxyz
  have hxy : x1 ≠ x2 := by
    have hvnd : v.Nodup := hv.nodup
    rw [hvsplit, hxyz] at hvnd
    have := (List.nodup_append.mp hvnd).2.1
    rw [List.nodup_cons, List.nodup_cons] at this
    exact fun h => this.1 (by simp [h])
  rw [hxyz] at hbr hcr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr hcr
  -- b and c fill positions x1, x2 (each ≠ a); the two orders give the two shapes
  have hbne : b ≠ a := fun h => hab' (h ▸ List.mem_cons_self ..)
  have hcne : c ≠ a := fun h => hab' (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have halpha : alphaWord (a :: b :: c :: s) = s ++ [c, b, a] := by
    show (a :: b :: c :: s).drop 3 ++ ((a :: b :: c :: s).take 3).reverse = _
    rfl
  have hsig : sigmaSqWord (a :: b :: c :: s) = s ++ [b, c, a] := rfl
  rcases hbr with rfl | (rfl | hbfalse)
  · -- x1 = b; then c = x2 (the σ²-sibling)
    rcases hcr with hc1 | (rfl | hcfalse)
    · exact absurd hc1.symm hbc
    · right; rw [hvsplit, hxyz, hsig]
    · exact absurd hcfalse hcne
  · -- x2 = b; then c = x1 (alphaWord)
    rcases hcr with rfl | (hc2 | hcfalse)
    · left; rw [hvsplit, hxyz, halpha]
    · exact absurd hc2.symm hbc
    · exact absurd hcfalse hcne
  · exact absurd hbfalse hbne

/-- The σ²-sibling fixes the marker (last symbol of the block start), like `door` and `α`. -/
theorem sigmaSqWord_marker {x : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x) :
    (sigmaSqWord x).getLastD 0 = (rho x).getLastD 0 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, c, t'', rfl⟩ : ∃ b c t'', t = b :: c :: t'' := by
    rcases t with _ | ⟨b, _ | ⟨c, t''⟩⟩
    · have := hx.length; simp at this; omega
    · have := hx.length; simp at this; omega
    · exact ⟨b, c, t'', rfl⟩
  have hsig : sigmaSqWord (a :: b :: c :: t'') = t'' ++ [b, c, a] := rfl
  have hrho : rho (a :: b :: c :: t'') = (b :: c :: t'') ++ [a] := by
    show (a :: b :: c :: t'').rotate 1 = _; simp
  rw [hsig, hrho]
  rw [show t'' ++ [b, c, a] = (t'' ++ [b, c]) ++ [a] by simp, List.getLastD_concat,
      show (b :: c :: t'') ++ [a] = ((b :: c :: t'') ++ [a]) by rfl, List.getLastD_concat]

/-- **Marker-erasure of the σ²-sibling is `σ²` (`rotate 2`) on `k − 1` letters.**  The
level-`(k−1)` weight-2 partner of `ProofsSPrime.alpha_erase_marker` (which sends `alphaWord`
to `door`): the two marker-preserving weight-3 boundaries erase to the two weight-2 successors
on `k − 1` letters (`ProofsConfinement.wt_two_word_cases`). -/
theorem sigmaSqWord_erase_marker {x : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x) :
    (sigmaSqWord x).erase ((rho x).getLastD 0) =
      ((rho x).erase ((rho x).getLastD 0)).rotate 2 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, c, t'', rfl⟩ : ∃ b c t'', t = b :: c :: t'' := by
    rcases t with _ | ⟨b, _ | ⟨c, t''⟩⟩
    · have := hx.length; simp at this; omega
    · have := hx.length; simp at this; omega
    · exact ⟨b, c, t'', rfl⟩
  have hnd : (a :: b :: c :: t'').Nodup := hx.nodup
  have hrho : rho (a :: b :: c :: t'') = (b :: c :: t'') ++ [a] := by
    show (a :: b :: c :: t'').rotate 1 = _; simp
  have hmark : (rho (a :: b :: c :: t'')).getLastD 0 = a := by
    rw [hrho, show (b :: c :: t'') ++ [a] = ((b :: c :: t'') ++ [a]) by rfl,
        List.getLastD_concat]
  have hanbct : a ∉ (b :: c :: t'') := (List.nodup_cons.mp hnd).1
  have hrhoerase : (rho (a :: b :: c :: t'')).erase a = b :: c :: t'' := by
    rw [hrho, List.erase_append_right _ hanbct, List.erase_cons_head, List.append_nil]
  have hsig : sigmaSqWord (a :: b :: c :: t'') = t'' ++ [b, c, a] := rfl
  have hantcb : a ∉ (t'' ++ [b, c]) := by
    intro h; rw [List.mem_append] at h
    rcases h with h | h
    · exact hanbct (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    · simp at h
      rcases h with h | h
      · exact hanbct (h ▸ List.mem_cons_self ..)
      · exact hanbct (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hsigerase : (sigmaSqWord (a :: b :: c :: t'')).erase a = t'' ++ [b, c] := by
    rw [hsig, show t'' ++ [b, c, a] = (t'' ++ [b, c]) ++ [a] by simp,
        List.erase_append_right _ hantcb, List.erase_cons_head, List.append_nil]
  rw [hmark, hsigerase, hrhoerase]
  rw [List.rotate_eq_drop_append_take (by simp only [List.length_cons]; omega :
    2 ≤ (b :: c :: t'').length)]
  rfl

/-! ## The packaged meta-reduction: weight-3 at level `k` ↦ weight-2 at level `k − 1`

`ProofsSPrime.alpha_erase_marker` witnessed only the `alphaWord` shape.  Combined with the
classification above and the σ²-sibling erasure, we get the full dichotomy: a marker-preserving
weight-3 boundary erases to a **weight-2 successor on `k − 1` letters** — `door` iff it is the
`α` move, `σ²` (`rotate 2`) iff it is the sibling.  This is the corrected form of the handoff's
"weight-3 keeping meta-confinement is exactly `α`": the naive "erasure `= door` ⟹ `α`" is
*false* without marker-preservation (four of the six weight-3 shapes move the marker, and even
among the two marker-preserving shapes one erases to `σ²`, not `door`).  The genuine content is
this exact `wt_two_word_cases`-shaped dichotomy one level down. -/

/-- **Packaged meta-reduction (word level).**  A marker-preserving weight-3 successor `v` of `x`
erases (deleting the marker `α₁ = (rho x).getLastD 0`) to a weight-2 successor of
`u = (rho x).erase α₁` on `k − 1` letters: either `door u` (exactly when `v = alphaWord x`, the
meta-door) or `u.rotate 2` (exactly when `v = sigmaSqWord x`, the meta-`σ²`). -/
theorem weight3_marker_erase_cases {x v : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x)
    (hv : IsPermWord k v) (hover : x.drop 3 = v.take (k - 3))
    (hmark : v.getLastD 0 = (rho x).getLastD 0) :
    (v = alphaWord x ∧
        v.erase ((rho x).getLastD 0) = door ((rho x).erase ((rho x).getLastD 0)))
      ∨ (v = sigmaSqWord x ∧
        v.erase ((rho x).getLastD 0) = ((rho x).erase ((rho x).getLastD 0)).rotate 2) := by
  rcases weight3_marker_cases hk hx hv hover hmark with hα | hσ
  · exact Or.inl ⟨hα, by rw [hα]; exact alpha_erase_marker hk hx⟩
  · exact Or.inr ⟨hσ, by rw [hσ]; exact sigmaSqWord_erase_marker hk hx⟩

/-! ## Path-level meta-reduction (the meta-analogue of `door_of_boundary`)

For a path, `door_of_boundary` reads a weight-2 boundary edge as a `door` step.  Here a
weight-3 edge that keeps the marker is read as one of the two weight-3 shapes, and its
marker-erasure as the corresponding weight-2 meta-step — the entry point for constructing the
projected walk on `k − 1` letters. -/

/-- **Weight-3 boundary ⟹ shape dichotomy.**  In any path, a weight-3 edge `p.vert i →
p.vert (i+1)` whose target keeps the marker `(rho (p.vert i)).getLastD 0` is `alphaWord` or
`sigmaSqWord` of the source; its marker-erasure is `door` resp. `rotate 2` on `k − 1` letters.
(The overlap hypothesis of `weight3_marker_cases` is automatic from `wt_spec` at weight 3, and
marker-preservation already excludes the `σ³`-shape, so no boundary/`k ∣ i+1` hypothesis is
needed.) -/
theorem weight3_marker_edge_cases (hk : 3 ≤ k) {p : HPath k} {i : ℕ}
    (hw : ew k (p.vert i) (p.vert (i + 1)) = 3)
    (hmark : (p.vert (i + 1) : List ℕ).getLastD 0 = (rho (p.vert i : List ℕ)).getLastD 0) :
    (p.vert (i + 1) : List ℕ) = alphaWord (p.vert i) ∨
      (p.vert (i + 1) : List ℕ) = sigmaSqWord (p.vert i) := by
  have hk1 : 1 ≤ k := by omega
  have hu : IsPermWord k (p.vert i : List ℕ) := (p.vert i).2
  have hv : IsPermWord k (p.vert (i + 1) : List ℕ) := (p.vert (i + 1)).2
  have hew : wt k (p.vert i : List ℕ) (p.vert (i + 1) : List ℕ) = 3 := hw
  have hspec := (wt_spec (u := (p.vert i : List ℕ)) (v := (p.vert (i + 1) : List ℕ))
    hk1 (le_of_eq hu.length)).2.2
  rw [hew] at hspec
  exact weight3_marker_cases hk hu hv hspec hmark

/-! ## A relabeling-free brick for the meta level

`ProofsConfinement.genLoop_door_eq_genLoop_rho` — the core "`door` and `σ` land in the same
marked loop" identity that drives `confinement` — is stated with an `IsPermWord k` hypothesis
(symbols exactly `{1,…,k}`).  A **meta**-word (the marker-erasure of a block start) has length
`k − 1` and is duplicate-free, but its symbol set is `{1,…,k} ∖ {α₁}`, *not* `{1,…,k−1}` — so
the lemma cannot be applied one level down without relabeling.  Inspecting its proof, only the
cons-structure (`2 ≤ w.length`) is used; we re-state it with that hypothesis alone, so it
applies verbatim to meta-words.  This removes the single biggest friction flagged by
`PROGRESS-sprime` for lifting `confinement` to `k − 1` letters. -/

/-- **Length-only `genLoop` door/σ identity.**  `genLoop (door w) = genLoop (rho w)` for any
word with `2 ≤ |w|` — no `IsPermWord` needed.  Ready for meta-words on `k − 1` letters. -/
theorem genLoop_door_eq_rho_of_len {w : List ℕ} (hw : 2 ≤ w.length) :
    genLoop (door w) = genLoop (rho w) := by
  obtain ⟨a, b, s, rfl⟩ : ∃ a b s, w = a :: b :: s := by
    rcases w with _ | ⟨a, _ | ⟨b, s⟩⟩
    · simp at hw
    · simp at hw
    · exact ⟨a, b, s, rfl⟩
  have hrho : rho (a :: b :: s) = b :: s ++ [a] := by
    show (a :: b :: s).rotate 1 = _; simp
  have hdoor : door (a :: b :: s) = s ++ [b, a] := rfl
  rw [hrho, hdoor]
  unfold genLoop
  have h1 : (s ++ [b, a]).getLastD 0 = a := by
    have : s ++ [b, a] = (s ++ [b]) ++ [a] := by simp
    rw [this, List.getLastD_concat]
  have h2 : (b :: s ++ [a]).getLastD 0 = a := by
    have : b :: s ++ [a] = (b :: s) ++ [a] := by simp
    rw [this, List.getLastD_concat]
  have h3 : (s ++ [b, a]).dropLast = s ++ [b] := by
    have : s ++ [b, a] = (s ++ [b]) ++ [a] := by simp
    rw [this, List.dropLast_concat]
  have h4 : (b :: s ++ [a]).dropLast = b :: s := by
    have : b :: s ++ [a] = (b :: s) ++ [a] := by simp
    rw [this, List.dropLast_concat]
  rw [h1, h2, h3, h4]
  refine Prod.ext rfl ?_
  show rotClass (s ++ [b]) = rotClass (b :: s)
  apply Quotient.sound
  exact List.IsRotated.symm ⟨1, by simp⟩

/-! ## Path-level meta-word evolution (concrete meta-σ / meta-door steps for (b))

The marker-erasure of a block start is the **meta-word**.  These lemmas evolve it one boundary
at a time in a real path, providing the per-step "closure of the tracked structure" that a
level-`(k−1)` confinement needs:

* a **door** boundary (weight 2) advances the meta-word by `σ` (`rotate 1`) — `metaWord_door_step`;
* an **α** boundary (weight 3, marker preserved) advances it by `door` — `metaWord_alpha_step`.

`metaWord_door_step` is unconditional at a door boundary (`door_of_boundary` reads the edge, and
`door_erase_marker` erases it).  `metaWord_alpha_step` takes the `alphaWord` case of
`weight3_marker_edge_cases` (the `σ²`-sibling advances by `rotate 2` instead — the meta-heavy
alternative). -/

/-- **Meta-σ step.**  Across a door boundary the meta-word (marker-erasure of the block start)
advances by a single rotation, `σ` on `k − 1` letters. -/
theorem metaWord_door_step (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {i : ℕ}
    (hi : i + 1 < p.numVerts) (hd : k ∣ (i + 1))
    (hw : ew k (p.vert i) (p.vert (i + 1)) = 2) :
    (p.vert (i + 1) : List ℕ).erase ((rho (p.vert i : List ℕ)).getLastD 0) =
      ((rho (p.vert i : List ℕ)).erase ((rho (p.vert i : List ℕ)).getLastD 0)).rotate 1 := by
  rw [door_of_boundary hk hp hi hd hw]
  exact door_erase_marker hk (p.vert i).2

/-- **Meta-door step.**  Across an `α` boundary (a marker-preserving weight-3 edge that lands on
`alphaWord`) the meta-word advances by `door` on `k − 1` letters — the meta-level weight-2
successor.  The `σ²`-sibling alternative advances by `rotate 2` (`sigmaSqWord_erase_marker`). -/
theorem metaWord_alpha_step (hk : 3 ≤ k) {p : HPath k} {i : ℕ}
    (_hi : i + 1 < p.numVerts) (_hw : ew k (p.vert i) (p.vert (i + 1)) = 3)
    (_hmark : (p.vert (i + 1) : List ℕ).getLastD 0 = (rho (p.vert i : List ℕ)).getLastD 0)
    (hα : (p.vert (i + 1) : List ℕ) = alphaWord (p.vert i)) :
    (p.vert (i + 1) : List ℕ).erase ((rho (p.vert i : List ℕ)).getLastD 0) =
      door ((rho (p.vert i : List ℕ)).erase ((rho (p.vert i : List ℕ)).getLastD 0)) := by
  rw [hα]; exact alpha_erase_marker hk (p.vert i).2

end ProofsMeta

end Hunter


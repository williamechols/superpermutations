/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsExcess

/-!
# Theorem 2 — the contracted-graph `S'_k` confinement (level-3, the deficit bands)

This file attacks the single remaining open sub-goal of Hunter's Theorem 2: the frontier
inequality `ExcessFrontier k` on the *deficit* lengths of the recursion region (the width-`k`
bands after each multiple of `k(k−1)`), where the level-2 confinement (`prp_3edgebound`,
`excess_ge_Dbase`) falls short of the demand `D(ℓ)` by the deficit.

The mathematical content is the paper's cut-off `S'_k`/`τ'`/`α` argument (main_version.tex
§"On Exitless Paths", which literally ends mid-sentence at "Since α is the only 3-step which
can be followed by (k−2) 2-steps, there ∎").  See `PROGRESS-sprime.md` for the full analysis.

The concrete heart built here is the **marker-erasure reduction**: along a run of block
boundaries, erasing the level-2 marker (the last symbol, which door and α both fix) turns

* a door boundary (`τ'`, weight 2) into a *rotation* `σ` on the remaining `k−1` letters, and
* an `α` boundary (weight 3) into a *door* on the remaining `k−1` letters.

Hence a run of door/α block boundaries projects, under marker-erasure, to a `σ`/door walk on
`k−1` letters — the paper's "paths in `X` behave like paths on `k−1` letters".  The level-3
marked loop `Vset3` (from `ProofsExcess`) is exactly the preimage, under marker-erasure, of a
level-2 marked loop `Vset` on `k−1` letters, so the level-3 confinement is a level-2
confinement one meta-level up.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsSPrime

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess Proved
open HPath

variable {k : ℕ}

/-! ## The marker-erasure reduction: door ↦ σ, α ↦ door on `k−1` letters

Let `x` be the *last* vertex of a block (`x = σ^{k−1}(A)` for a block start `A`, so
`rho x = A`).  The marker is `α₁ = (rho x).getLastD 0`, the last symbol of the block start,
fixed by both the door and the `α` boundary.  Erasing `α₁` collapses the `k`-letter block-step
into a `(k−1)`-letter step: a door boundary becomes the rotation `σ`, an `α` boundary becomes a
`door`. -/

/-- The door boundary fixes the marker (last symbol of the block start). -/
theorem door_marker {x : List ℕ} (hk : 2 ≤ k) (hx : IsPermWord k x) :
    (door x).getLastD 0 = (rho x).getLastD 0 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, t', rfl⟩ : ∃ b t', t = b :: t' := by
    rcases t with _ | ⟨b, t'⟩
    · have := hx.length; simp at this; omega
    · exact ⟨b, t', rfl⟩
  have hdoor : door (a :: b :: t') = t' ++ [b, a] := rfl
  have hrho : rho (a :: b :: t') = (b :: t') ++ [a] := by
    show (a :: b :: t').rotate 1 = _; simp
  rw [hdoor, hrho]
  rw [show t' ++ [b, a] = (t' ++ [b]) ++ [a] by simp, List.getLastD_concat,
      show (b :: t') ++ [a] = ((b :: t') ++ [a]) by rfl, List.getLastD_concat]

/-- **Marker-erasure of the door boundary is `σ` on `k−1` letters.**  Erasing the marker
`α₁` from the door successor `door x` yields the single rotation of `(rho x).erase α₁`. -/
theorem door_erase_marker {x : List ℕ} (hk : 2 ≤ k) (hx : IsPermWord k x) :
    (door x).erase ((rho x).getLastD 0) =
      ((rho x).erase ((rho x).getLastD 0)).rotate 1 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, t', rfl⟩ : ∃ b t', t = b :: t' := by
    rcases t with _ | ⟨b, t'⟩
    · have := hx.length; simp at this; omega
    · exact ⟨b, t', rfl⟩
  have hnd : (a :: b :: t').Nodup := hx.nodup
  have hrho : rho (a :: b :: t') = (b :: t') ++ [a] := by
    show (a :: b :: t').rotate 1 = _; simp
  have hmark : (rho (a :: b :: t')).getLastD 0 = a := by
    rw [hrho, show (b :: t') ++ [a] = ((b :: t') ++ [a]) by rfl, List.getLastD_concat]
  have hanbt : a ∉ (b :: t') := (List.nodup_cons.mp hnd).1
  have hrhoerase : (rho (a :: b :: t')).erase a = b :: t' := by
    rw [hrho, List.erase_append_right _ hanbt, List.erase_cons_head, List.append_nil]
  have hdoor : door (a :: b :: t') = t' ++ [b, a] := rfl
  have hantb : a ∉ (t' ++ [b]) := by
    intro h; rw [List.mem_append] at h
    rcases h with h | h
    · exact hanbt (List.mem_cons_of_mem _ h)
    · simp at h; exact hanbt (h ▸ List.mem_cons_self ..)
  have hdoorerase : (door (a :: b :: t')).erase a = t' ++ [b] := by
    rw [hdoor, show t' ++ [b, a] = (t' ++ [b]) ++ [a] by simp,
        List.erase_append_right _ hantb, List.erase_cons_head, List.append_nil]
  rw [hmark, hdoorerase, hrhoerase]
  show t' ++ [b] = (b :: t').rotate 1
  simp

/-- The `α` boundary fixes the marker (last symbol of the block start). -/
theorem alpha_marker {x : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x) :
    (alphaWord x).getLastD 0 = (rho x).getLastD 0 := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hx.ne_nil (by omega))
  obtain ⟨b, c, t'', rfl⟩ : ∃ b c t'', t = b :: c :: t'' := by
    rcases t with _ | ⟨b, _ | ⟨c, t''⟩⟩
    · have := hx.length; simp at this; omega
    · have := hx.length; simp at this; omega
    · exact ⟨b, c, t'', rfl⟩
  have halpha : alphaWord (a :: b :: c :: t'') = t'' ++ [c, b, a] := rfl
  have hrho : rho (a :: b :: c :: t'') = (b :: c :: t'') ++ [a] := by
    show (a :: b :: c :: t'').rotate 1 = _; simp
  rw [halpha, hrho]
  rw [show t'' ++ [c, b, a] = (t'' ++ [c, b]) ++ [a] by simp, List.getLastD_concat,
      show (b :: c :: t'') ++ [a] = ((b :: c :: t'') ++ [a]) by rfl, List.getLastD_concat]

/-- **Marker-erasure of the `α` boundary is `door` on `k−1` letters.**  Erasing the marker
`α₁` from the `α` successor `alphaWord x` yields the door of `(rho x).erase α₁`. -/
theorem alpha_erase_marker {x : List ℕ} (hk : 3 ≤ k) (hx : IsPermWord k x) :
    (alphaWord x).erase ((rho x).getLastD 0) =
      door ((rho x).erase ((rho x).getLastD 0)) := by
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
  have halpha : alphaWord (a :: b :: c :: t'') = t'' ++ [c, b, a] := rfl
  have hantcb : a ∉ (t'' ++ [c, b]) := by
    intro h; rw [List.mem_append] at h
    rcases h with h | h
    · exact hanbct (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    · simp at h
      rcases h with h | h
      · exact hanbct (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact hanbct (h ▸ List.mem_cons_self ..)
  have halphaerase : (alphaWord (a :: b :: c :: t'')).erase a = t'' ++ [c, b] := by
    rw [halpha, show t'' ++ [c, b, a] = (t'' ++ [c, b]) ++ [a] by simp,
        List.erase_append_right _ hantcb, List.erase_cons_head, List.append_nil]
  rw [hmark, halphaerase, hrhoerase]
  show t'' ++ [c, b] = door (b :: c :: t'')
  rfl

/-! ## `Vset3` as the marker-erasure preimage of a level-2 loop on `k−1` letters

`mem_Vset3`/`mem_Vset` make this definitional, but the bridge makes the meta-level structure
explicit: a vertex lies in the marked 3-loop `(α₁,α₂,K)` iff its marker-erasure lies in the
marked 2-loop `(α₂,K)`.  Combined with `door_erase_marker`/`alpha_erase_marker`, this is what
makes a door/α block-run project to a `σ`/door walk on `k−1` letters. -/

/-- `v ∈ Vset3 k α₁ α₂ K` iff the marker-erasure `v.erase α₁` lies in the level-2 marked loop
`{ w | rotClass (w.erase α₂) = K }` (the `Vset` predicate on `k−1` letters). -/
theorem mem_Vset3_iff_erase {α₁ α₂ : ℕ} {K : RotClass} {v : Vtx k} :
    v ∈ Vset3 k α₁ α₂ K ↔ rotClass (((v : List ℕ).erase α₁).erase α₂) = K :=
  mem_Vset3

/-! ## The unconditional level-3 confinement (card bound on a `Vset3`-run)

Direct meta-level analog of `ProofsConfinement.confinement`: any set of vertices that all lie
in one marked 3-loop `Vset3` and represent pairwise-distinct 1-cycles has at most
`(k−1)(k−2)` elements, because their 1-cycles are `k` disjoint vertices each inside a set of
`≤ k(k−1)(k−2)` vertices.  This is the level-3 counterpart of the "`k` disjoint 1-cycles
cannot fit in a `k(k−1)`-vertex marked 2-loop" pigeonhole. -/

/-- **Level-3 confinement (cardinality form).**  A `Vset3`-confined set of blocks with
pairwise-distinct 1-cycles has `≤ (k−1)(k−2)` elements. -/
theorem card_le_of_mem_Vset3 (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass} {A : Vtx k}
    (hα1 : α₁ = (A : List ℕ).getLastD 0)
    (hα2 : α₂ = ((A : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((A : List ℕ).dropLast.dropLast))
    (S : Finset (Vtx k)) (hmem : ∀ v ∈ S, v ∈ Vset3 k α₁ α₂ K)
    (hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → rotClass (u : List ℕ) ≠ rotClass (v : List ℕ)) :
    S.card ≤ (k - 1) * (k - 2) := by
  have hk1 : 1 ≤ k := by omega
  set bigU : Finset (Vtx k) := S.biUnion (fun v => cyc v) with hbigU
  have hdisj' : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (cyc u) (cyc v) :=
    fun u hu v hv huv => cyc_disjoint (hdisj u hu v hv huv)
  have hcard : bigU.card = k * S.card := by
    rw [hbigU, Finset.card_biUnion hdisj',
        Finset.sum_congr rfl (fun v _ => card_cyc hk1 v), Finset.sum_const, smul_eq_mul,
        Nat.mul_comm]
  have hsub : bigU ⊆ Vset3 k α₁ α₂ K := by
    rw [hbigU]
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨v, hvS, hxv⟩ := hx
    exact cyc_subset_Vset3 hk1 (hmem v hvS) hxv
  have hVle : (Vset3 k α₁ α₂ K).card ≤ k * (k - 1) * (k - 2) :=
    card_Vset3_le (A := A) hk hα1 hα2 hK
  have hle : k * S.card ≤ k * (k - 1) * (k - 2) := by
    rw [← hcard]; exact le_trans (Finset.card_le_card hsub) hVle
  have hle2 : k * S.card ≤ k * ((k - 1) * (k - 2)) := by rw [← Nat.mul_assoc]; exact hle
  exact Nat.le_of_mul_le_mul_left hle2 (by omega)

/-! ## Precise localization of the residue: the frontier on the deficit bands only

The level-2 machinery (`excess_ge_Dbase` / `excess_frontier_of_j_le_jbase`) already discharges
the frontier at every length with `j_k(ℓ) ≤ jbase(ℓ)` (deficit 0) — the base region and the
large majority of the recursion region.  The ONLY residue is the deficit bands, where
`j_k(ℓ) > jbase(ℓ)`.  We name that residue exactly and show it is all that stands between the
proved machinery and a complete `thm2`.  This is the S'_k meta-confinement target above. -/

/-- **The deficit-band frontier** — the excess frontier restricted to the deficit lengths
(`j_k(ℓ) > jbase(ℓ)`, i.e. the width-`k` bands after each multiple of `k(k−1)`).  This is the
sole remaining open piece of Theorem 2; everything else is discharged by level-2 confinement. -/
def ExcessFrontierDeficit (k : ℕ) : Prop :=
  ∀ q : HPath k, q.Exitless → 0 < q.numVerts →
    q.numVerts + (q.numVerts ⌈/⌉ k) + (q.numVerts ⌈/⌉ (k * (k - 1))) - 3 < j k q.numVerts →
    j k q.numVerts ≤ (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q

/-- **The full frontier reduces to the deficit-band frontier.**  Combining the deficit-band
hypothesis with the unconditional level-2 bound (`excess_frontier_of_j_le_jbase`, deficit 0)
recovers `ExcessFrontier k` for all lengths. -/
theorem excessFrontier_of_deficit {k : ℕ} (hk : 3 ≤ k)
    (hdef : ExcessFrontierDeficit k) : ExcessFrontier k := by
  intro q hqe h0
  by_cases hb : j k q.numVerts ≤
      q.numVerts + (q.numVerts ⌈/⌉ k) + (q.numVerts ⌈/⌉ (k * (k - 1))) - 3
  · exact excess_frontier_of_j_le_jbase hk hqe h0 hb
  · exact hdef q hqe h0 (by omega)

/-- **thm2 from the deficit-band frontier.**  Hunter's Theorem 2 (`j_k(ℓ) ≤ i_k(ℓ)`, all `ℓ`)
follows from `ExcessFrontierDeficit k` alone — the deficit bands are the entire residue.
Discharging `ExcessFrontierDeficit` (via the S'_k meta-confinement of this file) would complete
Theorem 2 for every `k`. -/
theorem thm2_of_deficitFrontier {k ℓ : ℕ} (hk : 3 ≤ k)
    (hdef : ExcessFrontierDeficit k) (hex : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (excessFrontier_of_deficit hk hdef) hex

end ProofsSPrime

end Hunter

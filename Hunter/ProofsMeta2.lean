/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta

/-!
# Theorem 2 — the meta-path construction (level ≥ 3 confinement, part II)

This file continues `Hunter.ProofsMeta`, executing the meta-path construction pass:

* (i)   the **meta-run invariant**: the level-`(k−1)` `genLoop` of the block-start's meta-word
        is preserved across a *complete* 2-loop followed by an `α` (meta-door) boundary — the
        meta analogue of `ProofsConfinement.confinement`'s `hinv`;
* (ii)  **meta-no-reentry**: distinct 2-loops along an `α`-run carry pairwise-distinct 1-cycles;
* (iii) the **meta-pigeonhole**: an `α`-run confined in one meta-structure has `≤ k−2` complete
        2-loops;
* (iv)  the **amortized telescope** assembling `ExcessFrontier k`.

See `PROGRESS-meta2.md` for the running status and the precise frontier reached.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta2

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
  ProofsMeta Proved
open HPath

variable {k : ℕ}

/-! ## Word-level meta-invariant: `Vset3` membership under the two meta-moves

The meta-structure tracked along an `α`-run is the level-3 marked loop `Vset3 k α₁ α₂ K`
where `α₁` is the (run-constant) level-1 marker, and `(α₂, K)` is the level-`(k−1)` `genLoop`
of the **first** block-start's meta-word `A.erase α₁`.  The two meta-moves preserve this
membership:

* a **door** boundary rotates the meta-word (`metaWord_door_step`); `Vset3` membership is
  preserved because rotation fixes the doubly-erased rotation class
  (`rotClass_erase_rotate_one`) — `Vset3_of_metaWord_rotate`;
* a **complete 2-loop** (its `k−1` blocks rotate the meta-word by `k−2`) followed by an `α`
  (meta-door) boundary sends the meta-word to `door (w.rotate (k−2))` with `w` the 2-loop's
  first meta-word; since `|w| = k−1`, `ρ (w.rotate (k−2)) = w.rotate (k−1) = w`, so
  `genLoop (door (w.rotate (k−2))) = genLoop w` (`genLoop_door_eq_rho_of_len`) and membership
  is restored — `Vset3_of_metaWord_complete_alpha`. -/

/-- **Door meta-step preserves `Vset3`.**  If the meta-word (marker-erasure by the run-constant
`α₁`) of `B` is a single rotation of that of `A`, then `B` lies in the same level-3 marked loop
as `A`.  This is the meta analogue of `sigma_mem_Vset` (rotation-closure) for the door boundary. -/
theorem Vset3_of_metaWord_rotate {α₁ α₂ : ℕ} {K : RotClass} {A B : Vtx k}
    (hA : A ∈ Vset3 k α₁ α₂ K)
    (hstep : (B : List ℕ).erase α₁ = ((A : List ℕ).erase α₁).rotate 1) :
    B ∈ Vset3 k α₁ α₂ K := by
  rw [mem_Vset3] at hA ⊢
  rw [hstep, rotClass_erase_rotate_one (A.2.nodup.erase α₁)]
  exact hA

/-- **Complete-2-loop `α`-step preserves `Vset3`.**  Let `w = A.erase α₁` be the meta-word of
the 2-loop's first block (`|w| = k−1`), and `(α₂, K) = genLoop w` its level-`(k−1)` marked
loop.  After the 2-loop's `k−2` door boundaries the meta-word is `w.rotate (k−2)`, and the `α`
boundary sends it to `door (w.rotate (k−2)) = B.erase α₁`.  Then `B ∈ Vset3 k α₁ α₂ K`: the
completeness (`ρ (w.rotate (k−2)) = w`) restores the doubly-erased class to `K`. -/
theorem Vset3_of_metaWord_complete_alpha {α₁ α₂ : ℕ} {K : RotClass} {A B : Vtx k}
    (hk : 3 ≤ k)
    (hα2 : α₂ = ((A : List ℕ).erase α₁).getLastD 0)
    (hK : K = rotClass ((A : List ℕ).erase α₁).dropLast)
    (hlen : ((A : List ℕ).erase α₁).length = k - 1)
    (hstep : (B : List ℕ).erase α₁ = door (((A : List ℕ).erase α₁).rotate (k - 2))) :
    B ∈ Vset3 k α₁ α₂ K := by
  set w := (A : List ℕ).erase α₁ with hw
  -- `ρ (w.rotate (k-2)) = w` since `|w| = k-1`
  have hrot : (w.rotate (k - 2)).rotate 1 = w := by
    rw [List.rotate_rotate, show (k - 2) + 1 = k - 1 from by omega, ← hlen, List.rotate_length]
  have h2le : 2 ≤ (w.rotate (k - 2)).length := by rw [List.length_rotate, hlen]; omega
  -- `genLoop (door (w.rotate (k-2))) = genLoop w`
  have hgl : genLoop (door (w.rotate (k - 2))) = genLoop w := by
    rw [genLoop_door_eq_rho_of_len h2le]
    show genLoop ((w.rotate (k - 2)).rotate 1) = genLoop w
    rw [hrot]
  -- `u = B.erase α₁ = door (w.rotate (k-2))`, and it is nodup
  set u := (B : List ℕ).erase α₁ with hu
  have hunod : u.Nodup := B.2.nodup.erase α₁
  have hueq : u = door (w.rotate (k - 2)) := hstep
  have hglu : genLoop u = (α₂, K) := by
    rw [hueq, hgl, genLoop, ← hα2, ← hK]
  have humark : u.getLastD 0 = α₂ := congrArg Prod.fst hglu
  have huclass : rotClass u.dropLast = K := congrArg Prod.snd hglu
  rw [mem_Vset3, ← hu, ← humark, erase_getLastD hunod]
  exact huclass

/-! ## (i) The meta-run invariant — the `hinv` of `confinement`, one level up

The meta-block-starts of an `α`-run are the first block-starts `Astar j` of the successive
complete 2-loops.  Their meta-words evolve by the complete-2-loop `α`-step
`(Astar (j+1)).erase α₁ = door ((Astar j).erase α₁).rotate (k−2)`.  The invariant is that the
level-`(k−1)` `genLoop` of the meta-word is constant along the run — proved by induction with
`genLoop_door_eq_rho_of_len` and `ρ (w.rotate (k−2)) = w.rotate (k−1) = w` (`|w| = k−1`), the
exact shape of `ProofsConfinement.confinement`'s `hinv` (`genLoop_door_eq_genLoop_rho` there). -/

/-- **Meta-run `genLoop` invariant.**  Along an `α`-run of complete 2-loops, the level-`(k−1)`
`genLoop` of the meta-block-start's meta-word `(Astar j).erase α₁` is constant.  The `succ`
step is the complete-2-loop `α`-transition; completeness (`|w| = k−1 ⇒ w.rotate (k−1) = w`)
turns the `door`-successor's `genLoop` back into `genLoop w` via `genLoop_door_eq_rho_of_len`. -/
theorem meta_hinv {α₁ α₂ : ℕ} {K : RotClass} {Astar : ℕ → Vtx k} (hk : 3 ≤ k)
    (hlen : ∀ j, ((Astar j : List ℕ).erase α₁).length = k - 1)
    (hg0 : genLoop ((Astar 0 : List ℕ).erase α₁) = (α₂, K))
    (hstep : ∀ j, (Astar (j + 1) : List ℕ).erase α₁ =
        door (((Astar j : List ℕ).erase α₁).rotate (k - 2))) :
    ∀ j, genLoop ((Astar j : List ℕ).erase α₁) = (α₂, K) := by
  intro j
  induction j with
  | zero => exact hg0
  | succ j ih =>
    rw [hstep j]
    have hrot : (((Astar j : List ℕ).erase α₁).rotate (k - 2)).rotate 1 =
        (Astar j : List ℕ).erase α₁ := by
      rw [List.rotate_rotate, show (k - 2) + 1 = k - 1 from by omega, ← hlen j, List.rotate_length]
    have h2le : 2 ≤ (((Astar j : List ℕ).erase α₁).rotate (k - 2)).length := by
      rw [List.length_rotate, hlen j]; omega
    rw [genLoop_door_eq_rho_of_len h2le]
    show genLoop ((((Astar j : List ℕ).erase α₁).rotate (k - 2)).rotate 1) = (α₂, K)
    rw [hrot]; exact ih

/-- A vertex whose meta-word has level-`(k−1)` `genLoop` `(α₂, K)` lies in the level-3 marked
loop `Vset3 k α₁ α₂ K`.  (The meta analogue of `mem_Vset_of_genLoop`.) -/
theorem mem_Vset3_of_genLoop_metaWord {α₁ α₂ : ℕ} {K : RotClass} {A : Vtx k}
    (h : genLoop ((A : List ℕ).erase α₁) = (α₂, K)) : A ∈ Vset3 k α₁ α₂ K := by
  rw [mem_Vset3]
  have h1 : ((A : List ℕ).erase α₁).getLastD 0 = α₂ := congrArg Prod.fst h
  have h2 : rotClass ((A : List ℕ).erase α₁).dropLast = K := congrArg Prod.snd h
  rw [← h1, erase_getLastD (A.2.nodup.erase α₁)]
  exact h2

/-- **Meta-block-starts are confined.**  Combining `meta_hinv` with membership: every
meta-block-start of the `α`-run lies in one level-3 marked loop `Vset3 k α₁ α₂ K`. -/
theorem meta_hinv_mem_Vset3 {α₁ α₂ : ℕ} {K : RotClass} {Astar : ℕ → Vtx k} (hk : 3 ≤ k)
    (hlen : ∀ j, ((Astar j : List ℕ).erase α₁).length = k - 1)
    (hg0 : genLoop ((Astar 0 : List ℕ).erase α₁) = (α₂, K))
    (hstep : ∀ j, (Astar (j + 1) : List ℕ).erase α₁ =
        door (((Astar j : List ℕ).erase α₁).rotate (k - 2))) :
    ∀ j, Astar j ∈ Vset3 k α₁ α₂ K :=
  fun j => mem_Vset3_of_genLoop_metaWord (meta_hinv hk hlen hg0 hstep j)

/-- **Intra-2-loop confinement.**  Every block-start of a 2-loop has meta-word a rotation of
the 2-loop's first meta-word (successive door boundaries rotate it), so it lies in the same
level-3 marked loop.  (Rotation preserves the doubly-erased class, `rotClass_erase_rotate`.) -/
theorem Vset3_of_metaWord_rotate_iter {α₁ α₂ : ℕ} {K : RotClass} {A B : Vtx k} {r : ℕ}
    (hA : A ∈ Vset3 k α₁ α₂ K)
    (hstep : (B : List ℕ).erase α₁ = ((A : List ℕ).erase α₁).rotate r) :
    B ∈ Vset3 k α₁ α₂ K := by
  rw [mem_Vset3] at hA ⊢
  rw [hstep, rotClass_erase_rotate (A.2.nodup.erase α₁) r]
  exact hA

/-! ## (iii) The meta-pigeonhole — `≤ k−2` complete 2-loops per `α`-run

The level-3 marked loop has a budget of `(k−1)(k−2)` one-cycles (`card_le_of_mem_Vset3`).  An
`α`-run of `m` **complete** 2-loops confines `(k−1)·m` pairwise-distinct 1-cycles (each 2-loop
has `k−1` fresh blocks, by meta-no-reentry), all in one `Vset3`.  Hence `(k−1)·m ≤ (k−1)(k−2)`,
so `m ≤ k−2`. -/

/-- **Meta-pigeonhole.**  If the `k−1` block-starts of each of `m` complete 2-loops of an
`α`-run all lie in one level-3 marked loop `Vset3 k α₁ α₂ K` (markers/class read off a base
word `A`) and carry pairwise-distinct 1-cycles, then the number of complete 2-loops is
`m ≤ k−2`.  (`(k−1)·m` distinct 1-cycles in a `(k−1)(k−2)`-cycle budget.) -/
theorem meta_pigeonhole (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass} {A : Vtx k}
    (hα1 : α₁ = (A : List ℕ).getLastD 0)
    (hα2 : α₂ = ((A : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((A : List ℕ).dropLast.dropLast))
    {m : ℕ} (blk : Fin m × Fin (k - 1) → Vtx k)
    (hmem : ∀ i, blk i ∈ Vset3 k α₁ α₂ K)
    (hcyc : ∀ i i', i ≠ i' → rotClass (blk i : List ℕ) ≠ rotClass (blk i' : List ℕ)) :
    m ≤ k - 2 := by
  classical
  have hinj : Function.Injective blk := fun i i' h => by
    by_contra hne; exact hcyc i i' hne (by rw [h])
  set S : Finset (Vtx k) := Finset.univ.image blk with hS
  have hScard : S.card = m * (k - 1) := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
  have hmemS : ∀ v ∈ S, v ∈ Vset3 k α₁ α₂ K := by
    intro v hv; rw [hS, Finset.mem_image] at hv
    obtain ⟨i, _, rfl⟩ := hv; exact hmem i
  have hdisjS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      rotClass (u : List ℕ) ≠ rotClass (v : List ℕ) := by
    intro u hu v hv huv
    rw [hS, Finset.mem_image] at hu hv
    obtain ⟨i, _, rfl⟩ := hu; obtain ⟨i', _, rfl⟩ := hv
    exact hcyc i i' (fun h => huv (by rw [h]))
  have hcard := card_le_of_mem_Vset3 hk hα1 hα2 hK S hmemS hdisjS
  rw [hScard, show (k - 1) * (k - 2) = (k - 2) * (k - 1) from Nat.mul_comm _ _] at hcard
  exact Nat.le_of_mul_le_mul_right hcard (by omega)

/-! ## (ii) Meta-no-reentry — distinct 2-loops carry distinct 1-cycles

Level-1 `no_reentry` (a spent 1-cycle is never re-entered) lifts to the meta level: block-starts
at strictly-increasing block positions carry pairwise-distinct 1-cycles.  This is exactly the
`hcyc` distinctness hypothesis the meta-pigeonhole needs, discharged along the path. -/

/-- **Meta-no-reentry (position form).**  Block-starts of an exitless path at a family of
strictly-increasing block positions (multiples of `k`, at least `k` apart) carry
pairwise-distinct 1-cycles. -/
theorem meta_no_reentry (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {ι : Type*}
    [LinearOrder ι] (pos : ι → ℕ) (hdvd : ∀ i, k ∣ pos i)
    (hmono : ∀ i i', i < i' → pos i + k ≤ pos i')
    (hlt : ∀ i, pos i < p.numVerts) :
    ∀ i i', i ≠ i' →
      rotClass (p.vert (pos i) : List ℕ) ≠ rotClass (p.vert (pos i') : List ℕ) := by
  intro i i' hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact no_reentry hk hp (hdvd i) (hmono i i' h) (hlt i')
  · exact (no_reentry hk hp (hdvd i') (hmono i' i h) (hlt i)).symm

/-! ## The capstone: meta-confinement (`≤ k−2` complete 2-loops per `α`-run)

Assembling (i)+(ii)+(iii): the meta-block-starts `Astar j` of the run evolve their meta-words by
the complete-2-loop `α`-transition (`hstep`), so by `meta_hinv` their level-`(k−1)` `genLoop` is
constant — all lie in one `Vset3` (i).  Every block `blk (j, r)` of 2-loop `j` has meta-word
`(Astar j).erase α₁` rotated by `r`, so it too lies in that `Vset3` (intra-2-loop rotation
closure).  With the `(k−1)·m` blocks carrying pairwise-distinct 1-cycles (`hcyc`, from
meta-no-reentry (ii)), the pigeonhole (iii) forces `m ≤ k−2`.

This is `ProofsConfinement.confinement` lifted one meta-level: there, `k` blocks in a
`k(k−1)`-vertex `Vset` is impossible; here, `k−1` complete 2-loops (`(k−1)²` blocks) in a
`k(k−1)(k−2)`-vertex `Vset3` is impossible. -/

/-- **Meta-confinement.**  An `α`-run of `m` complete 2-loops, whose meta-block-starts obey the
complete-2-loop `α`-transition (`hstep`) and whose blocks obey the intra-2-loop rotation
relation (`hblk`) with pairwise-distinct 1-cycles (`hcyc`), has `m ≤ k−2`.  The markers `α₁, α₂`
and class `K` are read off the run's first block-start `Astar 0`. -/
theorem meta_confinement (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass}
    {Astar : ℕ → Vtx k} {m : ℕ} (blk : Fin m × Fin (k - 1) → Vtx k)
    (hα1 : α₁ = (Astar 0 : List ℕ).getLastD 0)
    (hα2 : α₂ = ((Astar 0 : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((Astar 0 : List ℕ).dropLast.dropLast))
    (hlen : ∀ j, ((Astar j : List ℕ).erase α₁).length = k - 1)
    (hstep : ∀ j, (Astar (j + 1) : List ℕ).erase α₁ =
        door (((Astar j : List ℕ).erase α₁).rotate (k - 2)))
    (hblk : ∀ i : Fin m × Fin (k - 1),
        (blk i : List ℕ).erase α₁ = ((Astar i.1 : List ℕ).erase α₁).rotate i.2)
    (hcyc : ∀ i i', i ≠ i' → rotClass (blk i : List ℕ) ≠ rotClass (blk i' : List ℕ)) :
    m ≤ k - 2 := by
  have herase0 : (Astar 0 : List ℕ).erase α₁ = (Astar 0 : List ℕ).dropLast := by
    rw [hα1, erase_getLastD (Astar 0).2.nodup]
  have hg0 : genLoop ((Astar 0 : List ℕ).erase α₁) = (α₂, K) := by
    rw [herase0, genLoop, ← hα2, ← hK]
  have hmemStar : ∀ j, Astar j ∈ Vset3 k α₁ α₂ K := meta_hinv_mem_Vset3 hk hlen hg0 hstep
  have hmemBlk : ∀ i : Fin m × Fin (k - 1), blk i ∈ Vset3 k α₁ α₂ K := fun i =>
    Vset3_of_metaWord_rotate_iter (hmemStar i.1) (hblk i)
  exact meta_pigeonhole hk hα1 hα2 hK blk hmemBlk hcyc

/-! ## The σ²-sibling budget check (decisive: it does NOT break the meta frame)

Task (iii) flagged the σ²-sibling as needing its own budget analysis: a marker-preserving
weight-3 boundary need not be the meta-door `α` (`alphaWord`) — it can be the sibling
`sigmaSqWord`, whose marker-erasure is `rotate 2` on `k−1` letters (`sigmaSqWord_erase_marker`),
i.e. a **meta-`σ²`**.  Since `rotate 2` is a rotation, it preserves the doubly-erased class
(`rotClass_erase_rotate`) and hence `Vset3` membership: the σ²-sibling **stays inside** the same
meta-structure.  It advances the meta-word within the current meta-1-cycle (consuming meta-budget
like two door-steps) and does NOT open a new 2-loop — while additionally paying `1` unit of
`≥3`-weight excess.  So the σ²-sibling is *favorable* for the frontier (extra banked excess, no
lost confinement) and introduces **no hole** in the meta-genLoop frame. -/

/-- **σ²-sibling stays confined.**  If the previous block-start `σx` (`= ρx`) lies in the level-3
marked loop and `B` is the `sigmaSqWord` successor, then `B` is still in the same `Vset3`: the
meta-`σ²` (`rotate 2`) preserves the doubly-erased rotation class.  Hence the σ²-sibling does not
break the meta-run invariant. -/
theorem Vset3_of_sigmaSq_step {α₁ α₂ : ℕ} {K : RotClass} {x B : Vtx k} (hk : 3 ≤ k)
    (hA : sigma x ∈ Vset3 k α₁ α₂ K)
    (hα1 : α₁ = (sigma x : List ℕ).getLastD 0)
    (hB : (B : List ℕ) = sigmaSqWord (x : List ℕ)) :
    B ∈ Vset3 k α₁ α₂ K := by
  have hsx : (sigma x : List ℕ) = rho (x : List ℕ) := rfl
  have hstep : (B : List ℕ).erase α₁ = ((sigma x : List ℕ).erase α₁).rotate 2 := by
    conv_rhs => rw [hsx]
    rw [hB, hα1, hsx, sigmaSqWord_erase_marker hk x.2]
  exact Vset3_of_metaWord_rotate_iter hA hstep

end ProofsMeta2

end Hunter

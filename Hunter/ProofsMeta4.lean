/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta3

/-!
# Theorem 2 — the RUN EXTRACTION layer (level ≥ 3 confinement, part IV)

This file continues `Hunter.ProofsMeta2`/`Hunter.ProofsMeta3`.  It builds the bridge from an
*actual exitless path* to `ProofsMeta2.meta_confinement`: given a maximal α-run of complete
2-loops inside an exitless path, it manufactures the `hstep`/`hblk`/`hcyc`/`hlen` inputs and
concludes the run-length bound `m ≤ k − 2` at path level (`alpha_run_bound`), then packages
the per-run excess seed for the telescope (`runs_pay`).

The crux is the **marker reconciliation**: `metaWord_door_step`/`metaWord_alpha_step` speak of
the *dynamic* per-step marker `(rho (p.vert i)).getLastD 0`, whereas `meta_confinement` wants a
*fixed* run-marker `α₁`.  The resolution formalized here: at every block-boundary of a
marker-preserving run the dynamic marker equals the *previous block-start's last symbol*
(`rho_boundary_prev`), and both the door step and the α step *preserve* that symbol
(`marker_door_step` / `marker_alpha_step`).  Hence along the whole run the dynamic marker is the
constant `α₁`, and the exact-word `hstep`/`hblk` identities hold with `α₁` fixed.

See `PROGRESS-meta4.md` for the running status.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta4

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
  ProofsMeta ProofsMeta2 Proved
open HPath

variable {k : ℕ}

/-! ## Word-level micro-lemmas: last symbol of `door`/`rho` -/

/-- The last symbol of `door w` is the head `w[0]` of `w`. -/
theorem door_getLastD (w : List ℕ) : (door w).getLastD 0 = w.getD 0 0 := by
  show (w.drop 2 ++ [w.getD 1 0, w.getD 0 0]).getLastD 0 = w.getD 0 0
  rw [show w.drop 2 ++ [w.getD 1 0, w.getD 0 0]
        = (w.drop 2 ++ [w.getD 1 0]) ++ [w.getD 0 0] from by simp, List.getLastD_concat]

/-- The last symbol of `rho w = w.rotate 1` is the head `w[0]` of `w`. -/
theorem rho_getLastD (w : List ℕ) : (rho w).getLastD 0 = w.getD 0 0 := by
  cases w with
  | nil => rfl
  | cons a s =>
    show ((a :: s).rotate 1).getLastD 0 = a
    rw [show (a :: s).rotate 1 = s ++ [a] from by simp, List.getLastD_concat]

/-! ## The boundary-source ↦ previous-block-start identity

At the boundary edge into block `t` (source position `k·t − 1`, the last vertex of block
`t − 1`), rotating the source by one lands exactly on the previous block start `p.vert(k·(t−1))`.
This is what turns the *dynamic* marker `(rho (p.vert (k·t−1))).getLastD 0` into the previous
block-start's marker — the key to the marker reconciliation. -/

/-- Rotating a length-`k` vertex word by `k` is the identity. -/
theorem rotate_len_eq (v : Vtx k) : (v : List ℕ).rotate k = v := by
  have hrl : (v : List ℕ).rotate k = (v : List ℕ).rotate (v : List ℕ).length := by
    rw [v.2.length]
  rw [hrl, List.rotate_length]

/-- **Boundary rho.**  For an exitless path, `rho (p.vert (k·t − 1)) = p.vert (k·(t − 1))`
(the last vertex of block `t − 1` rotated once is the block start). -/
theorem rho_boundary_prev (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hN : k * t ≤ p.numVerts) :
    (rho (p.vert (k * t - 1) : List ℕ)) = (p.vert (k * (t - 1)) : List ℕ) := by
  have hkt : 0 < k * t := Nat.mul_pos (by omega) (by omega)
  have hmul : k * t = k * (t - 1) + k := by
    conv_lhs => rw [show t = (t - 1) + 1 from by omega]
    rw [Nat.mul_succ]
  have heq : k * (t - 1) + (k - 1) = k * t - 1 := by omega
  have hlt : k * (t - 1) + (k - 1) < p.numVerts := by rw [heq]; omega
  have hbc := block_is_full_cycle hk hp (⟨t - 1, rfl⟩ : k ∣ k * (t - 1)) (by omega : k - 1 < k) hlt
  rw [heq] at hbc
  show (p.vert (k * t - 1) : List ℕ).rotate 1 = (p.vert (k * (t - 1)) : List ℕ)
  rw [hbc, sigma_iter_val, List.rotate_rotate, show (k - 1) + 1 = k from by omega]
  exact rotate_len_eq _

/-! ## Block-level meta-word and marker steps (dynamic marker reconciled to `α₁`) -/

/-- **Meta-σ block step (fixed marker).**  Across a weight-2 (door) boundary into block `t`,
if the previous block-start's marker is `α₁`, the meta-word advances by `rotate 1` — stated with
the *fixed* `α₁`, not the dynamic marker. -/
theorem metaWord_door_block (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts)
    (hw : ew k (p.vert (k * t - 1)) (p.vert (k * t)) = 2)
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).erase α₁ = ((p.vert (k * (t - 1)) : List ℕ).erase α₁).rotate 1 := by
  have hk1 : 1 ≤ k := by omega
  have hkt : 0 < k * t := Nat.mul_pos (by omega) (by omega)
  have hi1 : k * t - 1 + 1 = k * t := by omega
  have hrho := rho_boundary_prev hk1 hp ht (by omega : k * t ≤ p.numVerts)
  have hdyn : (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0 = α₁ := by rw [hrho]; exact hmk
  have hstep := metaWord_door_step hk hp (i := k * t - 1) (by rw [hi1]; exact hN)
    (by rw [hi1]; exact ⟨t, rfl⟩) (by rw [hi1]; exact hw)
  rw [hi1, hdyn, hrho] at hstep
  exact hstep

/-- **Meta-door block step (fixed marker).**  Across an α boundary into block `t` (weight-3,
marker-preserving, landing on `alphaWord`), if the previous block-start's marker is `α₁`, the
meta-word advances by `door` — stated with the fixed `α₁`. -/
theorem metaWord_alpha_block (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts)
    (hw : ew k (p.vert (k * t - 1)) (p.vert (k * t)) = 3)
    (hmark : (p.vert (k * t) : List ℕ).getLastD 0
      = (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0)
    (hα : (p.vert (k * t) : List ℕ) = alphaWord (p.vert (k * t - 1) : List ℕ))
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).erase α₁ = door ((p.vert (k * (t - 1)) : List ℕ).erase α₁) := by
  have hk1 : 1 ≤ k := by omega
  have hkt : 0 < k * t := Nat.mul_pos (by omega) (by omega)
  have hi1 : k * t - 1 + 1 = k * t := by omega
  have hrho := rho_boundary_prev hk1 hp ht (by omega : k * t ≤ p.numVerts)
  have hdyn : (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0 = α₁ := by rw [hrho]; exact hmk
  have hstep := metaWord_alpha_step hk (i := k * t - 1) (by rw [hi1]; exact hN)
    (by rw [hi1]; exact hw) (by rw [hi1]; exact hmark) (by rw [hi1]; exact hα)
  rw [hi1, hdyn, hrho] at hstep
  exact hstep

/-- **Door preserves the block marker.**  A weight-2 boundary into block `t` keeps the
block-start's last symbol equal to the previous block-start's (`= α₁`). -/
theorem marker_door_step (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts)
    (hw : ew k (p.vert (k * t - 1)) (p.vert (k * t)) = 2)
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).getLastD 0 = α₁ := by
  have hk1 : 1 ≤ k := by omega
  have hkt : 0 < k * t := Nat.mul_pos (by omega) (by omega)
  have hi1 : k * t - 1 + 1 = k * t := by omega
  have hrho := rho_boundary_prev hk1 hp ht (by omega : k * t ≤ p.numVerts)
  have hdoor := door_of_boundary hk hp (i := k * t - 1) (by rw [hi1]; exact hN)
    (by rw [hi1]; exact ⟨t, rfl⟩) (by rw [hi1]; exact hw)
  rw [hi1] at hdoor
  rw [hdoor, door_getLastD, ← rho_getLastD, hrho]; exact hmk

/-- **α preserves the block marker.**  A marker-preserving boundary into block `t` keeps the
block-start's last symbol equal to the previous block-start's (`= α₁`). -/
theorem marker_alpha_step (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {t α₁ : ℕ}
    (ht : 1 ≤ t) (hN : k * t ≤ p.numVerts)
    (hmark : (p.vert (k * t) : List ℕ).getLastD 0
      = (rho (p.vert (k * t - 1) : List ℕ)).getLastD 0)
    (hmk : (p.vert (k * (t - 1)) : List ℕ).getLastD 0 = α₁) :
    (p.vert (k * t) : List ℕ).getLastD 0 = α₁ := by
  rw [hmark, rho_boundary_prev hk hp ht hN]; exact hmk

/-! ## The bounded meta-confinement wrapper

`ProofsMeta2.meta_confinement` states `hstep`/`hlen` for *all* `j : ℕ`.  A maximal α-run of `m`
2-loops only supplies them *inside the run* (`j < m` / `j + 1 < m`): the boundary out of the
last 2-loop is the run-ending heavy, so `hstep (m − 1)` is unavailable.  We re-run only the short
bounded meta-run induction (`meta_hinv` with `< m` bounds) and hand the confined block family to
`ProofsMeta2.meta_pigeonhole` — the pigeonhole itself is reused verbatim, not forked. -/

/-- **Bounded meta-confinement.**  As `ProofsMeta2.meta_confinement`, but `hlen`/`hstep` are only
required inside the run (`j < m`, `j + 1 < m`). -/
theorem meta_confinement' (hk : 3 ≤ k) {α₁ α₂ : ℕ} {K : RotClass}
    {Astar : ℕ → Vtx k} {m : ℕ} (blk : Fin m × Fin (k - 1) → Vtx k)
    (hα1 : α₁ = (Astar 0 : List ℕ).getLastD 0)
    (hα2 : α₂ = ((Astar 0 : List ℕ).dropLast).getLastD 0)
    (hK : K = rotClass ((Astar 0 : List ℕ).dropLast.dropLast))
    (hlen : ∀ j, j < m → ((Astar j : List ℕ).erase α₁).length = k - 1)
    (hstep : ∀ j, j + 1 < m → (Astar (j + 1) : List ℕ).erase α₁ =
        door (((Astar j : List ℕ).erase α₁).rotate (k - 2)))
    (hblk : ∀ i : Fin m × Fin (k - 1),
        (blk i : List ℕ).erase α₁ = ((Astar i.1 : List ℕ).erase α₁).rotate i.2)
    (hcyc : ∀ i i', i ≠ i' → rotClass (blk i : List ℕ) ≠ rotClass (blk i' : List ℕ)) :
    m ≤ k - 2 := by
  have herase0 : (Astar 0 : List ℕ).erase α₁ = (Astar 0 : List ℕ).dropLast := by
    rw [hα1, erase_getLastD (Astar 0).2.nodup]
  have hg0 : genLoop ((Astar 0 : List ℕ).erase α₁) = (α₂, K) := by
    rw [herase0, genLoop, ← hα2, ← hK]
  have hinv : ∀ j, j < m → genLoop ((Astar j : List ℕ).erase α₁) = (α₂, K) := by
    intro j
    induction j with
    | zero => intro _; exact hg0
    | succ j ih =>
      intro hj
      rw [hstep j hj]
      have hlenj := hlen j (by omega)
      have hrot : (((Astar j : List ℕ).erase α₁).rotate (k - 2)).rotate 1 =
          (Astar j : List ℕ).erase α₁ := by
        rw [List.rotate_rotate, show (k - 2) + 1 = k - 1 from by omega, ← hlenj, List.rotate_length]
      have h2le : 2 ≤ (((Astar j : List ℕ).erase α₁).rotate (k - 2)).length := by
        rw [List.length_rotate, hlenj]; omega
      rw [genLoop_door_eq_rho_of_len h2le]
      show genLoop ((((Astar j : List ℕ).erase α₁).rotate (k - 2)).rotate 1) = (α₂, K)
      rw [hrot]; exact ih (by omega)
  have hmemStar : ∀ j, j < m → Astar j ∈ Vset3 k α₁ α₂ K :=
    fun j hj => mem_Vset3_of_genLoop_metaWord (hinv j hj)
  have hmemBlk : ∀ i : Fin m × Fin (k - 1), blk i ∈ Vset3 k α₁ α₂ K := fun i =>
    Vset3_of_metaWord_rotate_iter (hmemStar i.1 i.1.isLt) (hblk i)
  exact meta_pigeonhole hk hα1 hα2 hK blk hmemBlk hcyc

/-! ## The path-level run bound: from a maximal α-run to `m ≤ k − 2`

Given an exitless path `p` and a maximal α-run of `m` complete 2-loops starting at block `t₀`:
the `k − 2` interior boundaries of each 2-loop are doors (`hdoor`) and each 2-loop is closed by
an α boundary (`halpha`: weight-3, marker-preserving, landing on `alphaWord`).  We manufacture
`meta_confinement'`'s inputs from the path and conclude the run length `m ≤ k − 2`.

Block indices: 2-loop `j` starts at block `t₀ + j·(k−1)`; its blocks are
`t₀ + j·(k−1) + r` for `r = 0,…,k−2`.  The `r ≥ 1` interior boundaries are doors; the boundary
into `t₀ + c·(k−1)` (start of 2-loop `c`, `1 ≤ c < m`) is the terminating α of 2-loop `c − 1`. -/

/-- **α-run bound (path level).**  A maximal α-run of `m` complete 2-loops inside an exitless
path has `m ≤ k − 2` 2-loops. -/
theorem alpha_run_bound (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m * (k - 1)) ≤ p.numVerts)
    (hdoor : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + j * (k - 1) + r) - 1))
          (p.vert (k * (t₀ + j * (k - 1) + r))) = 2)
    (halpha : ∀ c, 1 ≤ c → c < m →
        ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) = 3 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ).getLastD 0
          = (rho (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)).getLastD 0 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ)
          = alphaWord (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)) :
    m ≤ k - 2 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  -- position bounds
  have hSpos : 1 ≤ t₀ + m * (k - 1) := by
    have h1 : 1 * (k - 1) ≤ m * (k - 1) := Nat.mul_le_mul hmpos (le_refl _); omega
  have hposlt : ∀ T, T ≤ t₀ + m * (k - 1) - 1 → k * T < p.numVerts := by
    intro T hT
    have hSk : k * (t₀ + m * (k - 1) - 1) + k = k * (t₀ + m * (k - 1)) := by
      conv_rhs => rw [show t₀ + m * (k - 1) = (t₀ + m * (k - 1) - 1) + 1 from by omega]
      rw [Nat.mul_succ]
    calc k * T ≤ k * (t₀ + m * (k - 1) - 1) := Nat.mul_le_mul (le_refl k) hT
      _ < k * (t₀ + m * (k - 1)) := by omega
      _ ≤ p.numVerts := hN
  have hAr_le : ∀ j, j < m → ∀ r, r ≤ k - 2 → t₀ + j * (k - 1) + r ≤ t₀ + m * (k - 1) - 1 := by
    intro j hj r hr
    have hjm : j * (k - 1) ≤ (m - 1) * (k - 1) := Nat.mul_le_mul (by omega) (le_refl _)
    have hm1 : (m - 1) * (k - 1) + (k - 1) = m * (k - 1) := by
      conv_rhs => rw [show m = (m - 1) + 1 from by omega]
      rw [Nat.succ_mul]
    omega
  have hblklt : ∀ j, j < m → ∀ r, r ≤ k - 2 → k * (t₀ + j * (k - 1) + r) < p.numVerts :=
    fun j hj r hr => hposlt _ (hAr_le j hj r hr)
  have hc_le : ∀ c, c < m → t₀ + c * (k - 1) ≤ t₀ + m * (k - 1) - 1 := by
    intro c hc
    have hcm : c * (k - 1) ≤ (m - 1) * (k - 1) := Nat.mul_le_mul (by omega) (le_refl _)
    have hm1 : (m - 1) * (k - 1) + (k - 1) = m * (k - 1) := by
      conv_rhs => rw [show m = (m - 1) + 1 from by omega]
      rw [Nat.succ_mul]
    omega
  -- the fixed run-marker and the meta-structure read off the run's first block start
  set α₁ : ℕ := (p.vert (k * t₀) : List ℕ).getLastD 0 with hα1def
  set α₂ : ℕ := ((p.vert (k * t₀) : List ℕ).dropLast).getLastD 0 with hα2def
  set K : RotClass := rotClass ((p.vert (k * t₀) : List ℕ).dropLast.dropLast) with hKdef
  -- marker preservation along the run (dynamic marker = fixed α₁)
  have hmkInner : ∀ j, j < m → (p.vert (k * (t₀ + j * (k - 1))) : List ℕ).getLastD 0 = α₁ →
      ∀ r, r ≤ k - 2 → (p.vert (k * (t₀ + j * (k - 1) + r)) : List ℕ).getLastD 0 = α₁ := by
    intro j hj hstart r
    induction r with
    | zero => intro _; rw [Nat.add_zero]; exact hstart
    | succ r ih =>
      intro hr
      have hrle : r ≤ k - 2 := by omega
      exact marker_door_step hk2 hp (t := t₀ + j * (k - 1) + (r + 1)) (by omega)
        (hblklt j hj (r + 1) hr) (hdoor j (r + 1) hj (by omega) hr) (ih hrle)
  have hmkStart : ∀ j, j < m → (p.vert (k * (t₀ + j * (k - 1))) : List ℕ).getLastD 0 = α₁ := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show t₀ + 0 * (k - 1) = t₀ from by omega, hα1def]
    | succ j ih =>
      intro hj
      have hstartj := ih (by omega)
      have hinner := hmkInner j (by omega) hstartj (k - 2) (le_refl _)
      obtain ⟨_, hmark, _⟩ := halpha (j + 1) (by omega) hj
      have hmkprevA : (p.vert (k * (t₀ + (j + 1) * (k - 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
        rw [show t₀ + (j + 1) * (k - 1) - 1 = t₀ + j * (k - 1) + (k - 2) from by
          have he : (j + 1) * (k - 1) = j * (k - 1) + (k - 1) := Nat.succ_mul j (k - 1); omega]
        exact hinner
      exact marker_alpha_step hk1 hp (t := t₀ + (j + 1) * (k - 1))
        (by have h : 1 * 1 ≤ (j + 1) * (k - 1) := Nat.mul_le_mul (Nat.succ_pos j) (by omega); omega)
        (le_of_lt (hposlt _ (hc_le (j + 1) hj))) hmark hmkprevA
  have hmkAll : ∀ j, j < m → ∀ r, r ≤ k - 2 →
      (p.vert (k * (t₀ + j * (k - 1) + r)) : List ℕ).getLastD 0 = α₁ :=
    fun j hj r hr => hmkInner j hj (hmkStart j hj) r hr
  -- the intra-2-loop meta-word rotation relation (`hblk`)
  have hrot : ∀ j, j < m → ∀ r, r ≤ k - 2 →
      (p.vert (k * (t₀ + j * (k - 1) + r)) : List ℕ).erase α₁
        = ((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate r := by
    intro j hj r
    induction r with
    | zero => intro _; rw [Nat.add_zero, List.rotate_zero]
    | succ r ih =>
      intro hr
      have hrle : r ≤ k - 2 := by omega
      have hstep := metaWord_door_block hk2 hp (t := t₀ + j * (k - 1) + (r + 1)) (by omega)
        (hblklt j hj (r + 1) hr) (hdoor j (r + 1) hj (by omega) hr) (hmkAll j hj r hrle)
      rw [hstep, show t₀ + j * (k - 1) + (r + 1) - 1 = t₀ + j * (k - 1) + r from by omega,
          ih hrle, List.rotate_rotate]
  -- the inter-2-loop meta-word door step (`hstep`)
  have hstepMC : ∀ j, j + 1 < m →
      (p.vert (k * (t₀ + (j + 1) * (k - 1))) : List ℕ).erase α₁
        = door (((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).rotate (k - 2)) := by
    intro j hj
    obtain ⟨hw3, hmark, hα⟩ := halpha (j + 1) (by omega) hj
    have hmkprev : (p.vert (k * (t₀ + (j + 1) * (k - 1) - 1)) : List ℕ).getLastD 0 = α₁ := by
      rw [show t₀ + (j + 1) * (k - 1) - 1 = t₀ + j * (k - 1) + (k - 2) from by
        have he : (j + 1) * (k - 1) = j * (k - 1) + (k - 1) := Nat.succ_mul j (k - 1); omega]
      exact hmkAll j (by omega) (k - 2) (le_refl _)
    have hab := metaWord_alpha_block hk hp (t := t₀ + (j + 1) * (k - 1))
      (by have h : 1 * 1 ≤ (j + 1) * (k - 1) := Nat.mul_le_mul (Nat.succ_pos j) (by omega); omega)
      (hposlt _ (hc_le (j + 1) hj)) hw3 hmark hα hmkprev
    rw [hab, show t₀ + (j + 1) * (k - 1) - 1 = t₀ + j * (k - 1) + (k - 2) from by
        have he : (j + 1) * (k - 1) = j * (k - 1) + (k - 1) := Nat.succ_mul j (k - 1); omega,
        hrot j (by omega) (k - 2) (le_refl _)]
  -- `hlen`
  have hlenMC : ∀ j, j < m →
      ((p.vert (k * (t₀ + j * (k - 1))) : List ℕ).erase α₁).length = k - 1 := by
    intro j hj
    rw [← hmkStart j hj, erase_getLastD (p.vert (k * (t₀ + j * (k - 1)))).2.nodup,
        List.length_dropLast, (p.vert (k * (t₀ + j * (k - 1)))).2.length]
  -- `hcyc` via `no_reentry`, using injectivity of the linear block index
  have hninj : ∀ a a' : Fin m × Fin (k - 1),
      (a.1 : ℕ) * (k - 1) + (a.2 : ℕ) = (a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ) → a = a' := by
    intro a a' h
    have hd : 0 < k - 1 := by omega
    have h2 : (a.2 : ℕ) = (a'.2 : ℕ) := by
      have e1 : ((a.1 : ℕ) * (k - 1) + (a.2 : ℕ)) % (k - 1) = (a.2 : ℕ) := by
        rw [Nat.mul_comm (a.1 : ℕ) (k - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt a.2.isLt]
      have e2 : ((a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ)) % (k - 1) = (a'.2 : ℕ) := by
        rw [Nat.mul_comm (a'.1 : ℕ) (k - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt a'.2.isLt]
      rw [← e1, ← e2, h]
    have h1 : (a.1 : ℕ) = (a'.1 : ℕ) :=
      Nat.eq_of_mul_eq_mul_right hd (by omega)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hkey : ∀ a a' : Fin m × Fin (k - 1),
      (a.1 : ℕ) * (k - 1) + (a.2 : ℕ) < (a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ) →
      rotClass (p.vert (k * (t₀ + (a.1 : ℕ) * (k - 1) + (a.2 : ℕ))) : List ℕ)
        ≠ rotClass (p.vert (k * (t₀ + (a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ))) : List ℕ) := by
    intro a a' hlt
    have hBk : k * (t₀ + (a.1 : ℕ) * (k - 1) + (a.2 : ℕ)) + k
        ≤ k * (t₀ + (a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ)) := by
      rw [(Nat.mul_succ k _).symm]
      exact Nat.mul_le_mul (le_refl k) (by omega)
    have hB'n : k * (t₀ + (a'.1 : ℕ) * (k - 1) + (a'.2 : ℕ)) < p.numVerts :=
      hposlt _ (hAr_le a'.1 a'.1.isLt a'.2 (by have := a'.2.isLt; omega))
    exact no_reentry hk1 hp ⟨_, rfl⟩ hBk hB'n
  have hcycMC : ∀ i i' : Fin m × Fin (k - 1), i ≠ i' →
      rotClass (p.vert (k * (t₀ + (i.1 : ℕ) * (k - 1) + (i.2 : ℕ))) : List ℕ)
        ≠ rotClass (p.vert (k * (t₀ + (i'.1 : ℕ) * (k - 1) + (i'.2 : ℕ))) : List ℕ) := by
    intro i i' hne
    rcases lt_trichotomy ((i.1 : ℕ) * (k - 1) + (i.2 : ℕ)) ((i'.1 : ℕ) * (k - 1) + (i'.2 : ℕ))
      with h | h | h
    · exact hkey i i' h
    · exact absurd (hninj i i' h) hne
    · exact (hkey i' i h).symm
  -- assemble via the bounded meta-confinement wrapper
  refine meta_confinement' hk (α₁ := α₁) (α₂ := α₂) (K := K)
    (Astar := fun j => p.vert (k * (t₀ + j * (k - 1))))
    (blk := fun i => p.vert (k * (t₀ + (i.1 : ℕ) * (k - 1) + (i.2 : ℕ))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show α₁ = (p.vert (k * (t₀ + 0 * (k - 1))) : List ℕ).getLastD 0
    rw [hα1def, show t₀ + 0 * (k - 1) = t₀ from by omega]
  · show α₂ = ((p.vert (k * (t₀ + 0 * (k - 1))) : List ℕ).dropLast).getLastD 0
    rw [hα2def, show t₀ + 0 * (k - 1) = t₀ from by omega]
  · show K = rotClass ((p.vert (k * (t₀ + 0 * (k - 1))) : List ℕ).dropLast.dropLast)
    rw [hKdef, show t₀ + 0 * (k - 1) = t₀ from by omega]
  · exact hlenMC
  · exact hstepMC
  · exact fun i => hrot i.1 i.1.isLt i.2 (by have := i.2.isLt; omega)
  · exact hcycMC

end ProofsMeta4

/-! ## The telescope-facing corollary: `runs_pay`

`alpha_run_bound` caps a maximal α-run at `m ≤ k − 2` complete 2-loops; `boundary_contribution`
(`ProofsMeta3`) pins each weight-3 α-boundary's excess ledger term `ew − 2` to `1`.  Packaged,
this is the **per-run excess seed** the amortized telescope consumes: no α-run of complete
2-loops holds more than `k − 2` of them, and every α-transition inside it pays exactly one unit
of `≥3`-weight excess.

### Calibration (k = 5, against the `Refutations` `ℓ = 120` optimal witness)

`k − 2 = 3`, `k − 1 = 4`.  A complete 2-loop is `k − 1 = 4` blocks joined by `k − 2 = 3` interior
door boundaries and closed by one α (weight-3) boundary.  `runs_pay` says a maximal α-run holds
`m ≤ 3` complete 2-loops, and each α-transition contributes `ew − 2 = 3 − 2 = 1`.

The `ℓ = 120` witness histogram is `{1:96, 2:18, 3:4, 4:1}`: `4` weight-3 and `1` weight-4
boundary, so (Layer A, `excess_eq_sum_edgeWeight`) `excess = 4·(3−2) + 1·(4−2) = 4 + 2 = 6 =
Dfr(120)` — tight.  Every one of those `4` weight-3 boundaries — whether an interior α-transition
of a run or a run-terminating marker-mover — contributes exactly `1` by `runs_pay`'s payment
clause, and the single weight-4 contributes `2`; the count clause `m ≤ 3` is respected (no α-run
of complete 2-loops in the witness exceeds `k − 2 = 3`).  This is the demand-matched seed: the
frontier grows by `k − 2` per `ℓ₀`-window, and each window admits at most `k − 2` α-linked
complete 2-loops before a paying event, each paying `1`. -/

namespace Proved

open ProofsMeta4 HPath

/-- **α-run bound (path level)** — re-export of `ProofsMeta4.alpha_run_bound` into `Hunter.Proved`:
any maximal α-run of `m` complete 2-loops in an exitless path has `m ≤ k − 2`. -/
theorem alpha_run_bound {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m * (k - 1)) ≤ p.numVerts)
    (hdoor : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + j * (k - 1) + r) - 1))
          (p.vert (k * (t₀ + j * (k - 1) + r))) = 2)
    (halpha : ∀ c, 1 ≤ c → c < m →
        ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) = 3 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ).getLastD 0
          = (rho (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)).getLastD 0 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ)
          = alphaWord (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)) :
    m ≤ k - 2 :=
  ProofsMeta4.alpha_run_bound hk hp t₀ m hN hdoor halpha

/-- **runs_pay** — the per-run excess seed for the amortized telescope.  A maximal α-run of `m`
complete 2-loops (interior door boundaries `hdoor`, α terminators `halpha`) satisfies both:

* the **count bound** `m ≤ k − 2` (`alpha_run_bound` / meta-confinement); and
* the **payment clause**: each α-transition into 2-loop `c` (`1 ≤ c < m`) contributes exactly one
  unit of `≥3`-weight excess to the per-edge ledger `ew − 2` (`ProofsMeta3.excess_eq_sum_edgeWeight`).

So per `≤ (k − 2)` complete 2-loops of a run, the run's α-transitions bank `m − 1` excess units,
and the run cannot extend past `k − 2` 2-loops without a fresh paying (marker-moving / weight-`≥4`)
event — matching the frontier's `(k − 2)`-per-window growth. -/
theorem runs_pay {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ m : ℕ)
    (hN : k * (t₀ + m * (k - 1)) ≤ p.numVerts)
    (hdoor : ∀ j r, j < m → 1 ≤ r → r ≤ k - 2 →
        ew k (p.vert (k * (t₀ + j * (k - 1) + r) - 1))
          (p.vert (k * (t₀ + j * (k - 1) + r))) = 2)
    (halpha : ∀ c, 1 ≤ c → c < m →
        ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) = 3 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ).getLastD 0
          = (rho (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)).getLastD 0 ∧
        (p.vert (k * (t₀ + c * (k - 1))) : List ℕ)
          = alphaWord (p.vert (k * (t₀ + c * (k - 1)) - 1) : List ℕ)) :
    m ≤ k - 2 ∧
    ∀ c, 1 ≤ c → c < m →
      ew k (p.vert (k * (t₀ + c * (k - 1)) - 1)) (p.vert (k * (t₀ + c * (k - 1)))) - 2 = 1 :=
  ⟨ProofsMeta4.alpha_run_bound hk hp t₀ m hN hdoor halpha,
   fun c hc1 hcm => by have h := (halpha c hc1 hcm).1; omega⟩

end Proved

end Hunter

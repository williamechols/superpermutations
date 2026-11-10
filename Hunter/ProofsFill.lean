/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsLanding
import Hunter.ProofsSPrime
import Hunter.ProofsConfinement

/-!
# Theorem 2 — the FILL LEMMA (marker-move from a complete 2-loop caps at `k − 3`)

This file proves the **fill lemma**: in an exitless path a weight-3 *marker-moving* boundary
leaving a **complete** marked 2-loop (a door-run of `k − 1` blocks) opens a marked 2-loop whose
door-run meets an already-visited (source) 1-cycle at door-position `≤ k − 3`; hence at most
`k − 3` fresh blocks of the landing loop can ever be traversed.

The mathematical content is pure **word algebra** on `rotClass` / `List.erase` / `List.rotate`,
transcribed from the general-`k` symbolic adjudication (`campaign/anchor/symbolic_anchor.py`,
`campaign/reset/results.json`).  The three ingredients:

* `necklace_erase_invariance` — rotation-independence of fixed-value erasure at `rotClass` level
  (deliverable 1, a clean `List` lemma; re-exported from `ProofsConfinement.rotClass_erase_rotate`).
* the **marked-loop door-run model** `markBlock base m j = base.rotate j ++ [m]` and the exact
  **shared-class identities** for each marker-move family `mm_a … mm_d` leaving a complete source
  (deliverable 2).
* `markerMove_from_complete_fill_le` — the `≤ k − 3` fill bound (deliverable 3).

All results are `sorry`-free and axiom-clean.  Namespace `Hunter.ProofsFill`.
-/

namespace Hunter

open List

namespace ProofsFill

variable {k : ℕ}

/-! ## Deliverable 1 — the necklace-erase invariance

`rotClass ((W.rotate r).erase c) = rotClass (W.erase c)`: erasing a *fixed value* commutes with
cyclic rotation at the level of rotation classes.  This is the algebraic core of the whole
landing-cycle census (`symbolic_anchor.py`'s "necklace-erase rotation-invariance" check, verified
for `k = 4 … 8`).  It is already proved as `ProofsConfinement.rotClass_erase_rotate`; we restate it
here under its census name as the file's primitive. -/

/-- **Necklace-erase invariance** (deliverable 1).  Erasing a fixed value `c` from a word is
invariant, at the `rotClass` level, under cyclic rotation of the word.  General `k`, clean `List`
lemma. -/
theorem necklace_erase_invariance {c : ℕ} {W : List ℕ} (hnd : W.Nodup) (r : ℕ) :
    rotClass ((W.rotate r).erase c) = rotClass (W.erase c) :=
  ProofsConfinement.rotClass_erase_rotate hnd r

/-- **Necklace-erase invariance, `Vset3` form.**  Membership of a vertex in a marked 3-loop
`Vset3 α₁ α₂ K` is unchanged if the vertex word is replaced by any cyclic rotation of it — the
double-erase `((v.erase α₁).erase α₂)` has a rotation-invariant class.  (This is the two-marker
iterate of `necklace_erase_invariance`, the closure fact behind `ProofsExcess.sigma_mem_Vset3`.) -/
theorem necklace_erase_invariance₂ {α₁ α₂ : ℕ} {W : List ℕ} (hnd : W.Nodup) (r : ℕ) :
    rotClass (((W.rotate r).erase α₁).erase α₂) = rotClass ((W.erase α₁).erase α₂) := by
  -- erase α₁ of a rotation is a rotation of the erase (up to rotClass), then erase α₂ + invariance
  -- we go through the rotation witness on the once-erased word.
  obtain ⟨q, hq⟩ : (W.rotate r).erase α₁ ~r (W.erase α₁) :=
    rotClass_eq_iff.mp (necklace_erase_invariance (c := α₁) hnd r)
  -- `L = (W.rotate r).erase α₁` is nodup and `L.rotate q = W.erase α₁`; push `erase α₂` through.
  have hLnd : ((W.rotate r).erase α₁).Nodup := ((List.rotate_perm W r).nodup_iff.mpr hnd).erase _
  calc rotClass (((W.rotate r).erase α₁).erase α₂)
      = rotClass ((((W.rotate r).erase α₁).rotate q).erase α₂) :=
        (necklace_erase_invariance hLnd q).symm
    _ = rotClass ((W.erase α₁).erase α₂) := by rw [hq]

/-! ## The marked-loop door-run model

A marked 2-loop with base word `base` (length `k − 1`) and marker `m` (the constant last symbol)
has block-starts `markBlock base m j = base.rotate j ++ [m]` for `j = 0, …, k − 2`: the meta-word
`base` rotates by exactly one per **door** boundary (`ProofsSynthesis.metaWord_door_block`,
`lemmaA`'s door-run), the marker stays fixed, and a nodup block-start is `dropLast ++ [getLastD]`
so this is the block-start.  Its 1-cycle class is `rotClass (markBlock base m j)`.

The **rotate helper** `(P ++ Q).rotate P.length = Q ++ P` is the only list computation the
shared-class census needs. -/

/-- Rotating a concatenation by the length of its left part swaps the two parts. -/
theorem rotate_append_left (P Q : List ℕ) : (P ++ Q).rotate P.length = Q ++ P := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- `rotate_append_left` with the amount supplied explicitly (so it matches a numeral in the
goal rather than the reducible `P.length`). -/
theorem rotate_append_left' (P Q : List ℕ) {n : ℕ} (hn : n = P.length) :
    (P ++ Q).rotate n = Q ++ P := by subst hn; exact rotate_append_left P Q

/-- `rotClass` is rotation-invariant: any rotation of a word has the same 1-cycle class. -/
theorem rotClass_rotate (w : List ℕ) (m : ℕ) : rotClass (w.rotate m) = rotClass w :=
  (rotClass_eq_iff.mpr ⟨m, rfl⟩).symm

/-- The `j`-th block-start of a marked 2-loop: base rotated by `j`, marker appended. -/
def markBlock (base : List ℕ) (m : ℕ) (j : ℕ) : List ℕ := base.rotate j ++ [m]

/-! ## Deliverable 2 — the shared-class identities per marker-move family

Exit head `x = a :: b :: c :: s` with `x₁ = a` the run marker, `x₂ = b`, `x₃ = c`, and
`s = x.drop 3` the length-`(k−3)` tail.  The **source** complete 2-loop (the loop the boundary
leaves) has base `u = b :: c :: s` and marker `a`; its block-starts are `srcBlock j`, all `k − 1`
1-cycles visited.  A weight-3 marker-move lands on one of the four families (`weight3_markerMove_last`
pins the new marker to `x₂ = b` for `mm_a`/`mm_b`, to `x₃ = c` for `mm_c`/`mm_d`):

| family | landing base | marker | shared door-positions (of `k−1`) → source block |
|--------|--------------|--------|--------------------------------------------------|
| `mm_a` | `s ++ [a,c]` |  `b`   | pos `k−3` → src 1;  pos `k−2` → src 0            |
| `mm_b` | `s ++ [c,a]` |  `b`   | pos `k−3` → src 2                                |
| `mm_c` | `s ++ [a,b]` |  `c`   | pos `0` → src 0 (landing entry itself is `A`)    |
| `mm_d` | `s ++ [b,a]` |  `c`   | pos `0` → src 1                                  |

Each identity is proved by the single rotation witness `rotate_append_left`.  The `s.length` /
`s.length + 1` positions ARE the general-`k` door-positions `k − 3` / `k − 2` (since the loop base
has length `k − 1 = s.length + 2`).  All four families collide with the visited source at
door-position `≤ k − 3` (`s.length` for `mm_a`/`mm_b`, `0` for `mm_c`/`mm_d`) — the fill bound. -/

variable (a b c : ℕ) (s : List ℕ)

/-- Source complete 2-loop block-start `j` (base `b :: c :: s`, marker `a`). -/
def srcBlock (j : ℕ) : List ℕ := markBlock (b :: c :: s) a j
/-- `mm_a` landing 2-loop block-start `j` (base `s ++ [a,c]`, marker `b`). -/
def mmaBlock (j : ℕ) : List ℕ := markBlock (s ++ [a, c]) b j
/-- `mm_b` landing 2-loop block-start `j` (base `s ++ [c,a]`, marker `b`). -/
def mmbBlock (j : ℕ) : List ℕ := markBlock (s ++ [c, a]) b j
/-- `mm_c` landing 2-loop block-start `j` (base `s ++ [a,b]`, marker `c`). -/
def mmcBlock (j : ℕ) : List ℕ := markBlock (s ++ [a, b]) c j
/-- `mm_d` landing 2-loop block-start `j` (base `s ++ [b,a]`, marker `c`). -/
def mmdBlock (j : ℕ) : List ℕ := markBlock (s ++ [b, a]) c j

/- **k = 5 calibration** (`campaign/anchor/fill_witness.py`, `A = A0..A4`, `x = A4::A0::A1::A2::A3`
so `a=A4, b=A0, c=A1, s=[A2,A3]`, `s.length = 2 = k−3`):
* `mm_a` base `[A2,A3,A4,A1]` marker `A0`; door-pos 2 block `(A4,A1,A2,A3,A0) ~r (A1,A2,A3,A0,A4)` =
  src block 1; door-pos 3 block `(A1,A2,A3,A4,A0) ~r A` = src block 0.  → 2 shared, maxfill `k−3=2`.
* `mm_b` base `[A2,A3,A1,A4]` marker `A0`; door-pos 2 `(A1,A4,A2,A3,A0) ~r (A2,A3,A0,A1,A4)` =
  src block 2.  → 1 shared, but first at pos 2 = `k−3`, so maxfill `k−3=2`.
* `mm_c` base `[A2,A3,A4,A0]` marker `A1`; door-pos 0 = landing entry `~r A` = src block 0 → not
  fresh, maxfill 0.
* `mm_d` base `[A2,A3,A0,A4]` marker `A1`; door-pos 0 = landing entry `~r` src block 1 → not fresh,
  maxfill 0.
Matches `results.json` COMPLETE_exit_opens (`mm_a` share 2, `mm_b` share 1, both maxfill `k−3`;
`mm_c`/`mm_d` not fresh) and `measure_caps.py` RESET-cap max `= k−3` for `k = 5,6,7`. -/

/-- **`mm_a`, first shared class.**  Landing door-position `k − 3` (`= s.length`) has the 1-cycle
class of source block 1. -/
theorem mm_a_share1 : rotClass (mmaBlock a b c s s.length) = rotClass (srcBlock a b c s 1) := by
  have h : (mmaBlock a b c s s.length).rotate 1 = srcBlock a b c s 1 := by
    unfold mmaBlock srcBlock markBlock
    rw [rotate_append_left s [a, c]]
    -- mmaBlock = a :: c :: s ++ [b];  rotate 1 = (c :: s ++ [b]) ++ [a]
    have h1 : ([a, c] ++ s ++ [b]) = [a] ++ (c :: s ++ [b]) := by simp
    have h2 : (b :: c :: s).rotate 1 ++ [a] = (c :: s ++ [b]) ++ [a] := by
      rw [show b :: c :: s = [b] ++ (c :: s) from rfl,
          rotate_append_left' [b] (c :: s) (by simp)]
    rw [h1, rotate_append_left' [a] (c :: s ++ [b]) (by simp), h2]
  rw [← h, rotClass_rotate]

/-- **`mm_a`, second shared class.**  Landing door-position `k − 2` (`= s.length + 1`) has the
1-cycle class of source block 0 (the source-loop base `A`). -/
theorem mm_a_share2 :
    rotClass (mmaBlock a b c s (s.length + 1)) = rotClass (srcBlock a b c s 0) := by
  have h : (mmaBlock a b c s (s.length + 1)).rotate (s.length + 2) = srcBlock a b c s 0 := by
    unfold mmaBlock srcBlock markBlock
    rw [show s ++ [a, c] = (s ++ [a]) ++ [c] by simp,
        show s.length + 1 = (s ++ [a]).length by simp, rotate_append_left (s ++ [a]) [c]]
    -- landing = c :: (s ++ [a]) ++ [b] = (c :: s ++ [a]) ++ [b]
    rw [show [c] ++ (s ++ [a]) ++ [b] = (c :: s ++ [a]) ++ [b] by simp,
        show s.length + 2 = (c :: s ++ [a]).length by simp,
        rotate_append_left (c :: s ++ [a]) [b]]
    simp
  rw [← h, rotClass_rotate]

/-- **`mm_b`, shared class.**  Landing door-position `k − 3` (`= s.length`) has the 1-cycle class
of source block 2. -/
theorem mm_b_share : rotClass (mmbBlock a b c s s.length) = rotClass (srcBlock a b c s 2) := by
  have h : (srcBlock a b c s 2).rotate (s.length + 1) = mmbBlock a b c s s.length := by
    unfold mmbBlock srcBlock markBlock
    rw [rotate_append_left s [c, a],
        show b :: c :: s = [b, c] ++ s from rfl, rotate_append_left' [b, c] s (by simp)]
    -- srcBlock 2 = (s ++ [b, c]) ++ [a] = (s ++ [b]) ++ [c, a]
    rw [show s ++ [b, c] ++ [a] = (s ++ [b]) ++ [c, a] by simp,
        show s.length + 1 = (s ++ [b]).length by simp, rotate_append_left (s ++ [b]) [c, a]]
    simp
  rw [← h, rotClass_rotate]

/-- **`mm_c`, shared class.**  The landing entry itself (door-position `0`) has the 1-cycle class
of source block 0 — the landing is *not fresh*. -/
theorem mm_c_share : rotClass (mmcBlock a b c s 0) = rotClass (srcBlock a b c s 0) := by
  have h : (srcBlock a b c s 0).rotate 2 = mmcBlock a b c s 0 := by
    unfold mmcBlock srcBlock markBlock
    rw [List.rotate_zero, List.rotate_zero,
        show b :: c :: s ++ [a] = [b, c] ++ (s ++ [a]) by simp,
        rotate_append_left' [b, c] (s ++ [a]) (by simp)]
    simp
  rw [← h, rotClass_rotate]

/-- **`mm_d`, shared class.**  The landing entry itself (door-position `0`) has the 1-cycle class
of source block 1 — the landing is *not fresh*. -/
theorem mm_d_share : rotClass (mmdBlock a b c s 0) = rotClass (srcBlock a b c s 1) := by
  have h : (srcBlock a b c s 1).rotate 1 = mmdBlock a b c s 0 := by
    unfold mmdBlock srcBlock markBlock
    rw [List.rotate_zero, show b :: c :: s = [b] ++ (c :: s) from rfl,
        rotate_append_left' [b] (c :: s) (by simp)]
    -- srcBlock 1 = (c :: s ++ [b]) ++ [a] = [c] ++ (s ++ [b, a])
    rw [show c :: s ++ [b] ++ [a] = [c] ++ (s ++ [b, a]) by simp,
        rotate_append_left' [c] (s ++ [b, a]) (by simp)]
  rw [← h, rotClass_rotate]

/-! ## Deliverable 3 — the `≤ k − 3` fill bound

`SourceVisited a b c s K` says the class `K` is one of the `k − 1` (all-visited) 1-cycle classes
of the complete source loop.  The door-run of the landing loop `blk j = markBlock base m j` is
traversed in order `j = 0, 1, 2, …`; by `ProofsExitless.no_reentry` a completed source 1-cycle is
never re-entered, so the traversal ends at the first visited door-position.  `fresh_run_le` packages
that ordering fact: any initial run of *fresh* (non-source) blocks stops at the first visited
position `p`.  Each marker-move family has a visited position `p ≤ s.length = k − 3`
(`s.length`/`k−3` for `mm_a`,`mm_b`; `0` for the not-fresh `mm_c`,`mm_d`), so the fresh run — the
number of blocks that can ever be traversed — is `≤ k − 3`.

Note (honest scope, matching `ProofsLanding`/`campaign/reset/results.json`): this is the
word-algebra + ordering core.  Threading it through the absolute block-index lattice of a concrete
`HPath` (so `hfresh` becomes the realized run) is the acknowledged `HPath(k−1)` meta-lift residual;
here `hfresh` is taken as the door-run hypothesis it discharges. -/

/-- The visited 1-cycle classes: the classes of the complete source loop's block-starts. -/
def SourceVisited (a b c : ℕ) (s : List ℕ) (K : RotClass) : Prop :=
  ∃ j, K = rotClass (srcBlock a b c s j)

/-- **Fresh-run cap (ordering core).**  If a door-run `blk` has a visited class at position `p`,
any initial segment of `F` fresh (non-visited) blocks has `F ≤ p`. -/
theorem fresh_run_le {blk : ℕ → List ℕ} {vis : RotClass → Prop} {p F : ℕ}
    (hp : vis (rotClass (blk p)))
    (hfresh : ∀ j, j < F → ¬ vis (rotClass (blk j))) : F ≤ p := by
  by_contra h
  exact hfresh p (by omega) hp

/-- **The fill bound, packaged.**  Given a visited landing door-position `p ≤ s.length`, any fresh
run has length `≤ s.length`. -/
theorem fill_le_of_visited {a b c : ℕ} {s base : List ℕ} {m F : ℕ}
    (hvis : ∃ p, p ≤ s.length ∧ SourceVisited a b c s (rotClass (markBlock base m p)))
    (hfresh : ∀ j, j < F → ¬ SourceVisited a b c s (rotClass (markBlock base m j))) :
    F ≤ s.length := by
  obtain ⟨p, hp, hv⟩ := hvis
  exact le_trans (fresh_run_le hv hfresh) hp

/-- **`markerMove_from_complete_fill_le` — the `≤ k − 3` fill bound** (deliverable 3).  A weight-3
marker-moving landing leaving a **complete** source loop (new marker `x₂ = b` for `mm_a`/`mm_b`,
`x₃ = c` for `mm_c`/`mm_d`, per `ProofsLanding.weight3_markerMove_last`) opens a 2-loop whose
door-run meets a visited source 1-cycle at position `≤ s.length = k − 3`.  Hence at most
`k − 3` (`= s.length`) fresh blocks of the landing loop can ever be traversed. -/
theorem markerMove_from_complete_fill_le (base : List ℕ) (m F : ℕ)
    (hfam : (base = s ++ [a, c] ∧ m = b) ∨ (base = s ++ [c, a] ∧ m = b) ∨
            (base = s ++ [a, b] ∧ m = c) ∨ (base = s ++ [b, a] ∧ m = c))
    (hfresh : ∀ j, j < F → ¬ SourceVisited a b c s (rotClass (markBlock base m j))) :
    F ≤ s.length := by
  refine fill_le_of_visited ?_ hfresh
  rcases hfam with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩
  · exact ⟨s.length, le_refl _, ⟨1, by rw [hm]; exact mm_a_share1 a b c s⟩⟩
  · exact ⟨s.length, le_refl _, ⟨2, by rw [hm]; exact mm_b_share a b c s⟩⟩
  · exact ⟨0, Nat.zero_le _, ⟨0, by rw [hm]; exact mm_c_share a b c s⟩⟩
  · exact ⟨0, Nat.zero_le _, ⟨1, by rw [hm]; exact mm_d_share a b c s⟩⟩

/-! ## Deliverable 4 (stretch) — the anchor source-membership identity

The robustness-margin half of the anchor (`campaign/anchor/symbolic_anchor.py`): every block-start
of the source loop lies in the landing marked-3-loop `Vset3(μ, c, K)`, *for every source depth*
`r`.  With source base `u` (marker `μ ∉ u`) the source block at depth `r` is `u.rotate r ++ [μ]`,
and erasing the two landing markers `μ` then `c` yields the rotation-invariant class
`K = rotClass (u.erase c)` — the class is independent of `r` by `necklace_erase_invariance`.  This
is exactly `symbolic_anchor.py`'s "`K = rotClass(A[:-1].erase c)`, `srcOK` for every depth". -/

/-- **`anchor_source_membership`** (deliverable 4, stretch).  For every source depth `r`, the
double marker-erasure `((u.rotate r ++ [μ]).erase μ).erase c` of the source block-start has the
fixed class `rotClass (u.erase c)` — the landing `Vset3(μ, c, ·)` key (`mem_Vset3_iff_erase`).  So
all source blocks lie in the one landing marked-3-loop, at every depth. -/
theorem anchor_source_membership {u : List ℕ} (hu : u.Nodup) (μ c : ℕ) (hμ : μ ∉ u) (r : ℕ) :
    rotClass (((u.rotate r ++ [μ]).erase μ).erase c) = rotClass (u.erase c) := by
  have hμr : μ ∉ u.rotate r := fun h => hμ ((List.rotate_perm u r).mem_iff.mp h)
  rw [List.erase_append_right _ hμr, List.erase_cons_head, List.append_nil]
  exact necklace_erase_invariance hu r

end ProofsFill

end Hunter

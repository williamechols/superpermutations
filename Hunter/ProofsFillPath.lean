/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsFill
import Hunter.ProofsRunExtract

/-!
# Theorem 2 — the FILL LEMMA at PATH LEVEL (`Hunter.Proved.fill_path`)

This file wires the word-algebra fill lemma (`Hunter/ProofsFill.lean`) down to a concrete
exitless `HPath`.  It discharges the `hfresh` door-run hypothesis of
`ProofsFill.markerMove_from_complete_fill_le` **entirely at path level** — using the ledger's
door-run reconstruction (`ProofsLedger.door_run_metaWord`), the rotation-structure normal form
(`ProofsExitless.no_reentry` / `block_is_full_cycle`), and the marker-move classification
(`ProofsLanding.weight3_markerMove_last`).

## Statement

`fill_path`: in an exitless path, a weight-3 **marker-moving** boundary into block `t` leaving a
**complete** source 2-loop (`IsComplete p (t−1)`) opens a landing 2-loop (entry block `t`,
`doorDepth p t = 0`) that can **never complete**: `¬ IsComplete p (t + (k−2))`.  The opened slab
fills to depth at most `k−3` — exactly the M1 "reset-from-complete opens only a defective slab"
exclusion (`PROGRESS-m1.md` §3/§5, the reset-only-from-incomplete soundness item).

## The coordinate bridge (calibrated on k = 5)

The source-side exit word is `X = p.vert (k·t − 1) = a :: b :: c :: s` (a permutation word,
`|s| = k − 3`), whose run marker is `a = (rho X).getLastD 0 = X₁`.  Its `rho` is the source loop's
last block-start `p.vert (k·(t−1)) = (b::c::s) ++ [a] = srcBlock 0` (`ProofsFill`'s coordinates).
The whole complete source loop reconstructs by `door_run_metaWord` as the `k−1` rotations
`srcBlock j = (b::c::s).rotate j ++ [a]`; concretely
* `p.vert (k·(t−1))  = srcBlock 0`,
* `p.vert (k·g0)     = srcBlock 1`   where `g0 = loopStart p (t−1) = t − (k−1)`,
* `p.vert (k·(g0+1)) = srcBlock 2`.

The landing block-start is `V = p.vert (k·t) = s ++ r`, `r` a permutation of `{a,b,c}` with
`V.getLastD 0 ≠ a` (marker moved).  By `weight3_markerMove_last` the moved marker is `b` or `c`,
and the four arrangements are exactly `ProofsFill`'s `mm_a … mm_d`:

| family | `V = p.vert (k·t)` | base `V.erase mark` | mark | collision (door-pos → src block) |
|--------|--------------------|---------------------|------|----------------------------------|
| `mm_a` | `s ++ [a,c,b]`     | `s ++ [a,c]`        | `b`  | pos `k−3` → `srcBlock 1 = p.vert (k·g0)`      |
| `mm_b` | `s ++ [c,a,b]`     | `s ++ [c,a]`        | `b`  | pos `k−3` → `srcBlock 2 = p.vert (k·(g0+1))`  |
| `mm_c` | `s ++ [a,b,c]`     | `s ++ [a,b]`        | `c`  | pos `0`   → `srcBlock 0 = p.vert (k·(t−1))`   |
| `mm_d` | `s ++ [b,a,c]`     | `s ++ [b,a]`        | `c`  | pos `0`   → `srcBlock 1 = p.vert (k·g0)`      |

k = 5 (`campaign/anchor/fill_witness.py`, `A = A0..A4`, `X = A4::A0::A1::A2::A3`, so
`a=A4, b=A0, c=A1, s=[A2,A3]`, `|s| = 2 = k−3`):  if the landing loop *completed* it would run
doors `t+1 … t+3` and place block `t + 2` (door-pos `s.length = 2`).  For `mm_a` that block is
`mmaBlock … 2 = (A4,A1,A2,A3,A0) ~ (A1,A2,A3,A0,A4) = srcBlock 1 = p.vert (k·g0)` — an already
visited earlier complete block.  `no_reentry` forbids re-entering a completed 1-cycle, so the
landing door-run cannot reach door-pos `k−3`, i.e. it never completes.

Namespace `Hunter.ProofsFillPath`.  Zero sorry, zero new axiom.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsFillPath

open ProofsExitless ProofsLedger ProofsFill ProofsMeta ProofsMeta3 ProofsLanding ProofsRunExtract
open ProofsSynthesis ProofsConfinement HPath

variable {k : ℕ}

/-! ## §1. Two reusable bricks -/

/-- A nonempty nodup word is its marker-erasure followed by its marker (the block-start
reconstruction; `erase_getLastD` + `list_dropLast_getLastD`). -/
theorem marker_reconstruct {w : List ℕ} (hnd : w.Nodup) (hne : w ≠ []) :
    w = w.erase (w.getLastD 0) ++ [w.getLastD 0] := by
  rw [erase_getLastD hnd]; exact list_dropLast_getLastD w hne

/-- **Door-run block-start reconstruction.**  Along a door-run rooted at block `t₀` (interior
boundaries into `t₀+1 … t₀+d` all weight-2), block-start `t₀+r` is the `r`-fold rotation of the
root's marker-erasure, with the (constant) marker appended:
`p.vert (k·(t₀+r)) = base.rotate r ++ [mark]` where `mark = (p.vert (k·t₀)).getLastD 0`,
`base = (p.vert (k·t₀)).erase mark`.  Immediate from `door_run_metaWord` + `marker_reconstruct`. -/
theorem blockrun_eq (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless) (t₀ d : ℕ)
    (hN : k * (t₀ + d) < p.numVerts)
    (hdoor : ∀ r, 1 ≤ r → r ≤ d →
        ew k (p.vert (k * (t₀ + r) - 1)) (p.vert (k * (t₀ + r))) = 2) :
    ∀ r, r ≤ d →
      (p.vert (k * (t₀ + r)) : List ℕ)
        = ((p.vert (k * t₀) : List ℕ).erase ((p.vert (k * t₀) : List ℕ).getLastD 0)).rotate r
          ++ [(p.vert (k * t₀) : List ℕ).getLastD 0] := by
  intro r hr
  obtain ⟨hmk, hmeta⟩ := door_run_metaWord hk hp t₀ d hN hdoor r hr
  have hne : (p.vert (k * (t₀ + r)) : List ℕ) ≠ [] := by
    intro h
    have hl := (p.vert (k * (t₀ + r))).2.length
    rw [h] at hl; simp at hl; omega
  calc (p.vert (k * (t₀ + r)) : List ℕ)
      = (p.vert (k * (t₀ + r)) : List ℕ).erase ((p.vert (k * (t₀ + r)) : List ℕ).getLastD 0)
          ++ [(p.vert (k * (t₀ + r)) : List ℕ).getLastD 0] :=
        marker_reconstruct (p.vert (k * (t₀ + r))).2.nodup hne
    _ = _ := by rw [hmk, hmeta]

/-! ## §2. The path-level fill bound

`fill_path`: a marker-move into block `t` leaving a **complete** source loop opens a landing loop
that cannot complete.  The proof reconstructs the source loop's block-starts as the `ProofsFill`
coordinates `srcBlock 0/1/2` (via `door_run_metaWord`), destructures the landing block-start into
one of the four `mm_a … mm_d` families, and — assuming the landing *did* complete — locates a
landing block whose 1-cycle class equals a source block's class (the `mmX` shared-class identity),
contradicting `no_reentry`. -/

theorem fill_path (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + (k - 2)) < p.numVerts)
    (hmm : IsMarkerMove p t) (hcomp : IsComplete p (t - 1)) :
    ¬ IsComplete p (t + (k - 2)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  -- doorDepth of the complete source loop
  have hcomp' : doorDepth p (t - 1) = k - 2 := hcomp
  have hk2t : k - 2 ≤ t - 1 := by rw [← hcomp']; exact doorDepth_le p (t - 1)
  -- ==================================================================================
  -- Destructure the source exit word `X = p.vert (k·t − 1) = a :: b :: c :: s`
  -- ==================================================================================
  obtain ⟨a, b, c, s, hxeq⟩ :
      ∃ a b c s, (p.vert (k * t - 1) : List ℕ) = a :: b :: c :: s := by
    have hlen : (p.vert (k * t - 1) : List ℕ).length = k := (p.vert (k * t - 1)).2.length
    set X : List ℕ := (p.vert (k * t - 1) : List ℕ) with hXd
    clear_value X
    match X, hlen with
    | a :: b :: c :: s, _ => exact ⟨a, b, c, s, rfl⟩
    | [], h => simp only [List.length_nil] at h; omega
    | [a], h => simp only [List.length_cons, List.length_nil] at h; omega
    | [a, b], h => simp only [List.length_cons, List.length_nil] at h; omega
  have hslen : s.length = k - 3 := by
    have hlen : (p.vert (k * t - 1) : List ℕ).length = k := (p.vert (k * t - 1)).2.length
    rw [hxeq] at hlen; simp at hlen; omega
  -- nodup structure of X = a :: b :: c :: s
  have hXnd : (a :: b :: c :: s).Nodup := by rw [← hxeq]; exact (p.vert (k * t - 1)).2.nodup
  have habcs : a ∉ (b :: c :: s) := (List.nodup_cons.mp hXnd).1
  have hbcsnd : (b :: c :: s).Nodup := (List.nodup_cons.mp hXnd).2
  have hbcs' : b ∉ (c :: s) := (List.nodup_cons.mp hbcsnd).1
  have hcsnd : (c :: s).Nodup := (List.nodup_cons.mp hbcsnd).2
  have hcs' : c ∉ s := (List.nodup_cons.mp hcsnd).1
  have hab : a ≠ b := fun h => habcs (by rw [h]; simp)
  have hac : a ≠ c := fun h => habcs (by rw [h]; simp)
  have hbc : b ≠ c := fun h => hbcs' (by rw [h]; simp)
  have hbs : b ∉ s := fun h => hbcs' (List.mem_cons_of_mem _ h)
  -- ==================================================================================
  -- Source loop reconstruction: srcBlock 0/1/2 are visited path blocks
  -- ==================================================================================
  set g0 : ℕ := (t - 1) - (k - 2) with hg0def
  have hg0 : g0 + (k - 2) = t - 1 := by omega
  -- window bound for block t−1
  have hBfull : k * (t - 1) + (k - 1) < p.numVerts := by
    have hkt : k * t = k * (t - 1) + k := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h2 : k * t ≤ k * (t + (k - 2)) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  -- block t−1 = (b::c::s) ++ [a] (from rho X)
  have hbt1 : (p.vert (k * (t - 1)) : List ℕ) = (b :: c :: s) ++ [a] := by
    have hfc : p.vert (k * (t - 1) + (k - 1)) = sigma^[k - 1] (p.vert (k * (t - 1))) :=
      block_is_full_cycle hk1 hp ⟨t - 1, rfl⟩ (by omega) hBfull
    have hidx : k * (t - 1) + (k - 1) = k * t - 1 := by
      have hkt : k * t = k * (t - 1) + k := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
    rw [hidx] at hfc
    have hxrot : (p.vert (k * t - 1) : List ℕ) = (p.vert (k * (t - 1)) : List ℕ).rotate (k - 1) := by
      rw [hfc]; exact sigma_iter_val (k - 1) (p.vert (k * (t - 1)))
    have hroteq : (p.vert (k * (t - 1)) : List ℕ).rotate (k - 1) = a :: b :: c :: s := by
      rw [← hxrot]; exact hxeq
    have hlen : (p.vert (k * (t - 1)) : List ℕ).length = k := (p.vert (k * (t - 1))).2.length
    have hcong : ((p.vert (k * (t - 1)) : List ℕ).rotate (k - 1)).rotate 1
        = (a :: b :: c :: s).rotate 1 := congrArg (·.rotate 1) hroteq
    have hrotk : (p.vert (k * (t - 1)) : List ℕ).rotate k = (p.vert (k * (t - 1)) : List ℕ) := by
      have hrl := List.rotate_length (p.vert (k * (t - 1)) : List ℕ)
      rw [hlen] at hrl; exact hrl
    rw [List.rotate_rotate, show (k - 1) + 1 = k from by omega, hrotk] at hcong
    rw [hcong]; show (a :: b :: c :: s).rotate 1 = (b :: c :: s) ++ [a]; simp
  have hsrc0 : (p.vert (k * (t - 1)) : List ℕ) = srcBlock a b c s 0 := by
    rw [hbt1]; simp [ProofsFill.srcBlock, ProofsFill.markBlock, List.rotate_zero]
  -- source door interiors
  have hdoor_src : ∀ r, 1 ≤ r → r ≤ k - 2 →
      ew k (p.vert (k * (g0 + r) - 1)) (p.vert (k * (g0 + r))) = 2 := by
    intro r hr1 hr2
    have hj : (k - 2) - r < doorDepth p (t - 1) := by rw [hcomp']; omega
    have hd := isDoor_of_lt_doorDepth p (t - 1) ((k - 2) - r) hj
    have hidx : (t - 1) - ((k - 2) - r) = g0 + r := by omega
    rw [hidx, IsDoor, bw] at hd; exact hd
  have hNsrc : k * (g0 + (k - 2)) < p.numVerts := by rw [hg0]; omega
  have hLsrc := blockrun_eq hk2 hp g0 (k - 2) hNsrc hdoor_src
  set sm : ℕ := (p.vert (k * g0) : List ℕ).getLastD 0 with hsmdef
  set sb : List ℕ := (p.vert (k * g0) : List ℕ).erase sm with hsbdef
  have hsblen : sb.length = k - 1 := by
    rw [hsbdef, hsmdef, erase_getLastD (p.vert (k * g0)).2.nodup, List.length_dropLast,
        (p.vert (k * g0)).2.length]
  -- block t−1 = sb.rotate (k−2) ++ [sm]
  have hLsrc_km2 := hLsrc (k - 2) (le_refl _)
  rw [hg0] at hLsrc_km2
  have happ : sb.rotate (k - 2) ++ [sm] = (b :: c :: s) ++ [a] := by rw [← hLsrc_km2]; exact hbt1
  have hlen1 : (sb.rotate (k - 2)).length = (b :: c :: s).length := by
    rw [List.length_rotate, hsblen]; simp only [List.length_cons]; omega
  obtain ⟨hrot, htt⟩ := List.append_inj happ hlen1
  have hma : sm = a := by injection htt
  have hsb1 : sb = (b :: c :: s).rotate 1 := by
    have h : (sb.rotate (k - 2)).rotate 1 = (b :: c :: s).rotate 1 := congrArg (·.rotate 1) hrot
    rw [List.rotate_rotate, show (k - 2) + 1 = k - 1 from by omega] at h
    have hid : sb.rotate (k - 1) = sb := by
      have hrl := List.rotate_length sb
      rw [hsblen] at hrl; exact hrl
    rw [hid] at h; exact h
  have hsrc1 : (p.vert (k * g0) : List ℕ) = srcBlock a b c s 1 := by
    have h0 := hLsrc 0 (by omega)
    rw [Nat.add_zero, List.rotate_zero, hsb1, hma] at h0
    rw [h0]; rfl
  have hsrc2 : (p.vert (k * (g0 + 1)) : List ℕ) = srcBlock a b c s 2 := by
    have h1 := hLsrc 1 (by omega)
    rw [hsb1, hma, List.rotate_rotate] at h1
    rw [h1]; rfl
  -- ==================================================================================
  -- The `no_reentry` collision closer
  -- ==================================================================================
  have collide : ∀ (pos srcidx : ℕ), srcidx + 1 ≤ t → k * (t + pos) < p.numVerts →
      rotClass (p.vert (k * (t + pos)) : List ℕ) = rotClass (p.vert (k * srcidx) : List ℕ) →
      False := by
    intro pos srcidx hle hlt hcls
    have hBk : k * srcidx + k ≤ k * (t + pos) := by
      have h := Nat.mul_le_mul (le_refl k) (show srcidx + 1 ≤ t + pos by omega)
      rwa [Nat.mul_succ] at h
    exact no_reentry hk1 hp (⟨srcidx, rfl⟩ : k ∣ k * srcidx) hBk hlt hcls.symm
  -- ==================================================================================
  -- Assume the landing loop completes; reconstruct it and derive the collision
  -- ==================================================================================
  intro hLcomp
  have hLcomp' : doorDepth p (t + (k - 2)) = k - 2 := hLcomp
  have hdoor_land : ∀ r, 1 ≤ r → r ≤ k - 2 →
      ew k (p.vert (k * (t + r) - 1)) (p.vert (k * (t + r))) = 2 := by
    intro r hr1 hr2
    have hj : (k - 2) - r < doorDepth p (t + (k - 2)) := by rw [hLcomp']; omega
    have hd := isDoor_of_lt_doorDepth p (t + (k - 2)) ((k - 2) - r) hj
    have hidx : (t + (k - 2)) - ((k - 2) - r) = t + r := by omega
    rw [hidx, IsDoor, bw] at hd; exact hd
  have hLland := blockrun_eq hk2 hp t (k - 2) hN hdoor_land
  -- landing overlap: V = s ++ [pp, qq, zz]
  have hbw : bw p t = 3 := hmm.1
  have hwt3 : wt k (p.vert (k * t - 1) : List ℕ) (p.vert (k * t) : List ℕ) = 3 := hbw
  have hover : (p.vert (k * t - 1) : List ℕ).drop 3 = (p.vert (k * t) : List ℕ).take (k - 3) := by
    have hspec := (wt_spec (u := (p.vert (k * t - 1) : List ℕ)) (v := (p.vert (k * t) : List ℕ)) hk1
      (le_of_eq (p.vert (k * t - 1)).2.length)).2.2
    rw [hwt3] at hspec; exact hspec
  have hstake : s = (p.vert (k * t) : List ℕ).take (k - 3) := by rw [← hover, hxeq]; rfl
  have hV : (p.vert (k * t) : List ℕ) = s ++ (p.vert (k * t) : List ℕ).drop (k - 3) := by
    conv_lhs => rw [← List.take_append_drop (k - 3) (p.vert (k * t) : List ℕ)]
    rw [← hstake]
  have hrlen : ((p.vert (k * t) : List ℕ).drop (k - 3)).length = 3 := by
    rw [List.length_drop, (p.vert (k * t)).2.length]; omega
  obtain ⟨pp, qq, zz, hrtail⟩ := List.length_eq_three.mp hrlen
  have hVform : (p.vert (k * t) : List ℕ) = s ++ [pp, qq, zz] := by rw [hV, hrtail]
  have hmarkV : (p.vert (k * t) : List ℕ).getLastD 0 = zz := by
    rw [hVform, show s ++ [pp, qq, zz] = (s ++ [pp, qq]) ++ [zz] by simp, List.getLastD_concat]
  -- V nodup structure
  have hVnd : (s ++ [pp, qq, zz]).Nodup := by rw [← hVform]; exact (p.vert (k * t)).2.nodup
  have hnd3 : ([pp, qq, zz] : List ℕ).Nodup := (List.nodup_append.mp hVnd).2.1
  have hdisj := (List.nodup_append.mp hVnd).2.2
  have hpq : pp ≠ qq := by intro h; subst h; simp at hnd3
  have hpz : pp ≠ zz := by intro h; subst h; simp at hnd3
  have hqz : qq ≠ zz := by intro h; subst h; simp at hnd3
  have hpps : pp ∉ s := fun hm => hdisj pp hm pp (by simp) rfl
  have hqqs : qq ∉ s := fun hm => hdisj qq hm qq (by simp) rfl
  have hzzs : zz ∉ s := fun hm => hdisj zz hm zz (by simp) rfl
  -- marker moved: zz ≠ a
  have hmarkerA : marker p (k * t - 1) = a := by
    rw [marker, hxeq]
    show (rho (a :: b :: c :: s)).getLastD 0 = a
    rw [show rho (a :: b :: c :: s) = (b :: c :: s) ++ [a] by
          show (a :: b :: c :: s).rotate 1 = _; simp, List.getLastD_concat]
  have hzza : zz ≠ a := by
    intro h; apply hmm.2; unfold markPres; rw [hmarkV, hmarkerA]; exact h
  -- membership pp, qq, zz ∈ {a, b, c}
  have hsym : (p.vert (k * t) : List ℕ).toFinset = (a :: b :: c :: s).toFinset := by
    have h1 := (p.vert (k * t)).2.toFinset_eq
    have h2 := (p.vert (k * t - 1)).2.toFinset_eq
    rw [hxeq] at h2; rw [h1, h2]
  have hmemabc : ∀ y, y ∈ (p.vert (k * t) : List ℕ) → y ∉ s → (y = a ∨ y = b ∨ y = c) := by
    intro y hy hys
    have hym : y ∈ (a :: b :: c :: s) := by
      have := List.mem_toFinset.mpr hy
      rw [hsym, List.mem_toFinset] at this; exact this
    rw [List.mem_cons, List.mem_cons, List.mem_cons] at hym
    rcases hym with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hys
  have hppmem := hmemabc pp (by rw [hVform]; exact List.mem_append_right _ (by simp)) hpps
  have hqqmem := hmemabc qq (by rw [hVform]; exact List.mem_append_right _ (by simp)) hqqs
  have hzzmem := hmemabc zz (by rw [hVform]; exact List.mem_append_right _ (by simp)) hzzs
  -- generic landing block-start reconstruction: block (t+r) = (s ++ [pp,qq]).rotate r ++ [zz]
  have hVerase : (p.vert (k * t) : List ℕ).erase zz = s ++ [pp, qq] := by
    have hznotin : zz ∉ (s ++ [pp, qq]) := by
      intro h
      rcases List.mem_append.mp h with h1 | h1
      · exact hzzs h1
      · rcases List.mem_cons.mp h1 with h2 | h2
        · exact hpz h2.symm
        · exact hqz (List.mem_singleton.mp h2).symm
    rw [hVform, show s ++ [pp, qq, zz] = (s ++ [pp, qq]) ++ [zz] by simp,
        List.erase_append_right _ hznotin, List.erase_cons_head, List.append_nil]
  have hblock : ∀ r, r ≤ k - 2 →
      (p.vert (k * (t + r)) : List ℕ) = (s ++ [pp, qq]).rotate r ++ [zz] := by
    intro r hr
    rw [hLland r hr, hmarkV, hVerase]
  -- range helper for landing blocks
  have hrange : ∀ pos, pos ≤ k - 2 → k * (t + pos) < p.numVerts := by
    intro pos hpos
    have := Nat.mul_le_mul (le_refl k) (show t + pos ≤ t + (k - 2) by omega)
    omega
  -- ==================================================================================
  -- Four families → collision (mm_a / mm_b at door-pos k−3, mm_c / mm_d at door-pos 0)
  -- ==================================================================================
  rcases hzzmem with hzv | hzv | hzv
  · exact hzza hzv
  · -- zz = b
    rcases hppmem with hpv | hpv | hpv
    · -- pp = a
      rcases hqqmem with hqv | hqv | hqv
      · exact hpq (hpv.trans hqv.symm)
      · exact hqz (hqv.trans hzv.symm)
      · -- qq = c  (mm_a): pos = s.length, src block 1
        have hbk := hblock s.length (by omega)
        rw [hpv, hqv, hzv] at hbk
        have hcls : rotClass (p.vert (k * (t + s.length)) : List ℕ)
            = rotClass (p.vert (k * g0) : List ℕ) := by
          rw [hbk]
          show rotClass (mmaBlock a b c s s.length) = rotClass (p.vert (k * g0) : List ℕ)
          rw [mm_a_share1 a b c s, ← hsrc1]
        exact collide s.length g0 (by omega) (hrange s.length (by omega)) hcls
    · exact hpz (hpv.trans hzv.symm)
    · -- pp = c
      rcases hqqmem with hqv | hqv | hqv
      · -- qq = a  (mm_b): pos = s.length, src block 2
        have hbk := hblock s.length (by omega)
        rw [hpv, hqv, hzv] at hbk
        have hcls : rotClass (p.vert (k * (t + s.length)) : List ℕ)
            = rotClass (p.vert (k * (g0 + 1)) : List ℕ) := by
          rw [hbk]
          show rotClass (mmbBlock a b c s s.length) = rotClass (p.vert (k * (g0 + 1)) : List ℕ)
          rw [mm_b_share a b c s, ← hsrc2]
        exact collide s.length (g0 + 1) (by omega) (hrange s.length (by omega)) hcls
      · exact hqz (hqv.trans hzv.symm)
      · exact hpq (hpv.trans hqv.symm)
  · -- zz = c
    rcases hppmem with hpv | hpv | hpv
    · -- pp = a
      rcases hqqmem with hqv | hqv | hqv
      · exact hpq (hpv.trans hqv.symm)
      · -- qq = b  (mm_c): pos = 0, src block 0
        have hbk := hblock 0 (by omega)
        rw [Nat.add_zero, hpv, hqv, hzv] at hbk
        have hcls : rotClass (p.vert (k * t) : List ℕ)
            = rotClass (p.vert (k * (t - 1)) : List ℕ) := by
          rw [hbk]
          show rotClass (mmcBlock a b c s 0) = rotClass (p.vert (k * (t - 1)) : List ℕ)
          rw [mm_c_share a b c s, ← hsrc0]
        exact collide 0 (t - 1) (by omega) (hrange 0 (by omega)) hcls
      · exact hqz (hqv.trans hzv.symm)
    · -- pp = b
      rcases hqqmem with hqv | hqv | hqv
      · -- qq = a  (mm_d): pos = 0, src block 1
        have hbk := hblock 0 (by omega)
        rw [Nat.add_zero, hpv, hqv, hzv] at hbk
        have hcls : rotClass (p.vert (k * t) : List ℕ)
            = rotClass (p.vert (k * g0) : List ℕ) := by
          rw [hbk]
          show rotClass (mmdBlock a b c s 0) = rotClass (p.vert (k * g0) : List ℕ)
          rw [mm_d_share a b c s, ← hsrc1]
        exact collide 0 g0 (by omega) (hrange 0 (by omega)) hcls
      · exact hpq (hpv.trans hqv.symm)
      · exact hqz (hqv.trans hzv.symm)
    · exact hpz (hpv.trans hzv.symm)

end ProofsFillPath

/-! ## §3. The `Hunter.Proved` capstone and the M1 soundness interface

`Proved.fill_path` is the reset-only-from-complete exclusion the M1 slab certificate's soundness
bridge names (`PROGRESS-m1.md` §3 "reset-from-incomplete" row, §5 "reset-only-from-complete
exclusion"): a marker-move (`reset`, cost 1) leaving a **complete** 2-loop cannot open a full
slab.  It is now **unconditional** at path level — no `hfresh`/`hfill` hypothesis survives.

`ProofsM1.lean`'s Theorem-2 capstones (`Proved.thm2_of_m1`, …) are parameterized by the abstract
bound `M1WalkBound k` (the §5 computational residual) and take **no** `hfill` hypothesis, so this
lemma discharges a *side condition of `M1WalkBound`'s justification* rather than shrinking the
capstones' hypothesis list; `thm2_of_m1` still depends on `M1WalkBound k` alone. -/

namespace Proved

open ProofsLedger

/-- **`fill_path` — the path-level fill exclusion** (`Hunter.Proved`).  In an exitless path, a
weight-3 marker-moving boundary into block `t` leaving a **complete** source 2-loop
(`IsComplete p (t−1)`) opens a landing 2-loop that can **never complete**:
`¬ IsComplete p (t + (k−2))`.  The opened slab fills to depth at most `k−3`.  Discharges the M1
reset-only-from-complete exclusion unconditionally (`PROGRESS-m1.md` §3/§5). -/
theorem fill_path {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + (k - 2)) < p.numVerts)
    (hmm : IsMarkerMove p t) (hcomp : IsComplete p (t - 1)) :
    ¬ IsComplete p (t + (k - 2)) :=
  ProofsFillPath.fill_path hk hp ht hN hmm hcomp

/-- **The M1 reset-exclusion, in the negated-conjunction form** the soundness bridge consumes
(`PROGRESS-m1.md` §5): a marker-move at `t` cannot simultaneously leave a complete source loop
and open a completing landing loop. -/
theorem no_reset_from_complete_opens_complete {k : ℕ} (hk : 3 ≤ k) {p : HPath k}
    (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t) (hN : k * (t + (k - 2)) < p.numVerts) :
    ¬ (IsMarkerMove p t ∧ IsComplete p (t - 1) ∧ IsComplete p (t + (k - 2))) :=
  fun ⟨hmm, hc1, hc2⟩ => ProofsFillPath.fill_path hk hp ht hN hmm hc1 hc2

end Proved

end Hunter

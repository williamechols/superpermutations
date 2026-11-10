/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsTheorem

/-!
# Theorem 2 — closing the last two residuals (`Hunter.ProofsLast`)

This final pass closes (or sharply isolates) the two named residuals of the extended potential
certificate (`Hunter/ProofsTheorem.lean`):

* **`DefectiveDeepExit k`** — *CLOSED* (vacuously true).  The extended certificate needs a defective
  slab that reaches door-depth `k−3` to eject via a *heavy* boundary.  We prove the sharper, true
  fact that **a defective slab never reaches door-depth `k−3` at all**: extending
  `ProofsFillPath.fill_path`'s collision argument one door deeper, the block at door-depth `k−3`
  (`= s.length`) of a marker-move-from-complete landing carries the 1-cycle class of an already
  visited *source* block (`mm_a_share1`/`mm_b_share`, or the entry itself for `mm_c`/`mm_d`),
  contradicting `no_reentry`.  Hence `IsDefective p t ∧ doorDepth p t = k−3` is impossible and
  `DefectiveDeepExit` holds vacuously — G2 is discharged.

* **`TerminalFrontierTail k`** — the terminal partial-block vertex-level endpoint gluing.  We deliver
  the clean arithmetic reduction `Dfrontier(N) ≤ Dfr((N−1)/k + 1)` (`Dfrontier_le_Dfr_succ`,
  verified `0` violations `k = 5…10`) which pins the residual to the single terminal demand
  increment `Dfr(T+1) − Dfr(T) ∈ {0,1}`; the `{1}`-phase payment is the demand-phase-alignment
  kernel (the `HPath(k−1)` meta-lift) that resists a `k`-uniform symbolic proof, so it is carried on.

Namespace `Hunter.ProofsLast`.  Zero `sorry`, zero new axioms.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsLast

open ProofsExitless ProofsLedger ProofsFill ProofsFillPath ProofsMeta ProofsMeta3 ProofsLanding
open ProofsRunExtract ProofsSynthesis ProofsConfinement ProofsPotential ProofsTheorem HPath

variable {k : ℕ}

/-! ## §1. The defective slab never reaches door-depth `k−3` (residual G2)

`defective_deep_false` replicates the coordinate bridge of `ProofsFillPath.fill_path` but instead of
assuming the landing loop *completes* (door-run to `k−2`), it assumes only that the door-run reaches
door-depth `k−3` (blocks `t+1 … t+(k−3)` all doors).  That is already enough: the block at
door-position `k−3 = s.length` (for `mm_a`/`mm_b`), or the entry itself at position `0` (for
`mm_c`/`mm_d`), collides with a visited source 1-cycle — contradiction.  This is the "one door
deeper" extension that `fill_path` (single-block non-completion, door-depth `≤ k−3`) is too weak to
give directly. -/

/-- **A defective door-run cannot reach door-depth `k−3`.**  A marker-move-from-complete landing at
block `t` (`IsMarkerMove p t`, `IsComplete p (t−1)`) whose door-run continues `k−3` blocks (blocks
`t+1 … t+(k−3)` all doors) is impossible: block `t+(k−3)` re-enters a source 1-cycle. -/
theorem defective_deep_false (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ} (ht : 1 ≤ t)
    (hN : k * (t + (k - 2)) < p.numVerts)
    (hmm : IsMarkerMove p t) (hcomp : IsComplete p (t - 1))
    (hdoorrun : ∀ i, 1 ≤ i → i ≤ k - 3 → IsDoor p (t + i)) :
    False := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  -- doorDepth of the complete source loop
  have hcomp' : doorDepth p (t - 1) = k - 2 := hcomp
  have hk2t : k - 2 ≤ t - 1 := by rw [← hcomp']; exact doorDepth_le p (t - 1)
  -- window bound for the k−3-deep landing door-run
  have hN3 : k * (t + (k - 3)) < p.numVerts := by
    have : k * (t + (k - 3)) ≤ k * (t + (k - 2)) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
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
  have hBfull : k * (t - 1) + (k - 1) < p.numVerts := by
    have hkt : k * t = k * (t - 1) + k := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h2 : k * t ≤ k * (t + (k - 2)) := Nat.mul_le_mul (le_refl k) (by omega)
    omega
  -- block t−1 = (b::c::s) ++ [a]
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
  -- The k−3-deep landing door-run and its block-start reconstruction
  -- ==================================================================================
  have hdoor_land : ∀ i, 1 ≤ i → i ≤ k - 3 →
      ew k (p.vert (k * (t + i) - 1)) (p.vert (k * (t + i))) = 2 := by
    intro i hi1 hi2
    have hd := hdoorrun i hi1 hi2
    rw [IsDoor, bw] at hd; exact hd
  have hLland := blockrun_eq hk2 hp t (k - 3) hN3 hdoor_land
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
  have hblock : ∀ r, r ≤ k - 3 →
      (p.vert (k * (t + r)) : List ℕ) = (s ++ [pp, qq]).rotate r ++ [zz] := by
    intro r hr
    rw [hLland r hr, hmarkV, hVerase]
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

/-- **`DefectiveDeepExit k` — CLOSED (vacuously true).**  A defective slab never reaches door-depth
`k−3`: its door-run root `r = loopStart p t` opened via marker-move-from-complete, and if the run
reached door-depth `k−3` the block at that depth would re-enter a visited source 1-cycle
(`defective_deep_false`).  So the hypothesis `doorDepth p t = k−3` is impossible under
`IsDefective p t`, and the residual holds by `False.elim` — the extended certificate's deepest
defective eject case is unreachable, discharging G2. -/
theorem defectiveDeepExit (hk : 4 ≤ k) : DefectiveDeepExit k := by
  intro p hp t hN hdef hdd _hnd
  -- root of the defective door-run
  set r : ℕ := loopStart p t with hr
  have hrv : r = t - (k - 3) := by rw [hr, loopStart, hdd]
  have hle3 : k - 3 ≤ t := by rw [← hdd]; exact doorDepth_le p t
  have htr : t = r + (k - 3) := by omega
  -- IsDefective p t = mm-from-complete at r
  obtain ⟨hmm, hcomp⟩ := hdef
  -- r ≥ 1 (else IsComplete p 0 forces k = 2)
  have ht1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso
      have hc : doorDepth p (r - 1) = k - 2 := hcomp
      rw [h0] at hc; simp only [Nat.zero_sub, doorDepth_zero] at hc; omega
    · exact hpos
  -- window: r + (k−2) = t + 1
  have hNr : k * (r + (k - 2)) < p.numVerts := by
    have hidx : r + (k - 2) = t + 1 := by omega
    rw [hidx]; exact hN
  -- the door-run reaches door-depth k−3
  have hdoorrun : ∀ i, 1 ≤ i → i ≤ k - 3 → IsDoor p (r + i) := by
    intro i hi1 hi2
    have hj : (k - 3) - i < doorDepth p t := by rw [hdd]; omega
    have hd := isDoor_of_lt_doorDepth p t ((k - 3) - i) hj
    have hidx : t - ((k - 3) - i) = r + i := by omega
    rwa [hidx] at hd
  exact (defective_deep_false hk hp ht1 hNr hmm hcomp hdoorrun).elim

end ProofsLast

/-! ## §2. The `Hunter.Proved` capstones with G2 discharged

`DefectiveDeepExit` is now a theorem (`ProofsLast.defectiveDeepExit`), so it drops out of every
hypothesis list.  The Theorem-2 / Theorem-1 capstones of `Hunter/ProofsTheorem.lean` retain **only**
the terminal-tail residual `TerminalFrontierTail` (G3) plus the numeric guards. -/

namespace Proved

open ProofsClose ProofsTheorem ProofsRecursion ProofsM1

variable {k : ℕ}

/-- **Global G2 discharge**: `DefectiveDeepExitAll` is a theorem. -/
theorem defectiveDeepExitAll : DefectiveDeepExitAll :=
  fun _k hk => ProofsLast.defectiveDeepExit hk

/-- **`M1WalkBound k` from the single remaining residual G3.**  With `DefectiveDeepExit` discharged,
`m1WalkBound_of_defExit` carries only `TerminalFrontierTail k`. -/
theorem m1WalkBound_of_tail (hk : 4 ≤ k) (hG3 : TerminalFrontierTail k) : M1WalkBound k :=
  m1WalkBound_of_defExit hk (ProofsLast.defectiveDeepExit hk) hG3

/-- **Theorem 2** (verbatim `Statements.thm2` conclusion) from the single residual G3 + numeric
guards.  `DefectiveDeepExit` is discharged; only `TerminalFrontierTail` remains. -/
theorem thm2_of_tail {ℓ : ℕ} (hk : 4 ≤ k) (hG3 : TerminalFrontierTail k)
    (hℓ : HasExitlessPath k ℓ) : j k ℓ ≤ iExitless k ℓ :=
  thm2_final hk (ProofsLast.defectiveDeepExit hk) hG3 hℓ

/-- **Theorem 2 for all `k ≥ 3`** from the single residual G3.  `k = 3, 4` are the unconditional
base `ProofsRecursion.thm2_small`; `k ≥ 5` carries only `TerminalFrontierTail k` (G2 discharged).
So the sole residual of Theorem 2 over the full range is `TerminalFrontierTail` at `k ≥ 5`. -/
theorem thm2_ge3_of_tail {ℓ : ℕ} (hk : 3 ≤ k) (hG3 : 5 ≤ k → TerminalFrontierTail k)
    (hℓ : HasExitlessPath k ℓ) : j k ℓ ≤ iExitless k ℓ := by
  rcases Nat.lt_or_ge k 5 with h4 | h5
  · exact ProofsRecursion.thm2_small hk (by omega) hℓ
  · exact thm2_of_tail (by omega) (hG3 h5) hℓ

/-- **The global M1 slab bound** from G3 alone (base `M1WalkBound 3`, G2 discharged, G1 baked in). -/
theorem m1WalkBoundAll_of_tail (hbase : M1WalkBound 3) (hG3 : TerminalFrontierTailAll) :
    Proved.M1WalkBoundAll :=
  m1WalkBoundAll_of_defExit hbase defectiveDeepExitAll hG3

/-- **thm1v1** from G3 alone (G2 discharged; base + numeric leaves carried as in the existing
chain). -/
theorem thm1v1_of_tail (hbase : M1WalkBound 3) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  thm1v1_theorem hbase defectiveDeepExitAll hG3 hproof hexists

/-- **thm1v2** from G3 alone (G2 discharged). -/
theorem thm1v2_of_tail (hbase : M1WalkBound 3) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  thm1v2_theorem hbase defectiveDeepExitAll hG3 hproof hexists

/-- **eq-weak** from G3 alone (G2 discharged). -/
theorem eq_weak_of_tail (hbase : M1WalkBound 3) (hG3 : TerminalFrontierTailAll)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ (k.factorial : ℝ) + ((k - 1).factorial : ℝ) + ((k - 2).factorial : ℝ)
        + ((k - 4).factorial : ℝ) - 2 * ((k - 5).factorial : ℝ) - C * ((k - 6).factorial : ℝ) :=
  eq_weak_theorem hbase defectiveDeepExitAll hG3 hproof hexists

end Proved

end Hunter

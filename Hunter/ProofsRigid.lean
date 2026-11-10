/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsInduction

/-!
# The rigidity bridge — recasting `TerminalFrontierTail` as the sharp block bound

The terminal-tail residual `ProofsClose.TerminalFrontierTail k` (G3) is, by
`ProofsTail.terminalFrontierTail_iff_excessFrontier`, logically equivalent to the entire open
content of Theorem 2 in the recursion region.  This file pins that residual down to a single crisp
arithmetic statement and proves the *arithmetic half* of the reduction, sorry-free and axiom-clean.

## The clean frontier↔block identity (this file's main new fact)

`ProofsClose.Dfrontier_block_eq` shows the length-scale frontier demand equals the block-scale demand
`Dfr` at **block-aligned** lengths, `Dfrontier k (k·b) = Dfr k b`.  We generalize it to **every**
length:

> **`Dfrontier_eq_Dfr_ceil : Dfrontier k m = Dfr k (m ⌈/⌉ k)`**  for all `m ≥ 1` (`k ≥ 4`).

Numerically verified an exact equality for all `m` at `k = 5..9` (campaign/rigid).  The proof is a
strong induction on `m` mirroring `Dfr`'s own recursion: in the base window it is the nested-ceiling
identity `(m ⌈/⌉ k) ⌈/⌉ (k−1) = m ⌈/⌉ (k(k−1))` (`ceilDiv_ceilDiv`); in the recursion region the
period of `j` (`j_rec_unfold_one`, with `j k ℓ₀` pinned by `ProofsWalk.j_glue` at `b = Mper`) matches
the period of `Dfr` (`Dfr_shift_rec`).

## The residual, made crisp

With the identity, `TerminalFrontierTail k` is *exactly* the "opened-block" demand bound

> **`ExcessBlockCeil k := ∀ p exitless, 0 < |p| → Dfr k (|p| ⌈/⌉ k) ≤ excess p`**,

i.e. `excess ≥ Dfr(b)` at the **true block count** `b = ⌈|p|/k⌉`.  Via `Dfr_le_iff_le_G` this is
`b ≤ G(excess)` — PROOF.md's headline `F_E ≤ G(E)` at the honest block count.  The repository's
unconditional walk bound (`blockCount_le_G_excess`) delivers `(|p|−1)/k = b − 1 ≤ G(excess)`, exactly
**one block short**: the terminal boundary `k·b` lies at (or past) `|p|`, so the walk never charges the
last opened block's demand.  Closing that `−1` is the whole remaining content of Theorem 2.

Namespace `Hunter.ProofsRigid`.  **Zero `sorry`, zero new axioms.**
-/

namespace Hunter

open scoped Classical

namespace ProofsRigid

open ProofsPotential ProofsRecursion ProofsClose ProofsInduction Proved HPath

variable {k : ℕ}

/-! ## §1. The frontier↔block identity `Dfrontier k m = Dfr k (m ⌈/⌉ k)` -/

/-- `(m − k·q) ⌈/⌉ k = m ⌈/⌉ k − q` when `k·q ≤ m` (period shift for ceiling division). -/
theorem ceilDiv_sub_mul (hk : 1 ≤ k) {m q : ℕ} (hm : 1 ≤ m) (hle : k * q ≤ m) :
    (m - k * q) ⌈/⌉ k = m ⌈/⌉ k - q := by
  rcases Nat.eq_zero_or_pos (m - k * q) with h0 | hpos
  · -- m = k*q, exact multiple
    have hmeq : m = k * q := by omega
    rw [h0, hmeq, Proved.ceilDiv_of_dvd (by omega) ⟨q, rfl⟩, Nat.mul_div_cancel_left q (by omega),
        Nat.sub_self, Nat.ceilDiv_eq_add_pred_div, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
  · rw [ceilDiv_succ_pred (by omega) (by omega), ceilDiv_succ_pred hm (by omega)]
    have hqle : q ≤ (m - 1) / k := by
      rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]; omega
    have hkey : (m - k * q - 1) / k = (m - 1) / k - q := by
      have h1 : m - k * q - 1 = (m - 1) - k * q := by omega
      rw [h1]
      have hmod : (m - 1) % k < k := Nat.mod_lt _ (by omega)
      have hexp : (m - 1) - k * q = k * ((m - 1) / k - q) + (m - 1) % k := by
        have hmul : k * ((m - 1) / k - q) = k * ((m - 1) / k) - k * q := by rw [Nat.mul_sub]
        have hmle : k * q ≤ k * ((m - 1) / k) := Nat.mul_le_mul_left k hqle
        have := Nat.div_add_mod (m - 1) k
        omega
      rw [hexp, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < k),
          Nat.div_eq_of_lt hmod, Nat.zero_add]
    omega

/-- `Dfr k (Mper k) = k − 3`. -/
theorem Dfr_Mper (hk : 4 ≤ k) : Dfr k (Mper k) = k - 3 := by
  have hle : Mper k ≤ (k - 1) * (k - 2) := by rw [Mper]; omega
  rw [Dfr_base hle, Mper]
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 4 := ⟨k - 4, by omega⟩
  show ((a + 3) * (a + 2) - 1 - 1) / (a + 3) = a + 1
  have hnum : (a + 3) * (a + 2) - 1 - 1 = (a + 1) + (a + 3) * (a + 1) := by
    have h1 : (a + 3) * (a + 2) = a * a + 5 * a + 6 := by ring
    have h2 : (a + 3) * (a + 1) = a * a + 4 * a + 3 := by ring
    omega
  rw [hnum, Nat.add_mul_div_left _ _ (by omega : 0 < a + 3), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]

/-- **Additive frontier↔block identity** (the `j_glue` shape for *all* lengths).
`j k m = Dfr k (m ⌈/⌉ k) + (m − 1) + (m ⌈/⌉ k − 1)` for `m ≥ 1`. -/
theorem j_frontier_eq (hk : 4 ≤ k) :
    ∀ m, 1 ≤ m → j k m = Dfr k (m ⌈/⌉ k) + (m - 1) + (m ⌈/⌉ k - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm1
    have hkpos : 0 < k := by omega
    have hkk1pos : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    set base := k * (k - 1) * (k - 2) with hbase
    have hB1 : 1 ≤ m ⌈/⌉ k := by
      rw [ceilDiv_succ_pred hm1 hkpos]; exact Nat.le_add_left 1 _
    by_cases hbaseR : m ≤ base
    · -- base window
      have hble : m ⌈/⌉ k ≤ (k - 1) * (k - 2) := by
        rw [ceilDiv_succ_pred hm1 hkpos]
        have hstep : (m - 1) / k ≤ (base - 1) / k := Nat.div_le_div_right (by omega)
        have hb : (base - 1) / k = (k - 1) * (k - 2) - 1 := by
          have hbeq : base = k * ((k - 1) * (k - 2)) := by rw [hbase]; ring
          rw [hbeq]
          set X := (k - 1) * (k - 2) with hXdef
          have hXpos : 1 ≤ X := by rw [hXdef]; exact Nat.mul_pos (by omega) (by omega)
          have hkX : k ≤ k * X := Nat.le_mul_of_pos_right k hXpos
          rw [show k * X - 1 = k * (X - 1) + (k - 1) from by
                rw [Nat.mul_sub, Nat.mul_one]; omega,
              Nat.mul_add_div hkpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
        have hXpos : 1 ≤ (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
        omega
      -- `m ⌈/⌉ (k(k-1)) = Dfr k (m ⌈/⌉ k) + 1` (nested ceiling + `Dfr_base`)
      have hDBval : m ⌈/⌉ (k * (k - 1)) = Dfr k (m ⌈/⌉ k) + 1 := by
        rw [Dfr_base hble, ← ProofsConfinement.ceilDiv_ceilDiv hkpos (by omega),
            ceilDiv_succ_pred hB1 (by omega)]
      have hj : j k m = m + (m ⌈/⌉ k) + (m ⌈/⌉ (k * (k - 1))) - 3 := j_base (Or.inl hbaseR)
      omega
    · -- recursion region m > base
      rw [Nat.not_le] at hbaseR
      have hbaseR' : k * (k - 1) * (k - 2) < m := by rw [← hbase]; exact hbaseR
      have hjr : j k m = j k (m - ell0 k) + j k (ell0 k) + 3 :=
        j_rec_unfold_one (by omega) hbaseR'
      have hell0 : ell0 k = k * Mper k := ProofsWalk.ell0_eq_k_mul_Mper (by omega)
      have hMper_pos : 1 ≤ Mper k := ProofsPotential.Mper_pos (by omega)
      have hell0_le : ell0 k ≤ base := by rw [hbase, ell0]; omega
      have hml : 1 ≤ m - ell0 k := by omega
      have hmlt : m - ell0 k < m := by
        have : 1 ≤ ell0 k := ProofsRecursion.ell0_pos (by omega); omega
      have hshift : (m - ell0 k) ⌈/⌉ k = m ⌈/⌉ k - Mper k := by
        rw [hell0]; exact ceilDiv_sub_mul (by omega) hm1 (by rw [← hell0]; omega)
      -- b := m ⌈/⌉ k > (k-1)(k-2)
      have hbgt : (k - 1) * (k - 2) < m ⌈/⌉ k := by
        rw [ceilDiv_succ_pred hm1 hkpos]
        have hbasek : base / k = (k - 1) * (k - 2) := by
          rw [hbase, show k * (k - 1) * (k - 2) = k * ((k - 1) * (k - 2)) from by ring,
              Nat.mul_div_cancel_left _ hkpos]
        have hstep : base / k ≤ (m - 1) / k := Nat.div_le_div_right (by omega)
        omega
      have hMperv : Mper k = (k - 1) * (k - 2) - 1 := rfl
      -- IH at m - ℓ₀
      have hIH := ih (m - ell0 k) hmlt hml
      rw [hshift] at hIH
      -- j k ℓ₀ via j_glue at Mper
      have hjg : j k (k * Mper k) = Dfr k (Mper k) + (k * Mper k - 1) + (Mper k - 1) :=
        ProofsWalk.j_glue hk hMper_pos
      rw [← hell0] at hjg
      have hDfrM : Dfr k (Mper k) = k - 3 := Dfr_Mper hk
      -- block-scale recursion for Dfr k B
      have hDfrb : Dfr k (m ⌈/⌉ k) = Dfr k (m ⌈/⌉ k - Mper k) + (k - 2) :=
        Dfr_shift_rec (by omega) hbgt
      -- assemble (all subtractions handled by omega with the size facts)
      omega

/-- **The frontier↔block identity.**  `Dfrontier k m = Dfr k (m ⌈/⌉ k)` for every `m ≥ 1`
(`k ≥ 4`) — the generalization of `ProofsClose.Dfrontier_block_eq` from block-aligned lengths to
*all* lengths. -/
theorem Dfrontier_eq_Dfr_ceil (hk : 4 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    Dfrontier k m = Dfr k (m ⌈/⌉ k) := by
  have hkpos : 0 < k := by omega
  have hB1 : 1 ≤ m ⌈/⌉ k := by
    rw [ceilDiv_succ_pred hm hkpos]; exact Nat.le_add_left 1 _
  have h := j_frontier_eq hk m hm
  rw [Dfrontier]
  set B := m ⌈/⌉ k with hBdef
  clear_value B
  clear hBdef
  omega

/-! ## §2. The residual made crisp: `ExcessBlockCeil` (the opened-block demand) -/

/-- **The opened-block demand bound.**  `excess ≥ Dfr` at the **true block count**
`b = ⌈|p|/k⌉` (which counts the terminal opened block, not just the completed ones).  By
`Dfrontier_eq_Dfr_ceil` this is *exactly* the frontier bound `Dfrontier(|p|) ≤ excess`, hence
`↔ ExcessFrontier k ↔ TerminalFrontierTail k` — the whole open content of Theorem 2. -/
def ExcessBlockCeil (k : ℕ) : Prop :=
  ∀ p : HPath k, p.Exitless → 0 < p.numVerts → Dfr k (p.numVerts ⌈/⌉ k) ≤ excess p

/-- **The reduction (arithmetic half, PROVED).**  `ExcessBlockCeil k → TerminalFrontierTail k`.
The frontier demand at `|p|` equals `Dfr k (⌈|p|/k⌉)` (`Dfrontier_eq_Dfr_ceil`), so the
opened-block bound delivers it directly — the last-full-block hypothesis of `TerminalFrontierTail`
is not even used. -/
theorem terminalFrontierTail_of_blockCeil (hk : 4 ≤ k) (hbc : ExcessBlockCeil k) :
    TerminalFrontierTail k := by
  intro p hp h0 _
  have hj := j_frontier_eq hk p.numVerts h0
  have hbound := hbc p hp h0
  omega

/-- The block count `⌈|p|/k⌉` is positive for a nonempty path. -/
theorem one_le_ceil {p : HPath k} (hk : 4 ≤ k) (h0 : 0 < p.numVerts) : 1 ≤ p.numVerts ⌈/⌉ k := by
  rw [ceilDiv_succ_pred h0 (by omega)]; exact Nat.le_add_left 1 _

/-- **`ExcessBlockCeil` in `G`-form.**  Via the `Dfr`/`G` inversion (`Dfr_le_iff_le_G`),
`ExcessBlockCeil k` says the true block count `⌈|p|/k⌉` is `≤ G(excess)` — PROOF.md's headline
`F_E ≤ G(E)` read at the honest block count. -/
theorem blockCeil_iff_G (hk : 4 ≤ k) :
    ExcessBlockCeil k ↔
      ∀ p : HPath k, p.Exitless → 0 < p.numVerts → p.numVerts ⌈/⌉ k ≤ G k (excess p) := by
  constructor
  · intro h p hp h0
    exact (Dfr_le_iff_le_G hk _ (one_le_ceil hk h0) _).mp (h p hp h0)
  · intro h p hp h0
    exact (Dfr_le_iff_le_G hk _ (one_le_ceil hk h0) _).mpr (h p hp h0)

/-- **The exact off-by-one.**  The repository's *unconditional* walk bound
(`ProofsInduction.blockCount_le_G_excess`) delivers `⌈|p|/k⌉ − 1 ≤ G(excess)` — precisely **one
block short** of `ExcessBlockCeil`'s `⌈|p|/k⌉ ≤ G(excess)`.  The missing block is the terminal
*opened* block, whose demand boundary `k·⌈|p|/k⌉` lies at (or beyond) `|p|`, so the block-boundary
walk never charges it.  Closing that `−1` is the entire remaining content of Theorem 2. -/
theorem blockCeil_pred_le_G (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless) (h0 : 0 < p.numVerts) :
    p.numVerts ⌈/⌉ k - 1 ≤ G k (excess p) := by
  have hbc := blockCount_le_G_excess hk hp h0
  rwa [ceilDiv_succ_pred h0 (by omega), Nat.add_sub_cancel]

/-! ## §3. Conditional capstones on the single residual `ExcessBlockCeil` -/

/-- `ExcessFrontier k` from the crisp residual. -/
theorem excessFrontier_of_blockCeil (hk : 4 ≤ k) (hbc : ExcessBlockCeil k) :
    ProofsRecursion.ExcessFrontier k :=
  Proved.excess_frontier_chart hk (terminalFrontierTail_of_blockCeil hk hbc)

/-- **Theorem 2** (verbatim `Statements.thm2` conclusion) from the crisp residual, numeric guards
`hk`/`hℓ` only. -/
theorem thm2_of_blockCeil {ℓ : ℕ} (hk : 4 ≤ k) (hbc : ExcessBlockCeil k)
    (hℓ : HasExitlessPath k ℓ) : j k ℓ ≤ iExitless k ℓ :=
  Proved.thm2_of_chart hk (terminalFrontierTail_of_blockCeil hk hbc) hℓ

end ProofsRigid

end Hunter


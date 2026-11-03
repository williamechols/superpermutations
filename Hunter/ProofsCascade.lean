/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsFinal

/-!
# Theorem 2 — the CASCADE PHASE CLOSURE (partial closure of `JumpLoopEntryFree`)

This file formalizes the *intermediate-violation lever* that shrinks the combined-induction
residual `ProofsFinal.JumpLoopEntryFree k` to the single door-phase residue `n ≡ 1 (mod k)`,
where `n = |p| − ℓ₀` is the tight-prefix (jump) length.  The lever was verified at zero mismatch
for `k = 5,6,7,8` (`scratchpad/campaign/cascade/reduction.py`, `forward_window.py`).

## The argument (verified 0-mismatch, `k = 5,6,7,8`)

In the combined induction's residual branch — tight prefix `q` at jump length `n = |p| − ℓ₀`,
`doorDepth (winA p) = 0` — the top `ℓ₀`-window carries exactly `k − 2` units of demand
(`Dfr(|p|) = Dfr(n) + (k − 2)`, the `D`-recursion).  Let `Dfr(m) := j_k(m) − (m−1) − (⌈m/k⌉−1)`
be the frontier demand (so `ExcessFrontier k ↔ excess q ≥ Dfr(|q|)`).  The *last* demand jump `m*`
in `(n, |p|]` lands strictly interior (`m* < |p|`) exactly when `n ≢ 1 (mod k)`, and then the
length is closed **without the residual**: at `m = |p| − 1` the induction hypothesis gives
`excess(prefix_m) ≥ Dfr(m) = Dfr(n) + (k − 2) = excess q + (k − 2)`, and `excess p ≥ excess(prefix_m)`
by monotonicity — the required `k − 2` payment, unconditionally.

## Index-arithmetic calibration (`k = 5`, `k = 6`; from `reduction.py`)

`ℓ₀ = k(k−1)(k−2) − k`, `base = k(k−1)(k−2)`, `ℓ₀ ≡ 0 (mod k)`, `ℓ₀ ≡ k(k−2) (mod k(k−1))`.

* **`k = 5`** (`base = 60`, `ℓ₀ = 55`): jump length `n = 62` (`n % 5 = 2 ≠ 1`), `|p| = 117`.
  `Dfr(62) = Dfr(117) − 3`, and `Dfr(116) − Dfr(62) = 3 = k − 2` (last jump interior) — closed.
  Contrast `n = 61` (`n % 5 = 1`): `Dfr(116) − Dfr(61) = 2 = k − 3` — survives (the residual).
* **`k = 6`** (`base = 120`, `ℓ₀ = 114`): `n = 122` (`n % 6 = 2`), `|p| = 236`,
  `Dfr(235) − Dfr(122) = 4 = k − 2` — closed; `n = 121` (`n % 6 = 1`), `Dfr(235) − Dfr(121) = 3 = k − 3`.

The two clean identities driving the Lean proof, both verified 0-mismatch for `k = 5,6,7,8`:

* **`dfr_shift`** — `Dfr(m) = Dfr(m − ℓ₀) + (k − 2)` for every `m > base` (a *single* `j`-unfold);
* **`sstep_zero`** — `Dfr(n) = Dfr(n − 1)` for every `n > base` with `n % k ≠ 1` (no jump hypothesis;
  a downward `ℓ₀`-induction bottoming out at the base closed form `Dfr(x) = ⌈x/(k(k−1))⌉ − 1`).

Together: for jump length `n ≢ 1 (mod k)`, `Dfr(|p|−1) = Dfr(n−1) + (k−2) = Dfr(n) + (k−2)`.

Namespace `Hunter.ProofsCascade` (helpers); the residual restriction and capstones live in
`Hunter.Proved`.  Sorry-free, axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsCascade

open ProofsLedger ProofsAssembly ProofsRecursion ProofsWindow
open ProofsRFrame ProofsExcess ProofsMeta6 ProofsFinal
open HPath

variable {k : ℕ}

/-! ## §1. Excess monotonicity along prefixes -/

/-- **Excess is monotone along prefixes.**  The `excess` of a length-`m` prefix never exceeds the
excess of the whole path — each layer `edgeCountGe · r` is monotone (`edgeCountGe_prefix_le`). -/
theorem excess_prefix_le {p r : HPath k} {m : ℕ} (hpre : r.verts = p.verts.take m)
    (hmle : m ≤ p.numVerts) (hrn : r.numVerts = m) : excess r ≤ excess p := by
  rw [excess, excess]
  exact Finset.sum_le_sum (fun s _ => edgeCountGe_prefix_le hpre hmle hrn s)

/-! ## §2. The frontier demand `Dfr` in additive (subtraction-clean) form -/

/-- **Base-region frontier value.**  For `1 ≤ x ≤ k(k−1)(k−2)` the `j`-value splits exactly as
`j_k(x) = (x−1) + (⌈x/k⌉−1) + (⌈x/(k(k−1))⌉−1)`; hence `Dfr(x) = ⌈x/(k(k−1))⌉ − 1`. -/
theorem base_frontier (hk : 3 ≤ k) {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ k * (k - 1) * (k - 2)) :
    j k x = (x - 1) + (x ⌈/⌉ k - 1) + (x ⌈/⌉ (k * (k - 1)) - 1) := by
  have hk0 : 0 < k := by omega
  have h1 : 1 ≤ x ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred hx1 hk0]; exact Nat.le_add_left 1 _
  have h2 : 1 ≤ x ⌈/⌉ (k * (k - 1)) := by
    rw [Proved.ceilDiv_succ_pred hx1 (Nat.mul_pos hk0 (by omega))]; exact Nat.le_add_left 1 _
  rw [j_base (Or.inl hxle)]; omega

/-- **The single `ℓ₀`-window demand shift.**  For `m` in the recursion region a *single*
`j`-unfold gives `Dfr(m) = Dfr(m − ℓ₀) + (k − 2)`, stated additively (subtraction-clean). -/
theorem dfr_shift (hk : 3 ≤ k) (m : ℕ) (hm : k * (k - 1) * (k - 2) < m) :
    j k m + (m - ell0 k - 1) + ((m - ell0 k) ⌈/⌉ k - 1)
      = j k (m - ell0 k) + (m - 1) + (m ⌈/⌉ k - 1) + (k - 2) := by
  have hk0 : 0 < k := by omega
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hm2 : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm2
  have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
  have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
  have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
  -- j at ℓ₀ via the base closed form
  have hje0 : j k (ell0 k) = (ell0 k - 1) + (ell0 k / k - 1) + ((k - 2) - 1) := by
    rw [base_frontier hk (by omega : 1 ≤ ell0 k) he0base,
        Proved.ceilDiv_of_dvd hk0 hdvd, ceilDiv_ell0 hk]
  have hjrec : j k m = j k (m - ell0 k) + j k (ell0 k) + 3 := j_rec_unfold_one hk hm
  have hmL : m = (m - ell0 k) + ell0 k := by omega
  have hcdm : m ⌈/⌉ k = (m - ell0 k) ⌈/⌉ k + ell0 k / k := by
    conv_lhs => rw [hmL]
    exact ceilDiv_add_dvd hk0 hdvd
  have hL1 : 1 ≤ m - ell0 k := by omega
  have hcdL1 : 1 ≤ (m - ell0 k) ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred hL1 hk0]; exact Nat.le_add_left 1 _
  have hcdm1 : 1 ≤ m ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred (by omega : 1 ≤ m) hk0]; exact Nat.le_add_left 1 _
  have he0k1 : 1 ≤ ell0 k / k := (Nat.one_le_div_iff hk0).mpr hkle0
  omega

/-! ## §3. Ceiling / modular micro-lemmas for `sstep_zero` -/

/-- **Ceiling plateau.**  `⌈x/D⌉ = ⌈(x−1)/D⌉` whenever `x % D ≠ 1` (for `2 ≤ x`, `2 ≤ D`):
the ceiling increments only across `x ≡ 1 (mod D)`. -/
theorem ceilDiv_eq_pred {x D : ℕ} (hx : 2 ≤ x) (hD : 2 ≤ D) (hmod : x % D ≠ 1) :
    x ⌈/⌉ D = (x - 1) ⌈/⌉ D := by
  rw [Proved.ceilDiv_succ_pred (by omega : 1 ≤ x) (by omega : 0 < D),
      Proved.ceilDiv_succ_pred (by omega : 1 ≤ x - 1) (by omega : 0 < D)]
  have hnd : ¬ D ∣ (x - 1) := by
    rintro ⟨c, hc⟩
    apply hmod
    rw [show x = 1 + D * c from by omega, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [show x - 1 - 1 = x - 2 from by omega]
  have hs : ((x - 2) + 1) / D = (x - 2) / D + (if D ∣ ((x - 2) + 1) then 1 else 0) :=
    Nat.succ_div ..
  rw [show (x - 2) + 1 = x - 1 from by omega, if_neg hnd, Nat.add_zero] at hs
  rw [hs]

/-- **Modular descent.**  `n % k ≠ 1` forces `(n − ℓ₀) % (k(k−1)) ≠ 1`: a residue `1 (mod k(k−1))`
would reduce to `1 (mod k)` (as `k ∣ k(k−1)`), and `ℓ₀ ≡ 0 (mod k)` transports it to `n % k = 1`. -/
theorem mod_reduce (hk : 3 ≤ k) {n : ℕ} (hmod : n % k ≠ 1) (hge : ell0 k ≤ n) :
    (n - ell0 k) % (k * (k - 1)) ≠ 1 := by
  intro hc
  apply hmod
  have hkdvd : k ∣ k * (k - 1) := ⟨k - 1, rfl⟩
  have h1 : (n - ell0 k) % k = 1 := by
    rw [← Nat.mod_mod_of_dvd (n - ell0 k) hkdvd, hc]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨t, ht⟩ := k_dvd_ell0 hk
  have hnmod : n % k = (n - ell0 k) % k := by
    conv_lhs => rw [show n = (n - ell0 k) + k * t from by omega]
    rw [Nat.add_mul_mod_self_left]
  rw [hnmod, h1]

/-! ## §4. The single-step plateau `Dfr(n) = Dfr(n−1)` for `n ≢ 1 (mod k)` -/

/-- **Single-step plateau.**  For every `n` in the recursion region with `n % k ≠ 1`, the frontier
demand does not increase at `n`: `Dfr(n) = Dfr(n − 1)` (additive form).  Proved by downward
`ℓ₀`-induction: `dfr_shift` reduces both `Dfr(n)` and `Dfr(n−1)` by one window; the reduced pair is
handled by the IH (still in the recursion region) or by the base closed form (`ceilDiv_eq_pred`,
`mod_reduce`).  No jump-length hypothesis is used. -/
theorem sstep_zero (hk : 3 ≤ k) :
    ∀ n, k * (k - 1) * (k - 2) < n → n % k ≠ 1 →
      j k n + (n - 2) + ((n - 1) ⌈/⌉ k - 1) = j k (n - 1) + (n - 1) + (n ⌈/⌉ k - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmod
    have hk0 : 0 < k := by omega
    have he0 := ell0_pos hk
    have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
    have hm2 : 2 ≤ (k - 1) * (k - 2) := by
      have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
    have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm2
    have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
    have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
    have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
    -- `base + 1 ≡ 1 (mod k)`, so `n % k ≠ 1` and `n > base` give `n ≥ base + 2`
    have hn2 : k * (k - 1) * (k - 2) + 2 ≤ n := by
      rcases Nat.lt_or_ge n (k * (k - 1) * (k - 2) + 2) with h | h
      · exfalso; apply hmod
        rw [show n = 1 + ((k - 1) * (k - 2)) * k from by
              have : k * (k - 1) * (k - 2) = ((k - 1) * (k - 2)) * k := by ring
              omega,
            Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      · exact h
    -- shift both `Dfr(n)` and `Dfr(n−1)` down one window
    have hDSn := dfr_shift hk n hn
    have hDSn1 := dfr_shift hk (n - 1) (by omega)
    -- canonicalise `(n−1) − ℓ₀  =  (n − ℓ₀) − 1`
    have hcanon : n - 1 - ell0 k = n - ell0 k - 1 := by omega
    rw [hcanon] at hDSn1
    have hpmod : (n - ell0 k) % k ≠ 1 := by
      obtain ⟨t, ht⟩ := k_dvd_ell0 hk
      have : n % k = (n - ell0 k) % k := by
        conv_lhs => rw [show n = (n - ell0 k) + k * t from by omega]
        rw [Nat.add_mul_mod_self_left]
      rw [← this]; exact hmod
    by_cases hbc : n - ell0 k ≤ k * (k - 1) * (k - 2)
    · -- base region: closed form + ceiling plateau
      have hbfL := base_frontier hk (show 1 ≤ n - ell0 k by omega) hbc
      have hbfL1 := base_frontier hk (show 1 ≤ n - ell0 k - 1 by omega) (by omega)
      have hmodL : (n - ell0 k) % (k * (k - 1)) ≠ 1 := mod_reduce hk hmod (by omega)
      have hkk1 : 2 ≤ k * (k - 1) :=
        le_trans (by norm_num) (Nat.mul_le_mul (show 3 ≤ k from hk) (show 1 ≤ k - 1 by omega))
      have hcdeq : (n - ell0 k) ⌈/⌉ (k * (k - 1)) = (n - ell0 k - 1) ⌈/⌉ (k * (k - 1)) :=
        ceilDiv_eq_pred (by omega) hkk1 hmodL
      omega
    · -- recursion region: induction hypothesis at `n − ℓ₀`
      have hihL := ih (n - ell0 k) (by omega) (by omega) hpmod
      omega

/-- **Modular descent (base region).**  `x % k ≠ 1` forces `x % (k(k−1)) ≠ 1` (as `k ∣ k(k−1)`). -/
theorem mod_kk1_ne_one (hk : 3 ≤ k) {x : ℕ} (hmod : x % k ≠ 1) : x % (k * (k - 1)) ≠ 1 := by
  intro hc
  apply hmod
  have hkdvd : k ∣ k * (k - 1) := ⟨k - 1, rfl⟩
  rw [← Nat.mod_mod_of_dvd x hkdvd, hc]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Single-step plateau, all regions.**  For every `n ≥ 2` with `n % k ≠ 1`, `Dfr(n) = Dfr(n − 1)`
(additive).  In the recursion region this is `sstep_zero`; in the base region it is the closed form
`Dfr(x) = ⌈x/(k(k−1))⌉ − 1` together with the ceiling plateau (`mod_kk1_ne_one`, `ceilDiv_eq_pred`). -/
theorem dfr_plateau (hk : 3 ≤ k) (n : ℕ) (hn2 : 2 ≤ n) (hmod : n % k ≠ 1) :
    j k n + (n - 2) + ((n - 1) ⌈/⌉ k - 1) = j k (n - 1) + (n - 1) + (n ⌈/⌉ k - 1) := by
  by_cases hbc : n ≤ k * (k - 1) * (k - 2)
  · have hbfn := base_frontier hk (by omega : 1 ≤ n) hbc
    have hbfn1 := base_frontier hk (by omega : 1 ≤ n - 1) (by omega)
    have hkk1 : 2 ≤ k * (k - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul (show 3 ≤ k from hk) (show 1 ≤ k - 1 by omega))
    have hcdeq : n ⌈/⌉ (k * (k - 1)) = (n - 1) ⌈/⌉ (k * (k - 1)) :=
      ceilDiv_eq_pred hn2 hkk1 (mod_kk1_ne_one hk hmod)
    omega
  · exact sstep_zero hk n (by omega) hmod

/-! ## §5. The intermediate-violation lever (`m*` argument) -/

/-- **The `m*` lever.**  In the combined induction's tight residual branch — tight prefix `q` at
`n = |p| − ℓ₀` with `n ≢ 1 (mod k)` — the length is closed *unconditionally*: the last demand jump
lands interior, so at `m = |p| − 1` the induction hypothesis (`hIH`) supplies
`j_k(m) ≤ Dfrontier(m) + excess(prefix_m)` while the demand arithmetic (`dfr_shift` + `dfr_plateau`)
gives `Dfr(m) = Dfr(n) + (k − 2) = excess q + (k − 2)`; monotonicity of `excess` finishes. -/
theorem m_star_pays (hk : 3 ≤ k) {p q : HPath k} (hpe : p.Exitless)
    (hbaseR : k * (k - 1) * (k - 2) < p.numVerts)
    (hqnv : q.numVerts = p.numVerts - ell0 k)
    (htight : j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q)
    (hphase : (p.numVerts - ell0 k) % k ≠ 1)
    (hIH : ∀ r : HPath k, r.Exitless → r.numVerts < p.numVerts →
        j k r.numVerts ≤ (r.numVerts - 1) + (r.numVerts ⌈/⌉ k - 1) + excess r) :
    excess q + (k - 2) ≤ excess p := by
  have hk0 : 0 < k := by omega
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hm2 : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm2
  have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
  have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
  set N := p.numVerts with hNdef
  set n := N - ell0 k with hndef
  -- `(N − ℓ₀) % k = N % k`
  have hNmod : (N - ell0 k) % k = N % k := by
    obtain ⟨t, ht⟩ := k_dvd_ell0 hk
    have hNe : N = (N - ell0 k) + k * t := by omega
    calc (N - ell0 k) % k = ((N - ell0 k) + k * t) % k := (Nat.add_mul_mod_self_left ..).symm
      _ = N % k := by rw [← hNe]
  -- `n ≢ 1 (mod k)` with `N > base` forces `N ≥ base + 2` (else `N = base + 1 ≡ 1`)
  have hN2 : k * (k - 1) * (k - 2) + 2 ≤ N := by
    rcases Nat.lt_or_ge N (k * (k - 1) * (k - 2) + 2) with h | h
    · exfalso; apply hphase
      rw [hNmod, show N = 1 + ((k - 1) * (k - 2)) * k from by
            have : k * (k - 1) * (k - 2) = ((k - 1) * (k - 2)) * k := by ring
            omega,
          Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    · exact h
  set m := N - 1 with hmdef
  have hmbase : k * (k - 1) * (k - 2) < m := by omega
  have hmle : m ≤ N := by omega
  -- interior prefix `r` at `m = |p| − 1`
  obtain ⟨r, hrv, hre⟩ := prefix_exitless hpe (show 1 ≤ m by omega) hmle
  have hrnv : r.numVerts = m := by
    have hlen : p.verts.length = N := rfl
    show r.verts.length = m; rw [hrv, List.length_take, hlen]; omega
  have hfront := hIH r hre (by rw [hrnv]; omega)
  rw [hrnv] at hfront
  have hmono := excess_prefix_le hrv hmle hrnv
  -- demand arithmetic
  have hDS := dfr_shift hk m hmbase
  have hmel : m - ell0 k = n - 1 := by omega
  rw [hmel] at hDS
  have hn2 : 2 ≤ n := by omega
  have hSS := dfr_plateau hk n hn2 (by rw [hndef]; exact hphase)
  rw [hqnv] at htight
  omega

/-! ## §6. The residual restricted to the door-phase residue `n ≡ 1 (mod k)` -/

/-- **The Res1 residual.**  `ProofsFinal.JumpLoopEntryFree k` with the extra hypothesis that the
tight-prefix (jump) length `n = |p| − ℓ₀` sits on the door-phase residue `n ≡ 1 (mod k)`.  This is
strictly weaker than `JumpLoopEntryFree k`: the cascade lever below discharges every other residue
(`n ≢ 1 (mod k)`) unconditionally inside the combined induction. -/
def JumpLoopEntryFreeRes1 (k : ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    j k q.numVerts = (q.numVerts - 1) + (q.numVerts ⌈/⌉ k - 1) + excess q →
    j k (p.numVerts - ell0 k) ≠ j k (p.numVerts - ell0 k - k) + (k + 1) →
    (p.numVerts - ell0 k) % k = 1 →
    doorDepth p (winA p) ≠ 0

/-- **The cascade combined induction.**  `JumpLoopEntryFreeRes1 k → ExcessFrontier k`.  Re-runs
`ProofsFinal.excessFrontier_of_jumpLoopEntryFree`'s strong induction verbatim, but in the tight
residual branch first splits on the door-phase residue: `n ≢ 1 (mod k)` is closed by the `m*` lever
(`m_star_pays`) using the induction hypothesis; only `n ≡ 1 (mod k)` still appeals to the residual
(now `JumpLoopEntryFreeRes1`). -/
theorem excessFrontier_of_res1 (hk : 3 ≤ k) (hR : JumpLoopEntryFreeRes1 k) :
    ExcessFrontier k := by
  have main : ∀ ℓ : ℕ, ∀ p : HPath k, p.Exitless → p.numVerts = ℓ →
      j k p.numVerts ≤ (p.numVerts - 1) + (p.numVerts ⌈/⌉ k - 1) + excess p := by
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro p hpe hpℓ
      have h0 : 0 < p.numVerts := p.numVerts_pos
      by_cases hbaseR : p.numVerts ≤ k * (k - 1) * (k - 2)
      · exact excess_frontier_base hk hpe h0 hbaseR
      · rw [Nat.not_le] at hbaseR
        have he0pos : 0 < ell0 k := ell0_pos hk
        have hm : 2 ≤ (k - 1) * (k - 2) := by
          have h := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega)
          omega
        have hprod : k * 2 ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul (le_refl k) hm
        have heq : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
        have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
        have hkle0 : k ≤ ell0 k := by rw [he0val]; omega
        have he0base : ell0 k ≤ k * (k - 1) * (k - 2) := by rw [he0val]; omega
        set n := p.numVerts - ell0 k with hn
        have hn1 : 1 ≤ n := by rw [hn]; omega
        have hnk : k < n := by rw [hn, he0val]; omega
        have hnle : n ≤ p.numVerts := by rw [hn]; omega
        have hnlt : n < p.numVerts := by rw [hn]; omega
        have hNsum : p.numVerts = n + ell0 k := by rw [hn]; omega
        obtain ⟨q, hqv, hqe⟩ := prefix_exitless hpe hn1 hnle
        have hqnv : q.numVerts = n := by
          have hlen : p.verts.length = p.numVerts := rfl
          show q.verts.length = n
          rw [hqv, List.length_take, hlen]; omega
        have hpre : q.verts = p.verts.take (p.numVerts - ell0 k) := by rw [hqv, hn]
        have hnltℓ : n < ℓ := by rw [← hpℓ]; exact hnlt
        have hIH := ih n hnltℓ q hqe hqnv
        rw [hqnv] at hIH
        have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
        have hje0 : j k (ell0 k) = ell0 k + (ell0 k / k) + (k - 2) - 3 := by
          rw [j_base (Or.inl he0base), Proved.ceilDiv_of_dvd (show 0 < k by omega) hdvd,
              ceilDiv_ell0 hk]
        have hsplit : p.numVerts ⌈/⌉ k = n ⌈/⌉ k + ell0 k / k := by
          rw [hNsum]; exact ceilDiv_add_dvd (show 0 < k by omega) hdvd
        have hjrec : j k p.numVerts = j k n + j k (ell0 k) + 3 := by
          have hr := j_rec_unfold_one hk hbaseR
          rw [← hn] at hr; exact hr
        have hXn1 : 1 ≤ n ⌈/⌉ k := by
          rw [Proved.ceilDiv_succ_pred hn1 (show 0 < k by omega)]; exact Nat.le_add_left 1 _
        have hXe1 : 1 ≤ ell0 k / k :=
          (Nat.one_le_div_iff (show 0 < k by omega)).mpr hkle0
        by_cases htight : j k n = (n - 1) + (n ⌈/⌉ k - 1) + excess q
        · -- frontier-tight prefix: split on the door-phase residue `n mod k`
          by_cases hphase : n % k = 1
          · -- `n ≡ 1 (mod k)`: the residual (restricted) supplies `doorDepth ≠ 0`, then pay `k − 2`
            have haval : winA p = (n - 1) / k := by
              show (p.numVerts - ell0 k - 1) / k = (n - 1) / k
              have hnn : p.numVerts - ell0 k - 1 = n - 1 := by omega
              rw [hnn]
            have ha1 : 1 ≤ winA p := by
              rw [haval]; exact (Nat.one_le_div_iff (show 0 < k by omega)).mpr (by omega)
            have hdoor : doorDepth p (winA p) ≠ 0 := by
              intro hdd0
              by_cases hjump : j k n = j k (n - k) + (k + 1)
              · -- non-jump length: closed by the induction hypothesis
                obtain ⟨q', hq'v, hq'e⟩ := prefix_exitless hpe (show 1 ≤ n - k by omega)
                  (show n - k ≤ p.numVerts by omega)
                have hq'nv : q'.numVerts = n - k := by
                  have hlen : p.verts.length = p.numVerts := rfl
                  show q'.verts.length = n - k
                  rw [hq'v, List.length_take, hlen]; omega
                have hIH' := ih (n - k) (by omega) q' hq'e hq'nv
                rw [hq'nv] at hIH'
                have hkaN : k * winA p < p.numVerts := by
                  have : k * winA p ≤ n - 1 := by
                    rw [haval, Nat.mul_comm]; exact Nat.div_mul_le_self (n - 1) k
                  omega
                have hbw3 : 3 ≤ bw p (winA p) :=
                  bw_ge_three_of_doorDepth_zero (by omega) hpe ha1 hkaN hdd0
                have hstep : excess q' + (bw p (winA p) - 2) ≤ excess q :=
                  excess_block_step (by omega) (by omega) hnle ha1 haval hqv hq'v
                have hcstep : n ⌈/⌉ k = (n - k) ⌈/⌉ k + 1 := ceilDiv_step (by omega) (by omega)
                have hXnk1 : 1 ≤ (n - k) ⌈/⌉ k := by
                  rw [Proved.ceilDiv_succ_pred (show 1 ≤ n - k by omega) (show 0 < k by omega)]
                  exact Nat.le_add_left 1 _
                omega
              · -- jump length, `n ≡ 1 (mod k)`: the restricted residual
                exact hR p q hpe hqe hbaseR hpre (by rw [hqnv]; exact htight)
                  (by rw [← hn]; exact hjump) (by rw [← hn]; exact hphase) hdd0
            have hwin : excess q + (k - 2) ≤ excess p :=
              tight_window_pays hk hpe hqe hbaseR hpre hdoor
            omega
          · -- `n ≢ 1 (mod k)`: the `m*` lever closes the length with no residual
            have hlever : excess q + (k - 2) ≤ excess p :=
              m_star_pays hk hpe hbaseR (hqnv.trans hn) (by rw [hqnv]; exact htight)
                (by rw [← hn]; exact hphase)
                (fun r hre hrlt => ih r.numVerts (by rw [← hpℓ]; exact hrlt) r hre rfl)
            omega
        · -- bank ≥ 1: the proved `k − 3` floor suffices
          have hfloor : excess q + (k - 3) ≤ excess p :=
            windowExcess_ge_km3 hk hpe hbaseR hpre
          omega
  intro q hqe h0
  have := main q.numVerts q hqe rfl
  omega

end ProofsCascade

/-! ## §7. The `Hunter.Proved` capstones from the Res1 residual

The cascade lever shrinks the combined-induction residual to `JumpLoopEntryFreeRes1` — the door-phase
residue `n ≡ 1 (mod k)`.  All of Hunter's Theorem 2 / Theorem 1 capstones now follow from this
strictly weaker residual, exactly as `ProofsFinal`'s do from `JumpLoopEntryFree`.

**A note on `JumpLoopEntryFree` vs `JumpLoopEntryFreeRes1`.**  `JumpLoopEntryFreeRes1` is `≤`
`JumpLoopEntryFree` (it carries the extra `n ≡ 1 (mod k)` hypothesis), so `JumpLoopEntryFree →
JumpLoopEntryFreeRes1` holds trivially (`res1_of_jumpLoopEntryFree`).  The reverse (`Res1 → full
JumpLoopEntryFree`) is *not* available and is *not needed*: `JumpLoopEntryFree`'s conclusion
`doorDepth (winA p) = 0 → False` genuinely over-claims at `n ≢ 1 (mod k)` — the `m*` lever closes
those *lengths* (the frontier holds) without excluding `doorDepth = 0` configurations.  The correct,
strictly-weaker route is `Res1 → ExcessFrontier` (`ProofsCascade.excessFrontier_of_res1`), from which
`FrontierTightHeavy` and every capstone follow. -/

namespace Proved

open ProofsRecursion ProofsSynthesis ProofsFinal ProofsCascade

/-- **`JumpLoopEntryFreeRes1` is the weaker residual.**  It follows trivially from the full
`ProofsFinal.JumpLoopEntryFree` (drop the extra `n ≡ 1 (mod k)` hypothesis). -/
theorem res1_of_jumpLoopEntryFree {k : ℕ} (h : JumpLoopEntryFree k) :
    JumpLoopEntryFreeRes1 k :=
  fun p q hpe hqe hlt hpre htight hjump _ => h p q hpe hqe hlt hpre htight hjump

/-- **`ExcessFrontier` from the Res1 residual** (the cascade closure). -/
theorem excessFrontier_of_res1 {k : ℕ} (hk : 3 ≤ k) (hR : JumpLoopEntryFreeRes1 k) :
    ExcessFrontier k :=
  ProofsCascade.excessFrontier_of_res1 hk hR

/-- **`FrontierTightHeavy` from the Res1 residual.** -/
theorem frontierTightHeavy_of_res1 {k : ℕ} (hk : 3 ≤ k) (hR : JumpLoopEntryFreeRes1 k) :
    FrontierTightHeavy k :=
  frontierTightHeavy_of_excessFrontier hk (ProofsCascade.excessFrontier_of_res1 hk hR)

/-- **Theorem 2 from the Res1 residual** (verbatim `Statements.thm2` conclusion). -/
theorem thm2_of_res1 {k ℓ : ℕ} (hk : 3 ≤ k) (hR : JumpLoopEntryFreeRes1 k)
    (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  thm2_of_frontier hk (ProofsCascade.excessFrontier_of_res1 hk hR) hℓ

/-- **The global Res1 residual.** -/
def JumpLoopEntryFreeRes1All : Prop := ∀ k, 3 ≤ k → JumpLoopEntryFreeRes1 k

/-- **Theorem 2, globally, from the Res1 residual.** -/
theorem thm2_global_of_res1 (hR : JumpLoopEntryFreeRes1All) :
    ∀ k ℓ, 3 ≤ k → HasExitlessPath k ℓ → j k ℓ ≤ iExitless k ℓ :=
  fun k _ℓ hk hℓ => thm2_of_res1 hk (hR k hk) hℓ

/-- `JumpLoopEntryFreeRes1All → FrontierTightHeavyAll` (= `(MF)` global). -/
theorem frontierTightHeavyAll_of_res1All (hR : JumpLoopEntryFreeRes1All) :
    FrontierTightHeavyAll :=
  fun k hk => frontierTightHeavy_of_excessFrontier hk
    (ProofsCascade.excessFrontier_of_res1 hk (hR k hk))

/-- **thm1v1 from the Res1 residual** (superpermutation form). -/
theorem thm1v1_of_res1 (hR : JumpLoopEntryFreeRes1All)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (Lstar k : ℝ) ≥ coeff k * (k.factorial : ℝ) + (k : ℝ) - C :=
  ProofsMF.thm1v1_of_MF (frontierTightHeavyAll_of_res1All hR) hproof hexists

/-- **thm1v2 from the Res1 residual** (`L(k) ≥ coeff(k)·k! − O(1)`). -/
theorem thm1v2_of_res1 (hR : JumpLoopEntryFreeRes1All)
    (hproof : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2)) →
        (L k : ℝ) ≥ (iExitless k (k * (k - 1) * (k - 2)) : ℝ)
          + (((iExitless k (k * (k - 1) * (k - 2)) : ℝ) - (k : ℝ) + 2) /
              (((k * (k - 1) * (k - 2) : ℕ) : ℝ) - (k : ℝ)))
            * ((k.factorial : ℝ) - ((k * (k - 1) * (k - 2) : ℕ) : ℝ)))
    (hexists : ∀ k, 3 ≤ k → HasExitlessPath k (k * (k - 1) * (k - 2))) :
    ∃ (C : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → (L k : ℝ) ≥ coeff k * (k.factorial : ℝ) - C :=
  ProofsMF.thm1v2_of_MF (frontierTightHeavyAll_of_res1All hR) hproof hexists

end Proved

end Hunter

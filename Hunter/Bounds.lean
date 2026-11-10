/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Transform

/-!
# The optimisation quantities (Hunter §2.6, §6)

* `L k` — the minimum weight `L(k)` over Hamiltonian paths.
* `Lstar k := L k + k` — Hunter's `L*(k)`, the minimum superpermutation length.  We also
  port the direct superpermutation minimum `Ssuper k`; the bridge `Lstar k = Ssuper k`
  (`L*(k) = k + L(k)`) is proved as `Hunter.Proved.bridge_Lstar_eq_Ssuper`.
* `iExitless k ℓ` — Hunter's `i_k(ℓ)`, minimum weight of an exitless path on `ℓ` vertices.
* `ell0 k` (`= ℓ₀`), `j k ℓ` (`= j_k(ℓ)`, well-founded recursion), and `Rk k` (`= R_k`),
  `pValue`.

Empty/degenerate conventions (via `Nat.sInf ∅ = 0`, `sInf (ℚ) = 0`, and the `ℓ₀ = 0`
guard in `j`) are documented in `AMBIGUITIES.md`.
-/

namespace Hunter

open List
open scoped Classical

variable {k : ℕ}

/-! ## `L(k)`, `L*(k)`, and the superpermutation minimum -/

/-- Hunter §2.6: `L(k) = min_P w(P)`, the minimum weight over Hamiltonian paths of `𝒮_k`.
`Nat.sInf ∅ = 0` if none exist (they always do for `k ≥ 1`). -/
noncomputable def L (k : ℕ) : ℕ :=
  sInf {m | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}

/-- Hunter §2.6: `L*(k) = k + L(k)`, the minimum length of a `k`-superpermutation. -/
noncomputable def Lstar (k : ℕ) : ℕ := L k + k

/-- Hunter §1 (Coeff2 `IsSuperperm`): `w` is a `k`-superpermutation if it contains every
permutation of `[k]` as a factor. -/
def IsSuperperm (k : ℕ) (w : List ℕ) : Prop :=
  ∀ v, IsPermWord k v → v <:+: w

/-- Hunter §1/§2.6 (Coeff2 `S`): the minimum length of a `k`-superpermutation.  The bridge
`Lstar k = Ssuper k` is Hunter's `L*(k) = k + L(k)`, proved as
`Hunter.Proved.bridge_Lstar_eq_Ssuper`. -/
noncomputable def Ssuper (k : ℕ) : ℕ :=
  sInf {m | ∃ w : List ℕ, IsSuperperm k w ∧ w.length = m}

/-! ## `i_k(ℓ)` -/

/-- Hunter §2.6: `i_k(ℓ)` = minimum weight of an *exitless* path on `𝒮_k` with `ℓ`
vertices.  Empty case (`ℓ` for which no exitless path exists) is `0` via `Nat.sInf ∅ = 0`
— this **differs from the paper's `min* ∅ = +∞`**; see `AMBIGUITIES.md`. -/
noncomputable def iExitless (k ℓ : ℕ) : ℕ :=
  sInf {m | ∃ p : HPath k, p.Exitless ∧ p.numVerts = ℓ ∧ p.wtP = m}

/-! ## `ℓ₀` and `j_k(ℓ)` -/

/-- Hunter §2.9: the recursion pivot `ℓ₀ = k(k−1)(k−2) − k`. -/
def ell0 (k : ℕ) : ℕ := k * (k - 1) * (k - 2) - k

/-- Hunter §2.9: `j_k(ℓ)`, the "optimistically greedy" upper bound for `i_k`.

`j_k(ℓ) = ℓ + ⌈ℓ/k⌉ + ⌈ℓ/(k(k−1))⌉ − 3`      for `0 < ℓ ≤ k(k−1)(k−2)`,
`j_k(ℓ) = j_k(ℓ − ℓ₀) + j_k(ℓ₀) + 3`         for `ℓ > k(k−1)(k−2)`.

Well-founded on `ℓ` (each recursive argument is smaller since `ℓ₀ ≥ 1`).  When `ℓ₀ = 0`
(which happens for `k ≤ 2`, where `k(k−1)(k−2) = 0`) the base formula is used for all `ℓ`,
keeping the recursion terminating; the ℕ subtractions use the truncated convention.  See
`AMBIGUITIES.md`. -/
noncomputable def j (k ℓ : ℕ) : ℕ :=
  if h : ℓ ≤ k * (k - 1) * (k - 2) ∨ k * (k - 1) * (k - 2) - k = 0 then
    ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3
  else
    j k (ℓ - (k * (k - 1) * (k - 2) - k)) + j k (k * (k - 1) * (k - 2) - k) + 3
termination_by ℓ
decreasing_by
  · simp only [not_or] at h; omega
  · simp only [not_or] at h; omega

/-! ## `R_k` and `p_value` -/

/-- Hunter §2.9: `p_value(p) = 1 + minto(p) + w(p)`. -/
noncomputable def pValue (p : HPath k) : ℕ := 1 + p.minto + p.wtP

/-- Hunter §2.9: `R_k = min_{p ∈ 𝒳'_k, |p| ≤ k!−k} p_value(p)/|p|`, the minimal cost per
vertex over non-spanning path-components.  Taken as a **real** infimum (ℚ has no `InfSet`
instance; the value is the same rational), with the `sInf ∅ = 0` convention; see
`AMBIGUITIES.md`. -/
noncomputable def Rk (k : ℕ) : ℝ :=
  sInf {q : ℝ | ∃ p, p ∈ Xk' k ∧ p.numVerts ≤ k.factorial - k ∧
    q = (pValue p : ℝ) / (p.numVerts : ℝ)}

/-! ## Small free lemmas -/

theorem lstar_eq (k : ℕ) : Lstar k = L k + k := rfl

theorem ell0_eq (k : ℕ) : ell0 k = k * (k - 1) * (k - 2) - k := rfl

/-- The base branch of `j` (unfolding lemma). -/
theorem j_base {k ℓ : ℕ} (h : ℓ ≤ k * (k - 1) * (k - 2) ∨ k * (k - 1) * (k - 2) - k = 0) :
    j k ℓ = ℓ + (ℓ ⌈/⌉ k) + (ℓ ⌈/⌉ (k * (k - 1))) - 3 := by
  rw [j]; exact dif_pos h

/-- The recursive branch of `j` (unfolding lemma). -/
theorem j_rec {k ℓ : ℕ}
    (h : ¬ (ℓ ≤ k * (k - 1) * (k - 2) ∨ k * (k - 1) * (k - 2) - k = 0)) :
    j k ℓ = j k (ℓ - ell0 k) + j k (ell0 k) + 3 := by
  rw [j]; rw [dif_neg h]; rfl

end Hunter

/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsGB2
import Hunter.ProofsReductions
import Hunter.ProofsGreedy2

/-!
# Proofs — the `p_u`-extension and the remaining reduction leaves (`red_R`, `subprob1_comp`)

This file closes two reduction-side leaves:

* **`hkey` of `red_R`** — the paper's `p_u`-extension.  For each non-spanning
  strongly-exitless path-component `p ∈ 𝒳'_k` we prepend the full `σ`-orbit of the cheapest
  entry vertex `u` (`u ∉ p`, `w(u→p[1]) = minto(p)`), producing an **exitless** path `p_u` of
  length `|p|+k` with `w(p_u) = (k−1) + minto(p) + w(p)`.  This gives
  `i_k(|p|+k) ≤ p_value(p) + k − 2`, i.e. the per-path ratio bound.
* **`subprob1_comp`** (the AMENDED statement, corrected ceiling-remainder) — pure real
  arithmetic on the `j`-recursion.

Helpers live in `namespace Hunter.ProofsPu`; the delivered targets in `namespace
Hunter.Proved`.  Zero `sorry`, zero new axioms.  See `PROGRESS-pu.md`.
-/

namespace Hunter.ProofsPu

open List
open scoped Classical
open Hunter
open Hunter.HPath

/-! ## Ceiling-division nat identities -/

/-- **Ceiling-remainder identity**: `d · ⌈n/d⌉ = n + ((d − n mod d) mod d)` for `d > 0`.
The additive correction `(d − n mod d) mod d` is the exact ceiling remainder. -/
theorem cd_mul (n d : ℕ) (hd : 0 < d) : d * (n ⌈/⌉ d) = n + (d - n % d) % d := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < d ∧ n = d * q + r :=
    ⟨n / d, n % d, Nat.mod_lt n hd, (Nat.div_add_mod n d).symm⟩
  have hmod : (d * q + r) % d = r := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  rw [hmod]
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    rw [Nat.add_zero, Nat.sub_zero, Nat.mod_self, Nat.add_zero,
      ProofsReductions.cd_exact d q hd]
  · have hsub : (d - r) % d = d - r := Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    have hcd : (d * q + r) ⌈/⌉ d = q + 1 := by
      rw [Nat.ceilDiv_eq_add_pred_div,
        show d * q + r + d - 1 = d * (q + 1) + (r - 1) from by
          rw [Nat.mul_add, Nat.mul_one]; omega,
        Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega : r - 1 < d), Nat.add_zero]
    rw [hcd, Nat.mul_add, Nat.mul_one]; omega

/-- Ceiling of a "middle" quotient: `(D·Q + s) ⌈/⌉ D = Q + 1` when `0 < s < D`. -/
theorem cd_mid (D Q s : ℕ) (hD : 0 < D) (hs0 : 0 < s) (hs : s < D) :
    (D * Q + s) ⌈/⌉ D = Q + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div,
    show D * Q + s + D - 1 = D * (Q + 1) + (s - 1) from by rw [Nat.mul_add, Nat.mul_one]; omega,
    Nat.mul_add_div hD, Nat.div_eq_of_lt (by omega : s - 1 < D), Nat.add_zero]

/-! ## `ell0` ceiling values -/

/-- `ell0 k = k · ((k−1)(k−2) − 1)`. -/
theorem ell0_factor {k : ℕ} (hk : 3 ≤ k) : ell0 k = k * ((k - 1) * (k - 2) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [ell0, show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
  have ha : (m + 2) * (m + 1) = m * m + 3 * m + 2 := by ring
  rw [ha, show m * m + 3 * m + 2 - 1 = m * m + 3 * m + 1 from by omega]
  have hb : (m + 3) * (m + 2) * (m + 1) = (m + 3) * (m * m + 3 * m + 1) + (m + 3) := by ring
  rw [hb]; omega

/-- `⌈ell0 k / k⌉ = (k−1)(k−2) − 1`. -/
theorem cd_ell0_k {k : ℕ} (hk : 3 ≤ k) : (ell0 k) ⌈/⌉ k = (k - 1) * (k - 2) - 1 := by
  rw [ell0_factor hk]; exact ProofsReductions.cd_exact k _ (by omega)

/-- `⌈ell0 k / (k(k−1))⌉ = k − 2`. -/
theorem cd_ell0_kk {k : ℕ} (hk : 3 ≤ k) : (ell0 k) ⌈/⌉ (k * (k - 1)) = k - 2 := by
  have hrepr : ell0 k = (k * (k - 1)) * (k - 3) + k * (k - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    simp only [ell0, show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega,
      show m + 3 - 3 = m from by omega]
    have e : (m + 3) * (m + 2) * (m + 1)
        = (m + 3) * (m + 2) * m + (m + 3) * (m + 1) + (m + 3) := by ring
    omega
  rw [hrepr]
  have h := cd_mid (k * (k - 1)) (k - 3) (k * (k - 2))
    (Nat.mul_pos (by omega) (by omega)) (Nat.mul_pos (by omega) (by omega))
    (mul_lt_mul_of_pos_left (by omega : k - 2 < k - 1) (by omega : 0 < k))
  rw [h]; omega

/-- The real value of `j_k(ℓ₀)` (base branch, `ℓ₀ = k(k−1)(k−2) − k`). -/
theorem jell0_real {k : ℕ} (hk : 3 ≤ k) :
    (j k (ell0 k) : ℝ)
      = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ)
        + (((k : ℝ) - 1) * ((k : ℝ) - 2) - 1) + ((k : ℝ) - 2) - 3 := by
  have hbase : j k (ell0 k) = ell0 k + (ell0 k) ⌈/⌉ k + (ell0 k) ⌈/⌉ (k * (k - 1)) - 3 :=
    j_base (Or.inl (by rw [ell0_eq]; exact Nat.sub_le _ _))
  rw [cd_ell0_k hk, cd_ell0_kk hk] at hbase
  have hb1 : 1 ≤ (k - 1) * (k - 2) := Nat.mul_pos (by omega) (by omega)
  have hb1' : 2 ≤ (k - 1) * (k - 2) := by
    have := Nat.mul_le_mul (show 2 ≤ k - 1 by omega) (show 1 ≤ k - 2 by omega); omega
  have hb2 : k ≤ k * (k - 1) * (k - 2) :=
    le_trans (Nat.le_mul_of_pos_right k (by omega))
      (Nat.le_mul_of_pos_right _ (by omega))
  have hp : 2 * k ≤ k * (k - 1) * (k - 2) := by
    calc 2 * k = k * 2 := by ring
      _ ≤ k * ((k - 1) * (k - 2)) := Nat.mul_le_mul_left k hb1'
      _ = k * (k - 1) * (k - 2) := by rw [mul_assoc]
  have hell0_ge : 3 ≤ ell0 k := by rw [ell0_eq]; omega
  have hb3 : 3 ≤ ell0 k + ((k - 1) * (k - 2) - 1) + (k - 2) := le_trans hell0_ge (by omega)
  rw [hbase, Nat.cast_sub hb3]
  push_cast [ell0_eq, Nat.cast_sub hb2, Nat.cast_sub hb1,
    Nat.cast_sub (show 1 ≤ k from by omega), Nat.cast_sub (show 2 ≤ k from by omega)]
  ring

/-- Casting a ceiling to a fraction with the exact remainder: `(⌈n/d⌉ : ℝ) = (n + ρ)/d` where
`ρ = (d − n mod d) mod d`. -/
theorem cd_frac (n d : ℕ) (hd : 0 < d) :
    ((n ⌈/⌉ d : ℕ) : ℝ) = ((n : ℝ) + (((d - n % d) % d : ℕ) : ℝ)) / (d : ℝ) := by
  have hdne : (d : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hdne]
  have h := cd_mul n d hd
  have hr : ((d * (n ⌈/⌉ d) : ℕ) : ℝ) = ((n + (d - n % d) % d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  rw [mul_comm]; linarith [hr]

/-! ## The `p_u`-extension: the `σ`-orbit list and the prepended path -/

variable {k : ℕ}

/-- The `σ`-orbit list of `w`: `[w, σw, …, σ^{k−1}w]`, length `k`. -/
noncomputable def orbitList (w : Vtx k) : List (Vtx k) :=
  (List.range k).map (fun i => sigma^[i] w)

theorem orbitList_length (w : Vtx k) : (orbitList w).length = k := by
  simp [orbitList]

theorem orbitList_getElem (w : Vtx k) {i : ℕ} (hi : i < (orbitList w).length) :
    (orbitList w)[i] = sigma^[i] w := by
  simp only [orbitList, List.getElem_map, List.getElem_range]

theorem orbitList_nodup (_hk : 1 ≤ k) (w : Vtx k) : (orbitList w).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj hij
  rw [List.mem_range] at hi hj
  exact ProofsExitless.sigma_iter_inj w hi hj hij

theorem mem_orbitList {w x : Vtx k} (hx : x ∈ orbitList w) : ∃ i < k, x = sigma^[i] w := by
  simp only [orbitList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx; exact ⟨i, hi, rfl⟩

/-- **The `p_u`-extension, with its exact vertex list.**  Given a strongly-exitless path `p`
and a vertex `u ∉ p` realizing `minto(p)` (i.e. `w(u→p[1]) = minto(p)`), prepending the
`σ`-orbit `[σu, …, σ^{k−1}u, u]` of `u` yields an **exitless** path of length
`|p|+k` and weight `(k−1) + minto(p) + w(p)`. -/
theorem pu_exists_with_verts (hk : 2 ≤ k) {p : HPath k} (hSE : p.StronglyExitless)
    {u : Vtx k} (hu : u ∉ p.verts) (hmin : ew k u p.first = minto p) :
    ∃ q : HPath k, q.verts = orbitList (sigma u) ++ p.verts ∧
      q.Exitless ∧ q.numVerts = p.numVerts + k ∧
      q.wtP = (k - 1) + minto p + p.wtP := by
  have hk1 : 1 ≤ k := by omega
  set N := p.numVerts with hNdef
  have hpe : p.Exitless := hSE.1
  have huoc : p.IsUnionOfCycles := Proved.clm_1cyclesubset hSE
  -- every orbit vertex has `rotClass u`
  have hrc : ∀ i, rotClass ((sigma^[i] (sigma u)).1) = rotClass u.1 := fun i => by
    rw [ProofsExitless.rotClass_sigma_iter i (sigma u), ProofsStructure.rotClass_sigma u]
  -- a vertex of `p` never lies in the orbit (its `σ`-cycle would drag `u` into `p`)
  have hpin : ∀ x : Vtx k, x ∈ p.verts → x ∉ orbitList (sigma u) := by
    intro x hx hxo
    obtain ⟨i, -, rfl⟩ := mem_orbitList hxo
    have hcyc : u ∈ cyc (sigma^[i] (sigma u)) := ProofsExitless.mem_cyc.mpr (hrc i).symm
    exact hu (HPath.mem_vertsFinset.mp (huoc _ hx hcyc))
  -- build the path `q`
  have hnodup : (orbitList (sigma u) ++ p.verts).Nodup := by
    rw [List.nodup_append]
    refine ⟨orbitList_nodup hk1 (sigma u), p.nodup, ?_⟩
    intro a ha b hb heq
    exact hpin b hb (heq ▸ ha)
  have hne : orbitList (sigma u) ++ p.verts ≠ [] := by
    simp only [ne_eq, List.append_eq_nil_iff, not_and]; intro _; exact p.ne
  set q : HPath k := ⟨orbitList (sigma u) ++ p.verts, hne, hnodup⟩ with hqdef
  have hqverts : q.verts = orbitList (sigma u) ++ p.verts := rfl
  have hpvl : p.verts.length = N := rfl
  have hqnv : q.numVerts = p.numVerts + k := by
    show (orbitList (sigma u) ++ p.verts).length = p.numVerts + k
    rw [List.length_append, orbitList_length, hpvl]; omega
  -- vertex access
  have hvo : ∀ i, i < k → q.vert i = sigma^[i] (sigma u) := by
    intro i hi
    have hi' : i < (orbitList (sigma u)).length := by rw [orbitList_length]; exact hi
    have hval : q.vert i = (orbitList (sigma u) ++ p.verts)[i]'(by
        rw [List.length_append]; omega) := by
      rw [ProofsExitless.vert_getElem q (by rw [hqnv]; omega)]; rfl
    rw [hval, List.getElem_append_left hi', orbitList_getElem (sigma u) hi']
  have hvp : ∀ t, t < N → q.vert (k + t) = p.vert t := by
    intro t ht
    have hlen : (orbitList (sigma u)).length ≤ k + t := by rw [orbitList_length]; omega
    have hval : q.vert (k + t) = (orbitList (sigma u) ++ p.verts)[k + t]'(by
        rw [List.length_append, orbitList_length, hpvl]; omega) := by
      rw [ProofsExitless.vert_getElem q (by rw [hqnv]; omega)]; rfl
    rw [hval, List.getElem_append_right hlen,
      ProofsExitless.vert_getElem p (show t < p.numVerts from ht)]
    congr 1
    rw [orbitList_length]; omega
  -- position of a `p`-vertex inside `q` is shifted by `k`
  have hpos : ∀ v : Vtx k, v ∈ p.verts → q.pos v = k + p.pos v := by
    intro v hv
    show (orbitList (sigma u) ++ p.verts).idxOf v = k + p.verts.idxOf v
    rw [List.idxOf_append_of_notMem (hpin v hv), orbitList_length]
  -- `σ^{k-1}(σu) = u`
  have hlast : sigma^[k - 1] (sigma u) = u := by
    have h1 : sigma u = sigma^[1] u := by rw [Function.iterate_one]
    rw [h1, ← Function.iterate_add_apply sigma (k - 1) 1 u, show k - 1 + 1 = k from by omega,
      ProofsExitless.sigma_iter_period u]
  -- the junction weight is `minto p`; the orbit steps are weight 1
  refine ⟨q, hqverts, ?_, hqnv, ?_⟩
  · -- Exitless
    rw [HPath.Exitless]
    rintro ⟨i, hi1, hw, hlt⟩
    rw [hqnv] at hi1
    rcases lt_trichotomy (i + 1) k with hc1 | hc2 | hc3
    · -- both endpoints in the orbit: weight-1 σ-step
      have hik : i < k := by omega
      have hik1 : i + 1 < k := hc1
      rw [hvo i hik, hvo (i + 1) hik1,
        show sigma^[i + 1] (sigma u) = sigma (sigma^[i] (sigma u)) from
          (Function.iterate_succ_apply' sigma i (sigma u)),
        ew_sigma hk1] at hw
      omega
    · -- junction `i = k-1`: `σ(q[k-1]) = σu = q[0]`, position 0
      have hik : i < k := by omega
      have hiv : q.vert i = u := by
        rw [hvo i hik, show i = k - 1 from by omega, hlast]
      have hs : sigma (q.vert i) = q.vert 0 := by
        rw [hiv, hvo 0 hk1]; simp [Function.iterate_zero]
      rw [hs, ProofsExitless.pos_vert q (by rw [hqnv]; omega)] at hlt
      omega
    · -- inside `p`: shift by `k`, use `p`'s exitless rule
      obtain ⟨t, rfl⟩ : ∃ t, i = k + t := ⟨i - k, by omega⟩
      have htN : t + 1 < N := by omega
      have htN' : t < N := by omega
      rw [hvp t htN', show k + t + 1 = k + (t + 1) from by ring, hvp (t + 1) htN] at hw
      -- σ(p[t]) ∈ p.verts
      have hpvt : p.vert t ∈ p.verts := ProofsExitless.vert_mem p htN'
      have hsv : sigma (p.vert t) ∈ p.verts := by
        have hcyc : sigma (p.vert t) ∈ cyc (p.vert t) :=
          ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma (p.vert t))
        exact HPath.mem_vertsFinset.mp (huoc _ hpvt hcyc)
      rcases ProofsExitless.exitless_step hk1 hpe htN with heq | hle
      · rw [heq, ew_sigma hk1] at hw; omega
      · have hqs : sigma (q.vert (k + t)) = sigma (p.vert t) := by rw [hvp t htN']
        rw [hqs, hpos _ hsv] at hlt
        omega
  · -- weight
    rw [Proved.wtP_eq_sum q, hqnv]
    -- split `range (p.numVerts + k - 1)` at `k`
    have hsplit : Finset.range (p.numVerts + k - 1)
        = Finset.range k ∪ Finset.Ico k (p.numVerts + k - 1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le k) (by have := p.numVerts_pos; omega)]
    have hdisj : Disjoint (Finset.range k) (Finset.Ico k (p.numVerts + k - 1)) := by
      rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 k _
    rw [hsplit, Finset.sum_union hdisj]
    -- Part 1: orbit + junction = (k-1) + minto p
    have hpart1 : ∑ i ∈ Finset.range k, ew k (q.vert i) (q.vert (i + 1))
        = (k - 1) + minto p := by
      have hrange : ∑ i ∈ Finset.range k, ew k (q.vert i) (q.vert (i + 1))
          = ∑ i ∈ Finset.range ((k - 1) + 1), ew k (q.vert i) (q.vert (i + 1)) := by
        rw [show (k - 1) + 1 = k from by omega]
      rw [hrange, Finset.sum_range_succ]
      have horbstep : ∀ i ∈ Finset.range (k - 1), ew k (q.vert i) (q.vert (i + 1)) = 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hik : i < k := by omega
        have hik1 : i + 1 < k := by omega
        rw [hvo i hik, hvo (i + 1) hik1,
          show sigma^[i + 1] (sigma u) = sigma (sigma^[i] (sigma u)) from
            (Function.iterate_succ_apply' sigma i (sigma u)), ew_sigma hk1]
      rw [Finset.sum_congr rfl horbstep, Finset.sum_const, Finset.card_range, smul_eq_mul,
        mul_one]
      -- junction term
      have hjunc : ew k (q.vert (k - 1)) (q.vert (k - 1 + 1)) = minto p := by
        have h1 : q.vert (k - 1) = u := by rw [hvo (k - 1) (by omega), hlast]
        have h2 : q.vert (k - 1 + 1) = p.first := by
          rw [show k - 1 + 1 = k + 0 from by omega, hvp 0 p.numVerts_pos, HPath.vert_zero]
        rw [h1, h2, hmin]
      rw [hjunc]
    -- Part 2: inside `p` = wtP p
    have hpart2 : ∑ i ∈ Finset.Ico k (p.numVerts + k - 1), ew k (q.vert i) (q.vert (i + 1))
        = p.wtP := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show p.numVerts + k - 1 - k = p.numVerts - 1 from by omega]
      rw [Proved.wtP_eq_sum p]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      have htN' : t < N := by omega
      have htN : t + 1 < N := by omega  -- from t < p.numVerts - 1
      rw [hvp t htN', show k + t + 1 = k + (t + 1) from by ring, hvp (t + 1) htN]
    rw [hpart1, hpart2]

/-- Compatibility interface for callers that only need the size and weight of the
`p_u`-extension. -/
theorem pu_exists (hk : 2 ≤ k) {p : HPath k} (hSE : p.StronglyExitless)
    {u : Vtx k} (hu : u ∉ p.verts) (hmin : ew k u p.first = minto p) :
    ∃ q : HPath k, q.Exitless ∧ q.numVerts = p.numVerts + k ∧
      q.wtP = (k - 1) + minto p + p.wtP := by
  obtain ⟨q, _hqverts, hqExitless, hqNumVerts, hqWeight⟩ :=
    pu_exists_with_verts hk hSE hu hmin
  exact ⟨q, hqExitless, hqNumVerts, hqWeight⟩

end Hunter.ProofsPu

namespace Hunter.Proved

open Hunter
open Hunter.ProofsPu

variable {k : ℕ}

/-- **The `p_u`-extension per-path ratio bound** (the `hkey` of `red_R`).  For every
non-spanning strongly-exitless component `p ∈ 𝒳'_k`, the `i_k`-ratio at `ℓ = |p|+k` is
dominated by `p`'s cost ratio `p_value(p)/|p|`.  The witness is `pu_exists`. -/
theorem pu_key (hk : 2 ≤ k) {p : HPath k} (hp : p ∈ Xk' k)
    (hle : p.numVerts ≤ k.factorial - k) :
    k < p.numVerts + k ∧ HasExitlessPath k (p.numVerts + k) ∧
      ((iExitless k (p.numVerts + k) : ℝ) - (k : ℝ) + 2) /
          (((p.numVerts + k : ℕ) : ℝ) - (k : ℝ))
        ≤ (pValue p : ℝ) / (p.numVerts : ℝ) := by
  have hSE : p.StronglyExitless := ProofsB2.Xkcomps_subset hk hp
  -- there is a vertex outside `p` (since `|p| < k!`)
  have hlt : p.numVerts < Fintype.card (Vtx k) := by
    rw [ProofsRecursion.card_Vtx]
    have h1 := Nat.factorial_pos k
    have h2 := p.numVerts_pos
    omega
  have hex : ∃ v : Vtx k, v ∉ p.verts := by
    by_contra h; push Not at h
    have hham : p.IsHamiltonian := h
    rw [HPath.numVerts_eq_card_of_hamiltonian hham] at hlt
    omega
  -- realize `minto p`
  have hne0 : {d | ∃ v : Vtx k, v ∉ p.verts ∧ ew k v p.first = d}.Nonempty := by
    obtain ⟨v, hv⟩ := hex; exact ⟨ew k v p.first, v, hv, rfl⟩
  obtain ⟨u, hu, hew⟩ : ∃ u : Vtx k, u ∉ p.verts ∧ ew k u p.first = p.minto :=
    Nat.sInf_mem hne0
  obtain ⟨q, hqe, hqnv, hqw⟩ := pu_exists hk hSE hu hew
  have hnat : iExitless k (p.numVerts + k) + 2 ≤ pValue p + k := by
    have hile : iExitless k (p.numVerts + k) ≤ q.wtP := Nat.sInf_le ⟨q, hqe, hqnv, rfl⟩
    rw [hqw] at hile
    simp only [pValue]
    omega
  have hnvpos : (0 : ℝ) < (p.numVerts : ℝ) := by exact_mod_cast p.numVerts_pos
  refine ⟨by have := p.numVerts_pos; omega, ⟨q, hqe, hqnv⟩, ?_⟩
  have hden : ((p.numVerts + k : ℕ) : ℝ) - (k : ℝ) = (p.numVerts : ℝ) := by push_cast; ring
  have hnum : (iExitless k (p.numVerts + k) : ℝ) - (k : ℝ) + 2 ≤ (pValue p : ℝ) := by
    have : (iExitless k (p.numVerts + k) : ℝ) + 2 ≤ (pValue p : ℝ) + (k : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hden, div_le_div_iff_of_pos_right hnvpos]
  exact hnum

/-- **red-R (fully assembled)** — the take23 `≥` form with the `p_u`-extension (`hkey`) and the
`BddBelow` junk-guard **both discharged**.  The `p_u`-extension is supplied by `pu_key`; the
lower-boundedness is discharged inside `red_R_tightened`.  The **only** remaining hypothesis is
`hne` (a non-spanning strongly-exitless component exists in `𝒳'_k`) — this routes through the
paper's "unwinding" `P(p₁,…,pₙ)` (`prp_Xk_se_sufficiency`), the sole open combinatorial leaf,
and is not dischargeable here. -/
theorem red_R_final (hk : 2 ≤ k)
    (hne : ∃ p, p ∈ Xk' k ∧ p.numVerts ≤ k.factorial - k) :
    Rk k ≥ sInf {q : ℝ | ∃ ℓ, k < ℓ ∧ HasExitlessPath k ℓ ∧
      q = ((iExitless k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))} :=
  red_R_tightened hk (fun _p hp hle => pu_key hk hp hle) hne

/-- **subprob1-comp (AMENDED)** — the explicit decomposition of the subproblem-1 ratio, with
the corrected ceiling-remainder terms `((d − ℓ' mod d) mod d)/d`.  Pure real arithmetic on the
`j`-recursion unfolding `hjrec` and the base formula. -/
theorem subprob1_comp {k : ℕ} (hk : 3 ≤ k) {t ℓ : ℕ}
    (hle : t * ell0 k ≤ ℓ) (hklt : k < ℓ)
    (hℓ'1 : k < ℓ - t * ell0 k) (hℓ'2 : ℓ - t * ell0 k ≤ k * (k - 1) * (k - 2))
    (hjrec : j k ℓ = t * (j k (ell0 k) + 3) + j k (ℓ - t * ell0 k)) :
    ((j k ℓ : ℝ) - (k : ℝ) + 2) / ((ℓ : ℝ) - (k : ℝ))
      = (1 + 1 / (k : ℝ) + 1 / ((k : ℝ) * ((k : ℝ) - 1)))
        + ((t : ℝ) + 1) / (((k : ℝ) - 1) * ((ℓ : ℝ) - (k : ℝ)))
        + ((((k - (ℓ - t * ell0 k) % k) % k : ℕ) : ℝ) / (k : ℝ)
            + (((k * (k - 1) - (ℓ - t * ell0 k) % (k * (k - 1))) % (k * (k - 1)) : ℕ) : ℝ)
                / ((k : ℝ) * ((k : ℝ) - 1)))
          / ((ℓ : ℝ) - (k : ℝ)) := by
  set A := ℓ - t * ell0 k with hAdef
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := by positivity
  have hk1ne : (k : ℝ) - 1 ≠ 0 := by nlinarith
  have hℓkpos : (0 : ℝ) < (ℓ : ℝ) - (k : ℝ) := by
    have : (k : ℝ) < (ℓ : ℝ) := by exact_mod_cast hklt
    linarith
  have hℓkne : (ℓ : ℝ) - (k : ℝ) ≠ 0 := ne_of_gt hℓkpos
  have hkkne : (k : ℝ) * ((k : ℝ) - 1) ≠ 0 := mul_ne_zero hkne hk1ne
  -- base formula for `j k A`, cast to ℝ with ceilings → fractions
  have hjA_nat : j k A = A + A ⌈/⌉ k + A ⌈/⌉ (k * (k - 1)) - 3 := j_base (Or.inl hℓ'2)
  have h3A : 3 ≤ A + A ⌈/⌉ k + A ⌈/⌉ (k * (k - 1)) := by omega
  have hjAR : (j k A : ℝ)
      = (A : ℝ) + ((A ⌈/⌉ k : ℕ) : ℝ) + ((A ⌈/⌉ (k * (k - 1)) : ℕ) : ℝ) - 3 := by
    rw [hjA_nat, Nat.cast_sub h3A]; push_cast; ring
  have hcastkk : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
  rw [cd_frac A k (by omega), cd_frac A (k * (k - 1)) (Nat.mul_pos (by omega) (by omega)),
    hcastkk] at hjAR
  -- assemble `j k ℓ` over ℝ
  have hjkl : (j k ℓ : ℝ) = (t : ℝ) * ((j k (ell0 k) : ℝ) + 3) + (j k A : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hjrec; push_cast at h; linarith [h]
  have hcastell0 : (ell0 k : ℝ) = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) - (k : ℝ) := by
    rw [ell0_eq, Nat.cast_sub (le_trans (Nat.le_mul_of_pos_right k (by omega))
      (Nat.le_mul_of_pos_right _ (by omega))), ProofsReductions.castP (by omega)]
  have hcastA : (A : ℝ) = (ℓ : ℝ) - (t : ℝ) * (ell0 k : ℝ) := by
    rw [hAdef, Nat.cast_sub hle]; push_cast; ring
  rw [hjAR, jell0_real hk, hcastA, hcastell0] at hjkl
  rw [hjkl]
  field_simp
  ring

end Hunter.Proved

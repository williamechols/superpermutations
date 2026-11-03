/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsMeta5

/-!
# Theorem 2 — the amortized window, discharged down to the meta-supply residual

This file concretizes the potential `Φ` of `ProofsMeta5` and attacks the single remaining
obligation `AmortizedWindow k Φ`.

The mathematical advance here is the **windowed level-2 excess bound**: converting the
`confinement`/`cover_bound` machinery (which is *local*, not global) into

  `windowExcess_ge_km3` :  `excess q + (k − 3) ≤ excess p`

for the exitless `(|p|−ℓ₀)`-prefix `q` of an exitless `p` in the recursion region — the
"`k − 3` per window" that `ProofsDeficit`/`ProofsMeta3` only *claimed*.  This is the honest
floor under `AmortizedWindow` (whose target is `k − 2` plus the potential difference).

The remaining `+1` is genuinely the meta-confinement (`Proved.alpha_run_bound`) and, as the LP
analysis (`invariant/results.json`, `structural_only: INFEASIBLE`) shows, cannot be avoided by
any bounded structural-only potential.  We isolate it as a precise, named residual
`MetaWindowSupply` and prove `AmortizedWindow` conditional on it, for a concrete `Φ ∈ {0,1}`.

Namespace `Hunter.ProofsMeta6`.  Everything is sorry-free and axiom-clean.
-/

namespace Hunter

open List
open scoped Classical

namespace ProofsMeta6

open ProofsExitless ProofsConfinement ProofsRecursion ProofsExcess ProofsSPrime ProofsDeficit
open ProofsMeta3 ProofsWindow ProofsMeta5
open HPath

variable {k : ℕ}

/-! ## The windowed heavy-boundary count

`ProofsConfinement.confinement` is a *local* statement: no `k` consecutive complete blocks of
an exitless path are joined entirely by doors.  `ProofsConfinement.cover_bound` turns "a heavy
boundary in every `(k−1)`-block window" into a count.  Applying both to a *sub-range* of blocks
`(a, a+M]` gives a windowed heavy count `≥ M ⌈/⌉ (k−1) − 1`, the local analogue of
`prp_3edgebound`. -/

/-- **Windowed heavy count.**  Among the `M` block boundaries `t ∈ (a, a+M]` of an exitless
path (all lying below `numVerts`), at least `M ⌈/⌉ (k−1) − 1` carry weight `≥ 3`.  Local
version of `prp_3edgebound`, proved by `confinement` + `cover_bound` on the block sub-range. -/
theorem window_heavy_count (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    (a M : ℕ) (hM : k * (a + M) < p.numVerts) :
    M ⌈/⌉ (k - 1) - 1 ≤
      ((Finset.Icc 1 M).filter
        (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j))))).card := by
  set J : Finset ℕ := (Finset.Icc 1 M).filter
    (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j)))) with hJdef
  apply ProofsConfinement.cover_bound (d := k - 1) (T := M) (by omega) J
  intro b hb1 hbd
  by_contra hcon
  refine ProofsConfinement.confinement (by omega : 2 ≤ k) hp (t₀ := a + b - 1) ?_ ?_
  · -- `k * ((a+b-1) + k - 1) < numVerts`
    have he1 : (a + b - 1) + k - 1 + 1 ≤ a + M := by omega
    have hmul : k * ((a + b - 1) + k - 1 + 1) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) he1
    have hexp : k * ((a + b - 1) + k - 1 + 1) = k * ((a + b - 1) + k - 1) + k := by ring
    omega
  · intro t ht1 ht2
    -- `t = a + (t - a)`, and the block-offset `t - a` lies in the forbidden window
    have hta : a + (t - a) = t := by omega
    have htle : t ≤ a + M - 1 := by omega
    have hktle : k * t ≤ k * (a + M - 1) := Nat.mul_le_mul (le_refl k) htle
    have hexp2 : k * (a + M - 1) + k = k * (a + M) := by
      have : a + M - 1 + 1 = a + M := by omega
      calc k * (a + M - 1) + k = k * (a + M - 1 + 1) := by ring
        _ = k * (a + M) := by rw [this]
    have hktlt : k * t < p.numVerts := by omega
    have hkt1 : k * t - 1 + 1 = k * t := by
      have : 1 ≤ k * t := by
        have : 1 ≤ t := by omega
        calc 1 ≤ k := by omega
          _ = k * 1 := by ring
          _ ≤ k * t := Nat.mul_le_mul (le_refl k) this
      omega
    have hin : (k * t - 1) + 1 < p.numVerts := by rw [hkt1]; exact hktlt
    have hd : k ∣ ((k * t - 1) + 1) := by rw [hkt1]; exact ⟨t, rfl⟩
    have hge2 := ProofsWindow.boundary_ge_two (by omega : 1 ≤ k) hp hin hd
    rw [hkt1] at hge2
    rcases Nat.lt_or_ge (ew k (p.vert (k * t - 1)) (p.vert (k * t))) 3 with hlt3 | hge3
    · omega
    · exfalso
      apply hcon
      refine ⟨t - a, ?_, by omega, by omega⟩
      rw [hJdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [hta]; exact hge3

/-! ## The windowed level-2 excess floor (`k − 3` per window) — the mathematical advance

`ProofsDeficit`/`ProofsMeta3` *claim* "the level-2 count already delivers `k − 3` per window".
We now prove it.  `window_heavy_count` gives the confinement floor over the block sub-range;
mapping the block boundaries into the `ℓ₀`-window and comparing with the prefix count yields
`edgeCountGe q 3 + (k − 3) ≤ edgeCountGe p 3` and hence `excess q + (k − 3) ≤ excess p`,
unconditionally.  This is the honest floor under the (refuted-at-`k−2`) `WindowExcess`; the
remaining `+1` is exactly the still-open meta-confinement. -/

/-- `M ⌈/⌉ (k−1) = k − 2` for `M = (k−1)(k−2) − 1` (the block count of an `ℓ₀`-window). -/
theorem windowM_ceilDiv (hk : 3 ≤ k) : ((k - 1) * (k - 2) - 1) ⌈/⌉ (k - 1) = k - 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  have hMpos : 1 ≤ (m + 2) * (m + 1) - 1 := by
    have : 2 ≤ (m + 2) * (m + 1) := by nlinarith
    omega
  rw [Proved.ceilDiv_succ_pred hMpos (by omega : 0 < m + 2)]
  have hval : (m + 2) * (m + 1) - 1 - 1 = (m + 2) * m + m := by
    have : (m + 2) * (m + 1) = (m + 2) * m + (m + 2) := by ring
    omega
  have hdiv : ((m + 2) * (m + 1) - 1 - 1) / (m + 2) = m := by
    rw [hval, Nat.mul_add_div (by omega : 0 < m + 2), Nat.div_eq_of_lt (by omega : m < m + 2),
        Nat.add_zero]
  rw [hdiv]

/-- **The windowed heavy-edge floor.**  For an exitless `p` in the recursion region and its
`(|p|−ℓ₀)`-prefix `q`, the last `ℓ₀`-window carries at least `k − 3` weight-`≥3` edges:
`edgeCountGe q 3 + (k − 3) ≤ edgeCountGe p 3`.  This is the confinement floor (`WindowHeavy3` is
this with `k − 2`; it is off by exactly the meta-confinement `+1`). -/
theorem window_heavy3_ge (hk : 3 ≤ k) {p q : HPath k} (hp : p.Exitless)
    (hlt : k * (k - 1) * (k - 2) < p.numVerts)
    (hprefix : q.verts = p.verts.take (p.numVerts - ell0 k)) :
    edgeCountGe q 3 + (k - 3) ≤ edgeCountGe p 3 := by
  set N := p.numVerts with hNdef
  set n := N - ell0 k with hndef
  -- basic ℓ₀ facts
  have he0val : ell0 k = k * (k - 1) * (k - 2) - k := rfl
  have hm2 : 2 ≤ (k - 1) * (k - 2) := by nlinarith [show 2 ≤ k - 1 by omega, show 1 ≤ k - 2 by omega]
  have hkprod : k * ((k - 1) * (k - 2)) = k * (k - 1) * (k - 2) := by ring
  have hPk : k ≤ k * (k - 1) * (k - 2) := by
    have h1 : k * 1 ≤ k * (k - 1) := Nat.mul_le_mul (le_refl k) (by omega)
    have h2 : k * (k - 1) * 1 ≤ k * (k - 1) * (k - 2) := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  have he0lt : ell0 k < N := by rw [he0val]; omega
  have hNsum : N = n + ell0 k := by rw [hndef]; omega
  have hn1 : k < n := by rw [hndef, he0val]; omega
  have hnle : n ≤ N := by omega
  -- q.numVerts = n
  have hqn : q.numVerts = n := by
    have hlen : q.verts.length = (p.verts.take (N - ell0 k)).length := by rw [hprefix]
    have hNl : p.verts.length = N := rfl
    rw [List.length_take, hNl] at hlen
    show q.verts.length = n
    rw [hlen, hndef]; omega
  -- M := ell0 / k = (k-1)(k-2) - 1 blocks, with k * M = ell0
  have hdvd : k ∣ ell0 k := k_dvd_ell0 hk
  set M := ell0 k / k with hMdef
  have hkM : k * M = ell0 k := Nat.mul_div_cancel' hdvd
  have hMval : M = (k - 1) * (k - 2) - 1 := by
    have hB1 : (k - 1) * (k - 2) - 1 + 1 = (k - 1) * (k - 2) := by omega
    have hkB : k * ((k - 1) * (k - 2) - 1) + k = k * ((k - 1) * (k - 2)) := by
      calc k * ((k - 1) * (k - 2) - 1) + k
          = k * ((k - 1) * (k - 2) - 1 + 1) := by ring
        _ = k * ((k - 1) * (k - 2)) := by rw [hB1]
    have hkMk : k * M + k = k * ((k - 1) * (k - 2)) := by
      rw [hkM, he0val, hkprod]; omega
    have hcancel : k * M = k * ((k - 1) * (k - 2) - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hcancel
  -- a := (n-1)/k so that a+1 is the first block whose boundary lands ≥ n
  set a := (n - 1) / k with hadef
  have hdivmod : k * a + (n - 1) % k = n - 1 := Nat.div_add_mod (n - 1) k
  have hmodlt : (n - 1) % k < k := Nat.mod_lt (n - 1) (by omega)
  clear_value a
  -- the window heavy count
  have hM_lt : k * (a + M) < N := by
    have hexp : k * (a + M) = k * a + ell0 k := by rw [Nat.mul_add, hkM]
    omega
  have hcount := window_heavy_count hk hp a M hM_lt
  have hMc : M ⌈/⌉ (k - 1) = k - 2 := by rw [hMval]; exact windowM_ceilDiv hk
  -- the window heavy set at vertex level
  set Wf : Finset ℕ := (Finset.Ico (n - 1) (N - 1)).filter
    (fun i => 3 ≤ ew k (p.vert i) (p.vert (i + 1))) with hWfdef
  set J : Finset ℕ := (Finset.Icc 1 M).filter
    (fun j => 3 ≤ ew k (p.vert (k * (a + j) - 1)) (p.vert (k * (a + j)))) with hJdef
  -- |J| ≤ |Wf| via the block-boundary injection j ↦ k*(a+j) - 1
  have hJW : J.card ≤ Wf.card := by
    apply Finset.card_le_card_of_injOn (fun j => k * (a + j) - 1)
    · intro j hj
      rw [hJdef] at hj
      obtain ⟨hjIcc, hjh⟩ := Finset.mem_filter.mp hj
      obtain ⟨hj1, hjM⟩ := Finset.mem_Icc.mp hjIcc
      have haj_lo : k * (a + 1) ≤ k * (a + j) := Nat.mul_le_mul (le_refl k) (by omega)
      have haj_hi : k * (a + j) ≤ k * (a + M) := Nat.mul_le_mul (le_refl k) (by omega)
      have ha1 : k * (a + 1) = k * a + k := by ring
      have haM : k * (a + M) = k * a + ell0 k := by rw [Nat.mul_add, hkM]
      have hajpos : 1 ≤ k * (a + j) := by omega
      have haj1 : k * (a + j) - 1 + 1 = k * (a + j) := by omega
      show k * (a + j) - 1 ∈ Wf
      rw [hWfdef, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [haj1]; exact hjh
    · intro j1 hj1 j2 hj2 heq
      simp only [Finset.mem_coe] at hj1 hj2
      rw [hJdef] at hj1 hj2
      have hb1 : 1 ≤ j1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj1).1).1
      have hb2 : 1 ≤ j2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj2).1).1
      have heq' : k * (a + j1) - 1 = k * (a + j2) - 1 := heq
      have h1 : 0 < k * (a + j1) := Nat.mul_pos (by omega) (by omega)
      have h2 : 0 < k * (a + j2) := Nat.mul_pos (by omega) (by omega)
      have heq2 : k * (a + j1) = k * (a + j2) := by omega
      have hcancel := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) heq2
      omega
  -- edgeCountGe p 3 = edgeCountGe q 3 + |Wf|
  have hsplit : edgeCountGe p 3 = edgeCountGe q 3 + Wf.card := by
    have hunion : Finset.range (N - 1) = Finset.Ico 0 (n - 1) ∪ Finset.Ico (n - 1) (N - 1) := by
      rw [Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega), Finset.range_eq_Ico]
    have hdisj : Disjoint (Finset.Ico 0 (n - 1)) (Finset.Ico (n - 1) (N - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      rw [Finset.mem_Ico] at hx hx2
      omega
    rw [edgeCountGe, ← hNdef, hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    congr 1
    · -- prefix count equals edgeCountGe q 3
      rw [edgeCountGe, hqn, Finset.range_eq_Ico]
      congr 1
      apply Finset.filter_congr
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [prefix_vert_eq hprefix hnle (show i < n by omega),
          prefix_vert_eq hprefix hnle (show i + 1 < n by omega)]
  omega

/-- **The windowed excess floor.**  `excess q + (k − 3) ≤ excess p` for the `ℓ₀`-window of an
exitless recursion-region path.  The layer decomposition `excess = Σ_{r≥3} edgeCountGe·r` is
prefix-monotone, so the excess gap dominates the `r = 3` layer gap, bounded below by
`window_heavy3_ge`.  This is the LP-feasible floor: `WindowExcess` (the `k − 2` version) is
refuted, but its `k − 3` weakening holds unconditionally. -/
theorem windowExcess_ge_km3 (hk : 3 ≤ k) {p q : HPath k} (hp : p.Exitless)
    (hlt : k * (k - 1) * (k - 2) < p.numVerts)
    (hprefix : q.verts = p.verts.take (p.numVerts - ell0 k)) :
    excess q + (k - 3) ≤ excess p := by
  have hnle : p.numVerts - ell0 k ≤ p.numVerts := Nat.sub_le _ _
  have hqn : q.numVerts = p.numVerts - ell0 k := by
    have hlen : q.verts.length = (p.verts.take (p.numVerts - ell0 k)).length := by rw [hprefix]
    have hN : p.verts.length = p.numVerts := rfl
    rw [List.length_take, hN] at hlen
    show q.verts.length = _
    rw [hlen]; omega
  have hmono : ∀ r, edgeCountGe q r ≤ edgeCountGe p r :=
    fun r => edgeCountGe_prefix_le hprefix hnle hqn r
  have hres : edgeCountGe q 3 + (k - 3) ≤ edgeCountGe p 3 := window_heavy3_ge hk hp hlt hprefix
  rw [excess, excess]
  have h3mem : (3 : ℕ) ∈ Finset.Icc 3 k := by rw [Finset.mem_Icc]; omega
  rw [← Finset.add_sum_erase _ (edgeCountGe p) h3mem,
      ← Finset.add_sum_erase _ (edgeCountGe q) h3mem]
  have hsum : ∑ r ∈ (Finset.Icc 3 k).erase 3, edgeCountGe q r
            ≤ ∑ r ∈ (Finset.Icc 3 k).erase 3, edgeCountGe p r :=
    Finset.sum_le_sum (fun r _ => hmono r)
  omega

/-! ## The amortized window, discharged to the meta-supply residual

`AmortizedWindow k Φ` demands `excess q + (k−2) + Φ p ≤ excess p + Φ q`.  The windowed floor
`windowExcess_ge_km3` supplies `k − 3` of that unconditionally, so the only windows that still
need work are the ones where the banked surplus does *not* strictly increase across the window
(`¬ (Φ p + 1 ≤ Φ q)`).  We package exactly those as `MetaWindowSupply`, a strict weakening of
`AmortizedWindow`: the "release" windows (`Φ p + 1 ≤ Φ q`) — including the front-loading windows
that *refute* `WindowExcess` — are discharged here by the floor.  On the concrete state-based
potential of the LP analysis these release windows are precisely the `(Φ p, Φ q) = (0,1)` corner
(the `ℓ = 120` witness), so this genuinely shrinks the residual by the corner where the naive
per-window count fails. -/

/-- **The meta-supply residual** (a strict weakening of `AmortizedWindow`).  For each `ℓ₀`-window
either the potential strictly increases going into the prefix (`Φ p + 1 ≤ Φ q`, discharged by the
`k − 3` floor) or the window carries the full amortized demand.  The second disjunct is the only
genuine content; it is `AmortizedWindow` restricted to non-release windows, where the still-open
meta-confinement supplies the extra `+1`. -/
def MetaWindowSupply (k : ℕ) (Φ : HPath k → ℕ) : Prop :=
  ∀ p q : HPath k, p.Exitless → q.Exitless →
    k * (k - 1) * (k - 2) < p.numVerts →
    q.verts = p.verts.take (p.numVerts - ell0 k) →
    Φ p + 1 ≤ Φ q ∨ excess q + (k - 2) + Φ p ≤ excess p + Φ q

/-- **`MetaWindowSupply k Φ → AmortizedWindow k Φ`.**  The windowed floor `windowExcess_ge_km3`
(`excess q + (k−3) ≤ excess p`) discharges the release windows (`Φ p + 1 ≤ Φ q`); the rest is the
`MetaWindowSupply` residual verbatim.  Holds for *any* `Φ`. -/
theorem amortizedWindow_of_metaSupply (hk : 3 ≤ k) {Φ : HPath k → ℕ}
    (hsupply : MetaWindowSupply k Φ) : AmortizedWindow k Φ := by
  intro p q hpe hqe hlt hprefix
  rcases hsupply p q hpe hqe hlt hprefix with hrel | hdirect
  · have hfloor : excess q + (k - 3) ≤ excess p := windowExcess_ge_km3 hk hpe hlt hprefix
    omega
  · exact hdirect

/-! ## A concrete potential and its base-region obligation

The base-region obligation `BaseBound` is discharged for the natural *surplus-over-the-level-2-
floor* potential `Φ_surplus p = min 1 (excess p − D_base(|p|))`, `D_base(ℓ) = ⌈ℓ/(k(k−1))⌉ − 1`.
This is a genuine `{0,1}`-valued potential and `BaseBound` follows unconditionally from the level-2
bound `excess_ge_Dbase`.  (It is *not* the potential that satisfies `AmortizedWindow`: at the
`ℓ = 120` witness it takes `(Φ p, Φ q) = (1,1)` where the amortized window needs `(0,1)`, so the
window obligation genuinely requires the finer state-based potential of the LP analysis — the
base and window obligations bite on different structure.) -/

/-- The surplus-over-level-2-floor potential, `Φ ∈ {0,1}`. -/
noncomputable def PhiSurplus (k : ℕ) (p : HPath k) : ℕ :=
  min 1 (excess p - (p.numVerts ⌈/⌉ (k * (k - 1)) - 1))

/-- **`BaseBound` for the surplus potential.**  Unconditional, from `excess_ge_Dbase`:
`D_base + Φ_surplus ≤ excess`, and on the base region `j = jbase = (ℓ−1)+(⌈ℓ/k⌉−1)+D_base`. -/
theorem baseBound_phiSurplus (hk : 3 ≤ k) : BaseBound k (PhiSurplus k) := by
  intro p hpe h0 hle
  have hDb : (p.numVerts ⌈/⌉ (k * (k - 1)) - 1) ≤ excess p := excess_ge_Dbase hk hpe
  have hPhi : PhiSurplus k p ≤ excess p - (p.numVerts ⌈/⌉ (k * (k - 1)) - 1) := by
    unfold PhiSurplus; exact min_le_right _ _
  have hj : j k p.numVerts
      = p.numVerts + (p.numVerts ⌈/⌉ k) + (p.numVerts ⌈/⌉ (k * (k - 1))) - 3 :=
    j_base (Or.inl hle)
  have hck1 : 1 ≤ p.numVerts ⌈/⌉ k := by
    rw [Proved.ceilDiv_succ_pred h0 (by omega : 0 < k)]; exact Nat.le_add_left 1 _
  have hck2 : 1 ≤ p.numVerts ⌈/⌉ (k * (k - 1)) := by
    rw [Proved.ceilDiv_succ_pred h0 (Nat.mul_pos (by omega) (by omega))]; exact Nat.le_add_left 1 _
  omega

/-! ## `thm2` through the meta-supply residual -/

/-- **`thm2` conditional on `BaseBound` + `MetaWindowSupply`.**  For any `Φ`, discharging the
base-region invariant and the (floor-weakened) meta-supply gives Hunter's Theorem 2
(`j_k(ℓ) ≤ i_k(ℓ)`) for every `ℓ`.  This is a strictly smaller residual than
`ProofsMeta5.thm2_of_amortizedWindow`: the release windows (where `WindowExcess` is refuted) are
already closed by `windowExcess_ge_km3`. -/
theorem thm2_of_metaSupply {k ℓ : ℕ} (hk : 3 ≤ k) (Φ : HPath k → ℕ)
    (hbase : BaseBound k Φ) (hsupply : MetaWindowSupply k Φ) (hℓ : HasExitlessPath k ℓ) :
    j k ℓ ≤ iExitless k ℓ :=
  ProofsMeta5.thm2_of_amortizedWindow hk Φ hbase (amortizedWindow_of_metaSupply hk hsupply) hℓ

end ProofsMeta6

end Hunter

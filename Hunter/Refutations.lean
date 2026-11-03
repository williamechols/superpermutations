/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.ProofsWindow

/-!
# Refutation of the window residuals `WindowExcess 5` and `WindowHeavy3 5`

The window track (`ProofsDeficit`, `ProofsWindow`) reduced Hunter's Theorem 2 to two candidate
"uniform, per-window" residuals:

* `WindowExcess k` — every `ℓ₀`-window of an exitless path carries `≥ k−2` units of
  `≥3`-weight excess (`excess q + (k−2) ≤ excess p`);
* `WindowHeavy3 k` — the sharpened count form (`edgeCountGe q 3 + (k−2) ≤ edgeCountGe p 3`).

**Both are FALSE at `k = 5`.**  This file gives a machine-checked counterexample: the optimal
exitless witness path of 120 vertices in `𝒮_5`.  Its 65-vertex exitless prefix `q` has
`excess q = 4` while the full path `p` has `excess p = 6`; `WindowExcess 5` demands
`4 + 3 = 7 ≤ 6` — false.  Likewise `edgeCountGe q 3 = 3`, `edgeCountGe p 3 = 5` (only `2`
heavy edges in the top `ℓ₀ = 55`-window, not the demanded `3`), refuting `WindowHeavy3 5`.

The *cumulative* frontier `ExcessFrontier k` (`ProofsRecursion`) is untouched — it is consistent
with all `k ≤ 5` data and remains the sole open leaf of Theorem 2.  See `PROGRESS-refutations.md`.

## Computability bridge

`ew`/`wt` are `noncomputable` (built on `Nat.sInf`), so `decide` cannot reduce them directly.
We introduce a *computable* mirror `wtc5` and prove `ew 5 u v = wtc5 u.1 v.1` (`ew5_eq`), then
reflect `edgeCountGe`/`excess`/`Exitless` onto computable list operations, and discharge the
finite numeric facts by **kernel `decide`** (no `native_decide`).  Both refutations carry only the
project-standard axioms `[propext, Classical.choice, Quot.sound]` — verified by `#print axioms`,
see `PROGRESS-refutations.md`.
-/

namespace Hunter

open List
open scoped Classical

set_option maxRecDepth 10000

namespace Refutations

open HPath

/-- `IsPermWord k w` is *computably* decidable (it is a conjunction of a `Nodup` test and a
`Finset` equality).  The ambient `open scoped Classical` only supplies a low-priority fallback,
so registering this instance lets `decide` evaluate the concrete permutation-word proofs. -/
instance decIsPermWord (k : ℕ) (w : List ℕ) : Decidable (IsPermWord k w) :=
  decidable_of_iff (w.Nodup ∧ w.toFinset = Finset.Icc 1 k) Iff.rfl

/-! ## A computable mirror of the edge weight `wt` at `k = 5` -/

/-- **Computable edge weight at `k = 5`.**  For permutation words `u, v` of length `5`,
`wt 5 u v = wtc5 u v` (`wt_eq_wtc5`).  Unlike `wt` (a `noncomputable` `Nat.sInf`), this
scans the offsets `d = 1,…,5` explicitly and so reduces under `decide`. -/
def wtc5 (u v : List ℕ) : ℕ :=
  if u.drop 1 = v.take 4 then 1
  else if u.drop 2 = v.take 3 then 2
  else if u.drop 3 = v.take 2 then 3
  else if u.drop 4 = v.take 1 then 4
  else 5

/-- **Lower bound on `wt`.**  If every smaller offset `d' < d` fails the overlap test, then
`d ≤ wt 5 u v`.  (Dual to `wt_le`; together they pin `wt` exactly.) -/
theorem le_wt {u v : List ℕ} {d : ℕ} (hu : u.length ≤ 5)
    (h : ∀ d', 1 ≤ d' → d' < d → u.drop d' ≠ v.take (5 - d')) : d ≤ wt 5 u v := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, _, h3⟩ := wt_spec (by norm_num : (1 : ℕ) ≤ 5) hu (v := v)
  exact h _ h1 hlt h3

/-- **The bridge.**  `wt 5 u v = wtc5 u v` for any `u` of length `5`. -/
theorem wt_eq_wtc5 {u v : List ℕ} (hu : u.length = 5) : wt 5 u v = wtc5 u v := by
  have hule : u.length ≤ 5 := by omega
  have hge1 : 1 ≤ wt 5 u v := (wt_spec (by norm_num) hule (v := v)).1
  unfold wtc5
  split_ifs with h1 h2 h3 h4
  · -- d = 1
    have hle : wt 5 u v ≤ 1 := wt_le (by norm_num) (by norm_num) (by simpa using h1)
    omega
  · -- d = 2
    have hle : wt 5 u v ≤ 2 := wt_le (by norm_num) (by norm_num) (by simpa using h2)
    have hge : 2 ≤ wt 5 u v := le_wt hule (by
      intro d' hd1 hd2
      interval_cases d'; simpa using h1)
    omega
  · -- d = 3
    have hle : wt 5 u v ≤ 3 := wt_le (by norm_num) (by norm_num) (by simpa using h3)
    have hge : 3 ≤ wt 5 u v := le_wt hule (by
      intro d' hd1 hd2
      interval_cases d' <;> simp_all)
    omega
  · -- d = 4
    have hle : wt 5 u v ≤ 4 := wt_le (by norm_num) (by norm_num) (by simpa using h4)
    have hge : 4 ≤ wt 5 u v := le_wt hule (by
      intro d' hd1 hd2
      interval_cases d' <;> simp_all)
    omega
  · -- d = 5
    have hle : wt 5 u v ≤ 5 := wt_le (by norm_num) (by norm_num) (by
      have : u.drop 5 = [] := by rw [List.drop_eq_nil_iff]; omega
      simp [this])
    have hge : 5 ≤ wt 5 u v := le_wt hule (by
      intro d' hd1 hd2
      interval_cases d' <;> simp_all)
    omega

/-- `ew 5 u v = wtc5 u.1 v.1` for vertices of `𝒮_5` (words have length `5`). -/
theorem ew5_eq (u v : Vtx 5) : ew 5 u v = wtc5 u.1 v.1 :=
  wt_eq_wtc5 u.2.length

open ProofsExitless Proved ProofsRecursion ProofsExcess ProofsDeficit ProofsWindow

/-! ## Reflecting `edgeCountGe` / `excess` onto a computable edge-weight list -/

/-- The **computable** edge-weight list of a path: `wtc5` applied to each consecutive pair of
underlying words.  Equals the semantic weight list `zipWith (ew 5)` (`ewcList_eq`). -/
def ewcList (L : List (Vtx 5)) : List ℕ :=
  L.zipWith (fun u v => wtc5 u.1 v.1) L.tail

/-- The semantic edge-weight list `zipWith (ew 5) verts tail` equals its index-map form. -/
theorem zipWith_ew_eq_map (p : HPath 5) :
    p.verts.zipWith (ew 5) p.verts.tail
      = (List.range (p.numVerts - 1)).map (fun i => ew 5 (p.vert i) (p.vert (i + 1))) := by
  apply List.ext_getElem
  · rw [List.length_zipWith, List.length_map, List.length_range, List.length_tail]
    have : p.numVerts = p.verts.length := rfl
    omega
  · intro i h1 h2
    have hlen : i < p.verts.tail.length := by
      rw [List.length_tail]
      rw [List.length_zipWith, List.length_tail] at h1
      omega
    have hi1 : i < p.numVerts := by
      rw [List.length_zipWith, List.length_tail] at h1
      have : p.numVerts = p.verts.length := rfl
      omega
    have hi2 : i + 1 < p.numVerts := by
      rw [List.length_tail] at hlen
      have : p.numVerts = p.verts.length := rfl
      omega
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_tail]
    exact (congrArg₂ (ew 5) (vert_getElem p hi1) (vert_getElem p hi2)).symm

/-- The semantic and computable edge-weight lists agree (pointwise `ew5_eq`). -/
theorem ewcList_eq (p : HPath 5) :
    p.verts.zipWith (ew 5) p.verts.tail = ewcList p.verts := by
  have hfun : (ew 5 : Vtx 5 → Vtx 5 → ℕ) = (fun u v => wtc5 u.1 v.1) :=
    funext fun u => funext fun v => ew5_eq u v
  rw [ewcList, hfun]

/-- **Reflection of `edgeCountGe`.**  The `≥r`-edge count equals the sum of indicators over the
computable weight list `ewcList p.verts`. -/
theorem edgeCountGe_eq (p : HPath 5) (r : ℕ) :
    edgeCountGe p r
      = ((ewcList p.verts).map (fun w => if r ≤ w then (1 : ℕ) else 0)).sum := by
  have key : edgeCountGe p r
      = ∑ i ∈ Finset.range (p.numVerts - 1),
          (if r ≤ ew 5 (p.vert i) (p.vert (i + 1)) then (1 : ℕ) else 0) := by
    rw [edgeCountGe, Finset.card_filter]
  rw [key, ← list_range_map_sum]
  rw [show (fun i => if r ≤ ew 5 (p.vert i) (p.vert (i + 1)) then (1 : ℕ) else 0)
        = (fun w => if r ≤ w then (1 : ℕ) else 0) ∘
            (fun i => ew 5 (p.vert i) (p.vert (i + 1))) from rfl]
  rw [← List.map_map, ← zipWith_ew_eq_map, ewcList_eq]

/-- **Reflection of `excess`.**  `excess p = Σ_{r=3}^{5} (indicator sum over `ewcList p.verts`)`,
a fully computable expression. -/
theorem excess_eq (p : HPath 5) :
    excess p
      = ∑ r ∈ Finset.Icc 3 5,
          ((ewcList p.verts).map (fun w => if r ≤ w then (1 : ℕ) else 0)).sum := by
  rw [excess]
  exact Finset.sum_congr rfl (fun r _ => edgeCountGe_eq p r)

/-! ## Reflecting `Exitless` onto a computable early-exit scan -/

/-- A fixed vertex, used only as the (never-reached) out-of-range fallback of `getD`. -/
def vtx0 : Vtx 5 := ⟨[1, 2, 3, 4, 5], by decide⟩

/-- **Computable early-exit scan.**  Mirrors `EarlyExit`: at some index `i` the outgoing edge is
heavy (`≥2`) yet the weight-1 successor `σ(p[i])` has not been visited before `i`
(`i < idxOf(σ(p[i]))`).  If this returns `false`, the path is `Exitless`
(`exitless_of_hasEarlyExit_false`). -/
def hasEarlyExit (L : List (Vtx 5)) : Bool :=
  (List.range (L.length - 1)).any (fun i =>
    decide (2 ≤ wtc5 (L.getD i vtx0).1 (L.getD (i + 1) vtx0).1) &&
    decide (i < L.idxOf (sigma (L.getD i vtx0))))

/-- On the in-range indices, `getD … vtx0` recovers the semantic vertex `p.vert`. -/
theorem getD_vtx0_eq (p : HPath 5) {i : ℕ} (hi : i < p.numVerts) :
    p.verts.getD i vtx0 = p.vert i := by
  rw [HPath.vert, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

/-- **The bridge.**  Any semantic early exit is witnessed by the computable scan. -/
theorem hasEarlyExit_of_earlyExit {p : HPath 5} (h : EarlyExit p) :
    hasEarlyExit p.verts = true := by
  obtain ⟨i, hi, hw, hpos⟩ := h
  have hi0 : i < p.numVerts := by omega
  have hi1 : i + 1 < p.numVerts := hi
  rw [hasEarlyExit, List.any_eq_true]
  refine ⟨i, ?_, ?_⟩
  · rw [List.mem_range]
    have : p.numVerts = p.verts.length := rfl
    omega
  · rw [getD_vtx0_eq p hi0, getD_vtx0_eq p hi1, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, ← ew5_eq]
    exact ⟨hw, hpos⟩

/-- **`hasEarlyExit p.verts = false → p.Exitless`.**  The computable check certifies
exitlessness. -/
theorem exitless_of_hasEarlyExit_false {p : HPath 5}
    (h : hasEarlyExit p.verts = false) : p.Exitless := by
  intro hee
  rw [hasEarlyExit_of_earlyExit hee] at h
  exact Bool.noConfusion h

/-- The 120-vertex optimal exitless witness path in `𝒮_5` (indices into `all_perms 5`;
see scratchpad `thm2big/witness_paths.txt`, the `ELL 120` line). Each vertex carries its
`IsPermWord 5` proof by `decide`. -/
def theVerts : List (Vtx 5) :=
 [
  ⟨[1,2,3,4,5], by decide⟩, ⟨[2,3,4,5,1], by decide⟩, ⟨[3,4,5,1,2], by decide⟩, ⟨[4,5,1,2,3], by decide⟩,
  ⟨[5,1,2,3,4], by decide⟩, ⟨[2,3,4,1,5], by decide⟩, ⟨[3,4,1,5,2], by decide⟩, ⟨[4,1,5,2,3], by decide⟩,
  ⟨[1,5,2,3,4], by decide⟩, ⟨[5,2,3,4,1], by decide⟩, ⟨[3,4,1,2,5], by decide⟩, ⟨[4,1,2,5,3], by decide⟩,
  ⟨[1,2,5,3,4], by decide⟩, ⟨[2,5,3,4,1], by decide⟩, ⟨[5,3,4,1,2], by decide⟩, ⟨[4,1,2,3,5], by decide⟩,
  ⟨[1,2,3,5,4], by decide⟩, ⟨[2,3,5,4,1], by decide⟩, ⟨[3,5,4,1,2], by decide⟩, ⟨[5,4,1,2,3], by decide⟩,
  ⟨[2,3,1,4,5], by decide⟩, ⟨[3,1,4,5,2], by decide⟩, ⟨[1,4,5,2,3], by decide⟩, ⟨[4,5,2,3,1], by decide⟩,
  ⟨[5,2,3,1,4], by decide⟩, ⟨[3,1,4,2,5], by decide⟩, ⟨[1,4,2,5,3], by decide⟩, ⟨[4,2,5,3,1], by decide⟩,
  ⟨[2,5,3,1,4], by decide⟩, ⟨[5,3,1,4,2], by decide⟩, ⟨[1,4,2,3,5], by decide⟩, ⟨[4,2,3,5,1], by decide⟩,
  ⟨[2,3,5,1,4], by decide⟩, ⟨[3,5,1,4,2], by decide⟩, ⟨[5,1,4,2,3], by decide⟩, ⟨[4,2,3,1,5], by decide⟩,
  ⟨[2,3,1,5,4], by decide⟩, ⟨[3,1,5,4,2], by decide⟩, ⟨[1,5,4,2,3], by decide⟩, ⟨[5,4,2,3,1], by decide⟩,
  ⟨[3,1,2,4,5], by decide⟩, ⟨[1,2,4,5,3], by decide⟩, ⟨[2,4,5,3,1], by decide⟩, ⟨[4,5,3,1,2], by decide⟩,
  ⟨[5,3,1,2,4], by decide⟩, ⟨[1,2,4,3,5], by decide⟩, ⟨[2,4,3,5,1], by decide⟩, ⟨[4,3,5,1,2], by decide⟩,
  ⟨[3,5,1,2,4], by decide⟩, ⟨[5,1,2,4,3], by decide⟩, ⟨[2,4,3,1,5], by decide⟩, ⟨[4,3,1,5,2], by decide⟩,
  ⟨[3,1,5,2,4], by decide⟩, ⟨[1,5,2,4,3], by decide⟩, ⟨[5,2,4,3,1], by decide⟩, ⟨[4,3,1,2,5], by decide⟩,
  ⟨[3,1,2,5,4], by decide⟩, ⟨[1,2,5,4,3], by decide⟩, ⟨[2,5,4,3,1], by decide⟩, ⟨[5,4,3,1,2], by decide⟩,
  ⟨[2,1,3,5,4], by decide⟩, ⟨[1,3,5,4,2], by decide⟩, ⟨[3,5,4,2,1], by decide⟩, ⟨[5,4,2,1,3], by decide⟩,
  ⟨[4,2,1,3,5], by decide⟩, ⟨[1,3,5,2,4], by decide⟩, ⟨[3,5,2,4,1], by decide⟩, ⟨[5,2,4,1,3], by decide⟩,
  ⟨[2,4,1,3,5], by decide⟩, ⟨[4,1,3,5,2], by decide⟩, ⟨[3,5,2,1,4], by decide⟩, ⟨[5,2,1,4,3], by decide⟩,
  ⟨[2,1,4,3,5], by decide⟩, ⟨[1,4,3,5,2], by decide⟩, ⟨[4,3,5,2,1], by decide⟩, ⟨[5,2,1,3,4], by decide⟩,
  ⟨[2,1,3,4,5], by decide⟩, ⟨[1,3,4,5,2], by decide⟩, ⟨[3,4,5,2,1], by decide⟩, ⟨[4,5,2,1,3], by decide⟩,
  ⟨[1,3,2,5,4], by decide⟩, ⟨[3,2,5,4,1], by decide⟩, ⟨[2,5,4,1,3], by decide⟩, ⟨[5,4,1,3,2], by decide⟩,
  ⟨[4,1,3,2,5], by decide⟩, ⟨[3,2,5,1,4], by decide⟩, ⟨[2,5,1,4,3], by decide⟩, ⟨[5,1,4,3,2], by decide⟩,
  ⟨[1,4,3,2,5], by decide⟩, ⟨[4,3,2,5,1], by decide⟩, ⟨[2,5,1,3,4], by decide⟩, ⟨[5,1,3,4,2], by decide⟩,
  ⟨[1,3,4,2,5], by decide⟩, ⟨[3,4,2,5,1], by decide⟩, ⟨[4,2,5,1,3], by decide⟩, ⟨[5,1,3,2,4], by decide⟩,
  ⟨[1,3,2,4,5], by decide⟩, ⟨[3,2,4,5,1], by decide⟩, ⟨[2,4,5,1,3], by decide⟩, ⟨[4,5,1,3,2], by decide⟩,
  ⟨[3,2,1,5,4], by decide⟩, ⟨[2,1,5,4,3], by decide⟩, ⟨[1,5,4,3,2], by decide⟩, ⟨[5,4,3,2,1], by decide⟩,
  ⟨[4,3,2,1,5], by decide⟩, ⟨[2,1,5,3,4], by decide⟩, ⟨[1,5,3,4,2], by decide⟩, ⟨[5,3,4,2,1], by decide⟩,
  ⟨[3,4,2,1,5], by decide⟩, ⟨[4,2,1,5,3], by decide⟩, ⟨[1,5,3,2,4], by decide⟩, ⟨[5,3,2,4,1], by decide⟩,
  ⟨[3,2,4,1,5], by decide⟩, ⟨[2,4,1,5,3], by decide⟩, ⟨[4,1,5,3,2], by decide⟩, ⟨[5,3,2,1,4], by decide⟩,
  ⟨[3,2,1,4,5], by decide⟩, ⟨[2,1,4,5,3], by decide⟩, ⟨[1,4,5,3,2], by decide⟩, ⟨[4,5,3,2,1], by decide⟩
 ]

/-- The witness path `P` as an `HPath 5`. -/
def P : HPath 5 := ⟨theVerts, by decide, by decide⟩

/-- `P` is exitless (its computable early-exit scan returns `false`). -/
theorem P_exitless : P.Exitless :=
  exitless_of_hasEarlyExit_false (by decide)

/-- `P` has `120 > 60 = 5·4·3` vertices, so it lies in the recursion region. -/
theorem P_numVerts : P.numVerts = 120 := rfl

/-- `P.numVerts − ℓ₀(5) = 120 − 55 = 65`: the exitless prefix length demanded by the window
inequalities. -/
theorem prefix_len : P.numVerts - ell0 5 = 65 := by decide

/-! ## The two refutations -/

/-- **`WindowExcess 5` is FALSE.**  The 120-vertex witness `P` and its 65-vertex exitless prefix
`q` satisfy every hypothesis of `WindowExcess 5`, yet `excess q + (5−2) = 4 + 3 = 7 ≰ 6 = excess P`.

Discharged entirely by kernel `decide` (via the computable reflections `excess_eq` and
`hasEarlyExit`); the axiom set is the project standard `[propext, Classical.choice, Quot.sound]`
— no `native_decide`, no `Lean.ofReduceBool`. -/
theorem windowExcess_false : ¬ WindowExcess 5 := by
  intro hW
  have hp : P.Exitless := P_exitless
  have hlt : 5 * (5 - 1) * (5 - 2) < P.numVerts := by rw [P_numVerts]; norm_num
  obtain ⟨q, hqv, hqe⟩ :=
    prefix_exitless hp (by norm_num : (1 : ℕ) ≤ 65) (by rw [P_numVerts]; norm_num)
  have hpre : q.verts = P.verts.take (P.numVerts - ell0 5) := by rw [hqv, prefix_len]
  have hdemand := hW P q hp hqe hlt hpre
  have hep : excess P = 6 := by rw [excess_eq]; decide
  have heq : excess q = 4 := by rw [excess_eq, hqv]; decide
  rw [hep, heq] at hdemand
  omega

/-- **`WindowHeavy3 5` is FALSE.**  Same witness: the top `ℓ₀ = 55`-window carries only `2`
weight-`≥3` edges (`edgeCountGe P 3 − edgeCountGe q 3 = 5 − 3 = 2`), while `WindowHeavy3 5`
demands `k − 2 = 3`.  So `edgeCountGe q 3 + 3 = 3 + 3 = 6 ≰ 5 = edgeCountGe P 3`.

Discharged entirely by kernel `decide` (via the computable reflection `edgeCountGe_eq`); axiom set
is the project standard `[propext, Classical.choice, Quot.sound]` — no `native_decide`. -/
theorem windowHeavy3_false : ¬ WindowHeavy3 5 := by
  intro hW
  have hp : P.Exitless := P_exitless
  have hlt : 5 * (5 - 1) * (5 - 2) < P.numVerts := by rw [P_numVerts]; norm_num
  obtain ⟨q, hqv, hqe⟩ :=
    prefix_exitless hp (by norm_num : (1 : ℕ) ≤ 65) (by rw [P_numVerts]; norm_num)
  have hpre : q.verts = P.verts.take (P.numVerts - ell0 5) := by rw [hqv, prefix_len]
  have hdemand := hW P q hp hqe hlt hpre
  have hep : edgeCountGe P 3 = 5 := by rw [edgeCountGe_eq]; decide
  have heq : edgeCountGe q 3 = 3 := by rw [edgeCountGe_eq, hqv]; decide
  rw [hep, heq] at hdemand
  omega

end Refutations

end Hunter

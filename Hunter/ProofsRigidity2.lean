/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Hunter.Words
import Hunter.Graph
import Hunter.ProofsConfinement
import Hunter.ProofsClosure3

/-!
# Hunter Theorem 2, §2 — the RIGIDITY LEMMA (`Hunter/ProofsRigidity2.lean`)

This file transcribes Hunter's §2 rigidity argument (the machine-verified `PROOF_S2.md`) at the
word / rotation-class level, in the same coordinate system as the §3 CLOSURE LEMMA
(`Hunter/ProofsClosure3.lean`).  The two documents share conventions:

`rho = rotate 1` is Hunter's `σ`; `door w = w.drop 2 ++ [w[1],w[0]]` is Hunter's `τ`; the block
**exit** of a block entry `u` (a length-`k` permutation word) is `u.rotate (k−1)` (right rotation).
The fresh weight-2 step of a run is `τ₂ = door ∘ exit` ("rotate the first `k−1` letters, fix the
last").  A completed weight-2 run started at `u = a₁…aₘ b c` (`m = k−2`) has the `m+1 = k−1` entries

```
D_i = τ₂ⁱ(u) = rot_i(a₁…aₘ b) c,   0 ≤ i ≤ m,
```

which is `chartWord (A' := a₁…a_{m-1}) (z := aₘ) b c 0 i` of `ProofsClosure3`.  Its exit is
`e = c b a₁…aₘ`, and the six weight-3 successors of `e` are the `T1…T6` of `PROOF_S2 §3`.

All results are `sorry`-free and introduce no new axioms.
-/

namespace Hunter.ProofsRigidity2

open List Hunter

variable {k : ℕ}

/-! ## §0. Block exit, the `τ₂` step, and the run entries -/

/-- The block **exit** of a length-`k` block entry `u`: the right rotation `u.rotate (k−1)`. -/
def bexit (k : ℕ) (u : List ℕ) : List ℕ := u.rotate (k - 1)

/-- The **boundary weight** from block entry `u` to block entry `v`: `wt k (exit u) v`. -/
noncomputable def bwt (k : ℕ) (u v : List ℕ) : ℕ := wt k (bexit k u) v

/-- The fresh weight-2 run step `τ₂ = door ∘ exit` ("rotate the first `k−1` letters, fix the
last").  Repeated from a run start it enumerates the run entries. -/
def tau2 (k : ℕ) (w : List ℕ) : List ℕ := door (bexit k w)

/-- **The `τ₂` recurrence.**  If `|P| = k − 1`, then `τ₂` advances the rotation index of a word of
the form `P.rotate i ++ [x]` by one: `τ₂(rot_i P · x) = rot_{i+1} P · x`.  (`PROOF_S2 §1`.) -/
theorem tau2_step (hk : 2 ≤ k) {P : List ℕ} (hP : P.length = k - 1) (x : ℕ) (i : ℕ) :
    tau2 k (P.rotate i ++ [x]) = P.rotate (i + 1) ++ [x] := by
  have hWlen : (P.rotate i).length = k - 1 := by rw [List.length_rotate, hP]
  obtain ⟨w0, ws, hW⟩ : ∃ w0 ws, P.rotate i = w0 :: ws := by
    rcases hpr : P.rotate i with _ | ⟨w0, ws⟩
    · rw [hpr] at hWlen; simp at hWlen; omega
    · exact ⟨w0, ws, rfl⟩
  -- exit: rotate a length-k word right by 1 ⇒ move the last letter to the front
  have hbexit : bexit k (P.rotate i ++ [x]) = x :: (P.rotate i) := by
    unfold bexit
    rw [show k - 1 = (P.rotate i).length from hWlen.symm, List.rotate_append_length_eq]
    rfl
  -- door of `x :: w0 :: ws`
  rw [tau2, hbexit, hW]
  show door (x :: w0 :: ws) = P.rotate (i + 1) ++ [x]
  have hdoor : door (x :: w0 :: ws) = ws ++ [w0, x] := rfl
  rw [hdoor, ← List.rotate_rotate, hW]
  -- (w0 :: ws).rotate 1 = ws ++ [w0]
  have hr1 : (w0 :: ws).rotate 1 = ws ++ [w0] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  rw [hr1]; simp

/-- Iterating `τ₂` from a run start `P ++ [x]` (`|P| = k − 1`) gives the run entries. -/
theorem tau2_iter (hk : 2 ≤ k) {P : List ℕ} (hP : P.length = k - 1) (x : ℕ) (n : ℕ) :
    (tau2 k)^[n] (P ++ [x]) = P.rotate n ++ [x] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, tau2_step hk hP]

/-- The run entry `D_i` of the run started at `A ++ [b, c]` (`A = a₁…aₘ`), in closed form. -/
def runW (A : List ℕ) (b c : ℕ) (i : ℕ) : List ℕ := (A ++ [b]).rotate i ++ [c]

/-- `D_0 = A ++ [b, c]` is the run start. -/
theorem runW_zero (A : List ℕ) (b c : ℕ) : runW A b c 0 = A ++ [b, c] := by
  simp [runW]

/-- The run entries are the `τ₂`-iterates of the run start (`PROOF_S2 §1/§3`). -/
theorem runW_eq_iter (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) (b c : ℕ) (i : ℕ) :
    runW A b c i = (tau2 k)^[i] (A ++ [b, c]) := by
  have hP : (A ++ [b]).length = k - 1 := by rw [List.length_append]; simp; omega
  rw [runW, show A ++ [b, c] = (A ++ [b]) ++ [c] by simp, tau2_iter hk hP c i]

/-- The last run entry: `D_m = b :: A ++ [c]` (`m = k − 2 = |A|`). -/
theorem runW_last (A : List ℕ) (b c : ℕ) : runW A b c A.length = b :: A ++ [c] := by
  unfold runW
  rw [List.rotate_append_length_eq]
  simp

/-- The run exit `e = exit(D_m) = c :: b :: A` (`PROOF_S2 §3`). -/
theorem bexit_runW_last (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) (b c : ℕ) :
    bexit k (runW A b c A.length) = c :: b :: A := by
  rw [runW_last]
  unfold bexit
  rw [show k - 1 = (b :: A).length by simp; omega,
    show b :: A ++ [c] = (b :: A) ++ [c] from rfl, List.rotate_append_length_eq]
  rfl

/-! ## §1. Permutation-word transfer for run entries and the run exit -/

/-- Each run entry is a list-permutation of the run start `A ++ [b, c]`. -/
theorem runW_perm (A : List ℕ) (b c : ℕ) (i : ℕ) : runW A b c i ~ A ++ [b, c] := by
  have h1 : runW A b c i ~ (A ++ [b]) ++ [c] :=
    (List.perm_append_right_iff _).mpr (List.rotate_perm (A ++ [b]) i)
  simpa [List.append_assoc] using h1

/-- Run entries are permutation words when the run start is. -/
theorem isPermWord_runW {A : List ℕ} {b c : ℕ}
    (hu : IsPermWord k (A ++ [b, c])) (i : ℕ) : IsPermWord k (runW A b c i) :=
  hu.perm (runW_perm A b c i).symm

/-- The run exit is a permutation word when the run start is. -/
theorem isPermWord_bexit {w : List ℕ} (hw : IsPermWord k w) : IsPermWord k (bexit k w) :=
  isPermWord_rotate hw (k - 1)

/-! ## §2. The six weight-3 successors of a run exit and their collision identities

Run `A = a₁ :: As`, `k = |A| + 2 = |As| + 3`.  The run exit is `e = c :: b :: a₁ :: As`; its six
weight-3 successors are `Tj = As ++ [permutation of a₁, b, c]`.  We reuse
`ProofsClosure3.w3_six_cases` (with `A' := As`, `z := a₁`) for the enumeration and prove the six
collision identities of `PROOF_S2 §3` directly. -/

variable {As : List ℕ} {a₁ b c : ℕ}

/-- `T3 = runW A b c 1 = D₁`. -/
theorem T3_eq : runW (a₁ :: As) b c 1 = As ++ [b, a₁, c] := by
  rw [runW, show (a₁ :: As) ++ [b] = [a₁] ++ (As ++ [b]) by simp,
    show (1 : ℕ) = ([a₁] : List ℕ).length from rfl, List.rotate_append_length_eq]
  simp

/-- `T4 = σ(D₀) = (runW A b c 0).rotate 1`. -/
theorem T4_eq : (runW (a₁ :: As) b c 0).rotate 1 = As ++ [b, c, a₁] := by
  rw [runW_zero, show (a₁ :: As) ++ [b, c] = [a₁] ++ (As ++ [b, c]) by simp,
    show (1 : ℕ) = ([a₁] : List ℕ).length from rfl, List.rotate_append_length_eq]
  simp

/-- `T6 = σ²(D_m) = (runW A b c m).rotate 2`. -/
theorem T6_eq : (runW (a₁ :: As) b c (a₁ :: As).length).rotate 2 = As ++ [c, b, a₁] := by
  rw [runW_last, show b :: (a₁ :: As) ++ [c] = [b, a₁] ++ (As ++ [c]) by simp,
    show (2 : ℕ) = ([b, a₁] : List ℕ).length from rfl, List.rotate_append_length_eq]
  simp

/-- `T1 = τ₃(u) = runW (A.rotate 1) b c 0`, the next run's start. -/
theorem T1_eq : runW ((a₁ :: As).rotate 1) b c 0 = As ++ [a₁, b, c] := by
  rw [runW_zero, show (a₁ :: As).rotate 1 = As ++ [a₁] by
    rw [List.rotate_cons_succ, List.rotate_zero]]
  simp

/-- `τ₂^{m−1}(T2)` collides with the run: same class as `D₁ = runW A b c 1` (`PROOF_S2 §3`). -/
theorem T2_collide :
    rotClass ((tau2 (As.length + 3))^[As.length] (As ++ [a₁, c, b]))
      = rotClass (runW (a₁ :: As) b c 1) := by
  have hP : (As ++ [a₁, c]).length = (As.length + 3) - 1 := by simp
  rw [show As ++ [a₁, c, b] = (As ++ [a₁, c]) ++ [b] by simp,
    tau2_iter (by omega) hP b As.length,
    List.rotate_append_length_eq]
  have key : (runW (a₁ :: As) b c 1).rotate (As.length + 1) = [a₁, c] ++ As ++ [b] := by
    rw [T3_eq, show As ++ [b, a₁, c] = (As ++ [b]) ++ [a₁, c] by simp,
      show As.length + 1 = (As ++ [b]).length by simp, List.rotate_append_length_eq]
    simp
  rw [← key, ProofsClosure3.rotClass_rotate]

/-- `τ₂^{m−1}(T5)` collides with the run: same class as `D₀ = runW A b c 0` (`PROOF_S2 §3`). -/
theorem T5_collide :
    rotClass ((tau2 (As.length + 3))^[As.length] (As ++ [c, a₁, b]))
      = rotClass (runW (a₁ :: As) b c 0) := by
  have hP : (As ++ [c, a₁]).length = (As.length + 3) - 1 := by simp
  rw [show As ++ [c, a₁, b] = (As ++ [c, a₁]) ++ [b] by simp,
    tau2_iter (by omega) hP b As.length,
    List.rotate_append_length_eq]
  have key : (runW (a₁ :: As) b c 0).rotate (As.length + 2) = [c, a₁] ++ As ++ [b] := by
    rw [runW_zero, show (a₁ :: As) ++ [b, c] = (a₁ :: As ++ [b]) ++ [c] by simp,
      show As.length + 2 = (a₁ :: As ++ [b]).length by simp, List.rotate_append_length_eq]
    simp
  rw [← key, ProofsClosure3.rotClass_rotate]

/-! ## §2b. Weight-2 determinism and the `τ₂` period (the run cap, `PROOF_S2 §1`) -/

/-- **Weight-2 determinism.**  A fresh weight-2 successor of the block exit `exit u` (a weight-2
edge to a *different* rotation class) must be the `τ₂` step `door (exit u)`.  (`PROOF_S2 §1`: the
two weight-2 successors are `σ u` — same class — and `τ₂ u`.) -/
theorem fresh_w2_forced {u v : List ℕ} (hk : 2 ≤ k) (hu : IsPermWord k u) (hv : IsPermWord k v)
    (hw2 : bwt k u v = 2) (hfresh : rotClass v ≠ rotClass u) : v = tau2 k u := by
  have hx : IsPermWord k (bexit k u) := isPermWord_bexit hu
  have hover : (bexit k u).drop 2 = v.take (k - 2) := by
    have hspec := (wt_spec (u := bexit k u) (v := v) (by omega) (le_of_eq hx.length)).2.2
    rwa [show wt k (bexit k u) v = 2 from hw2] at hspec
  rcases ProofsConfinement.wt_two_word_cases hk hx hv hover with hrot | hdoor
  · exfalso; apply hfresh
    rw [hrot]
    show rotClass ((bexit k u).rotate 2) = rotClass u
    rw [bexit, List.rotate_rotate, ProofsClosure3.rotClass_rotate]
  · rw [hdoor]; rfl

/-- **The `τ₂` period.**  `τ₂^{k−1}` fixes any run start `A ++ [b, c]` with `|A| = k − 2`; hence a
maximal weight-2 run visits at most `k − 1` distinct blocks (`PROOF_S2 §1`). -/
theorem tau2_period (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) (b c : ℕ) :
    (tau2 k)^[k - 1] (A ++ [b, c]) = A ++ [b, c] := by
  have hP : (A ++ [b]).length = k - 1 := by rw [List.length_append]; simp; omega
  rw [show A ++ [b, c] = (A ++ [b]) ++ [c] by simp, tau2_iter hk hP c (k - 1),
    show k - 1 = (A ++ [b]).length from hP.symm, List.rotate_length]

/-! ## §2c. The counting pigeonhole (`PROOF_S2 §2`) -/

/-- **Zero-slack pigeonhole (run lengths).**  If `r ≤ m` maximal weight-2 runs, each of length at
most `n`, together contain `n · m` blocks, then there are exactly `m` runs and every run has the
full length `n`.  (`PROOF_S2 §2`, the `N = Σ Lᵢ ≤ r·n ≤ m·n = N` collapse.) -/
theorem runlen_pigeonhole {r m n : ℕ} (hn : 1 ≤ n) (hr : r ≤ m) (L : Fin r → ℕ)
    (hcap : ∀ i, L i ≤ n) (hsum : (∑ i, L i) = n * m) : r = m ∧ ∀ i, L i = n := by
  have hle : (∑ i, L i) ≤ r * n := by
    calc (∑ i : Fin r, L i) ≤ ∑ _i : Fin r, n := Finset.sum_le_sum (fun i _ => hcap i)
      _ = r * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hrm : r = m := by
    have h1 : n * m ≤ r * n := hsum ▸ hle
    have h2 : r * n ≤ m * n := Nat.mul_le_mul_right n hr
    nlinarith [Nat.mul_le_mul_right n hr]
  subst hrm
  refine ⟨rfl, ?_⟩
  have heq : (∑ i, L i) = ∑ _i : Fin r, n := by
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hcap i)).mp heq
  exact fun i => this i (Finset.mem_univ i)

/-- **Zero-slack pigeonhole (boundary weights).**  If `p` positive boundaries each contribute at
least `1` to the excess and together contribute exactly `p`, then every one contributes exactly `1`
— i.e. every weight-`≥3` boundary has weight exactly `3`.  (`PROOF_S2 §2`.) -/
theorem boundary_exact {p : ℕ} (w : Fin p → ℕ) (hge : ∀ i, 1 ≤ w i)
    (hsum : (∑ i, w i) = p) : ∀ i, w i = 1 := by
  have heq : (∑ i, w i) = ∑ _i : Fin p, 1 := by
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hge i)).mp heq.symm
  exact fun i => (this i (Finset.mem_univ i)).symm

/-! ## §3. The forced-step lemma: only `τ₃` survives -/

/-- The rotation classes visited by the completed run started at `A ++ [b, c]`. -/
def RunVisited (A : List ℕ) (b c : ℕ) (K : RotClass) : Prop :=
  ∃ i, i ≤ A.length ∧ K = rotClass (runW A b c i)

/-- **The forced step (`PROOF_S2 §3`).**  Let a completed weight-2 run start at `u = a₁ :: As ++
[b, c]` and end at the exit `e = c :: b :: a₁ :: As`.  A weight-3 successor `v` of `e` (sharing the
length-`(k−3)` overlap `As`) that is *fresh* (its class is not in the run) **and** whose `(m−1)`-th
`τ₂`-iterate is *also* fresh (would-be next-run block, not in the run) must be `τ₃(u) = runW
(A.rotate 1) b c 0` — the next run's start.  The other five successors are excluded: `T3, T4, T6`
are already in the run (fail freshness of `v`); `T2, T5` collide with the run at step `m−1` (fail
freshness of the iterate). -/
theorem forced_step
    (he : IsPermWord (As.length + 3) (c :: b :: a₁ :: As))
    {v : List ℕ} (hv : IsPermWord (As.length + 3) v)
    (hover : (c :: b :: a₁ :: As).drop 3 = v.take (As.length))
    (hvfresh : ¬ RunVisited (a₁ :: As) b c (rotClass v))
    (hlast : ¬ RunVisited (a₁ :: As) b c
        (rotClass ((tau2 (As.length + 3))^[As.length] v))) :
    v = runW ((a₁ :: As).rotate 1) b c 0 := by
  have hstart : (a₁ :: As).length = As.length + 1 := by simp
  have hcases := ProofsClosure3.w3_six_cases As a₁ b c he hv
    (by simpa [ProofsClosure3.finalExit] using hover)
  rcases hcases with h | h | h | h | h | h
  · -- T1: the surviving τ₃ move
    rw [h, T1_eq]
  · -- T2: excluded by the collision at step m−1
    exfalso; apply hlast
    rw [h, T2_collide]
    exact ⟨1, by rw [hstart]; omega, rfl⟩
  · -- T3 = D₁: not fresh
    exfalso; apply hvfresh
    exact ⟨1, by rw [hstart]; omega, by rw [h, ← T3_eq]⟩
  · -- T4 = σ(D₀): not fresh
    exfalso; apply hvfresh
    refine ⟨0, by omega, ?_⟩
    rw [h, ← T4_eq, ProofsClosure3.rotClass_rotate]
  · -- T5: excluded by the collision at step m−1
    exfalso; apply hlast
    rw [h, T5_collide]
    exact ⟨0, by omega, rfl⟩
  · -- T6 = σ²(D_m): not fresh
    exfalso; apply hvfresh
    refine ⟨(a₁ :: As).length, le_refl _, ?_⟩
    rw [h, ← T6_eq, ProofsClosure3.rotClass_rotate]

/-! ## §4. Assembling the runs (the induction of `PROOF_S2 §4`)

The two determinism engines — `fresh_w2_forced` (intra-run: a fresh weight-2 step is `τ₂`) and
`forced_step` (inter-run: the fresh full-run weight-3 continuation is `τ₃`) — assemble the whole
chart.  `run_forced` runs the intra-run determinism: once the run start and the (forced, by the
counting layer) weight-2 profile of the run are fixed, the whole run equals `D₀, …, D_m`. -/

/-- **Intra-run determinism (`PROOF_S2 §1/§4`).**  A block sequence `q` whose `0`-th entry is a run
start `A ++ [b, c]` (`|A| = k − 2`), whose consecutive entries have distinct rotation classes, and
whose first `m = |A|` boundaries all have weight `2`, is forced to be the run `q i = D_i = runW A b
c i` for `0 ≤ i ≤ m`.  (Iterated `fresh_w2_forced`.) -/
theorem run_forced (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) {b c : ℕ}
    {q : ℕ → List ℕ} (h0 : q 0 = A ++ [b, c])
    (hperm : ∀ i, IsPermWord k (q i))
    (hdist : ∀ i, i < A.length → rotClass (q (i + 1)) ≠ rotClass (q i))
    (hw2 : ∀ i, i < A.length → bwt k (q i) (q (i + 1)) = 2) :
    ∀ i, i ≤ A.length → q i = runW A b c i := by
  intro i
  induction i with
  | zero => intro _; rw [h0, runW_zero]
  | succ n ih =>
    intro hn
    have hnlt : n < A.length := by omega
    have hqn : q n = runW A b c n := ih (by omega)
    have hstep : q (n + 1) = tau2 k (q n) :=
      fresh_w2_forced hk (hperm n) (hperm (n + 1)) (hw2 n hnlt) (hdist n hnlt)
    rw [hstep, hqn, runW_eq_iter hk hA b c n,
      (Function.iterate_succ_apply' (tau2 k) n (A ++ [b, c])).symm,
      ← runW_eq_iter hk hA b c (n + 1)]

end Hunter.ProofsRigidity2

/-! ## Exports for `Hunter.Proved` (the §2 rigidity toolkit consumed by the endgame) -/

namespace Hunter.Proved

/-- `Hunter.Proved.RunVisited` — the rotation classes visited by a completed weight-2 run. -/
abbrev RunVisited := Hunter.ProofsRigidity2.RunVisited

/-- `Hunter.Proved.tau2_forced` — **weight-2 determinism** (`PROOF_S2 §1`): a fresh weight-2
successor of a block exit is the `τ₂` step. -/
theorem tau2_forced {k : ℕ} {u v : List ℕ} (hk : 2 ≤ k) (hu : IsPermWord k u)
    (hv : IsPermWord k v) (hw2 : Hunter.ProofsRigidity2.bwt k u v = 2)
    (hfresh : rotClass v ≠ rotClass u) : v = Hunter.ProofsRigidity2.tau2 k u :=
  Hunter.ProofsRigidity2.fresh_w2_forced hk hu hv hw2 hfresh

/-- `Hunter.Proved.tau3_forced` — **the forced step** (`PROOF_S2 §3`): the unique fresh full-run
weight-3 continuation of a completed run is `τ₃` (the next run's start). -/
theorem tau3_forced {As : List ℕ} {a₁ b c : ℕ}
    (he : IsPermWord (As.length + 3) (c :: b :: a₁ :: As))
    {v : List ℕ} (hv : IsPermWord (As.length + 3) v)
    (hover : (c :: b :: a₁ :: As).drop 3 = v.take As.length)
    (hvfresh : ¬ RunVisited (a₁ :: As) b c (rotClass v))
    (hlast : ¬ RunVisited (a₁ :: As) b c
        (rotClass ((Hunter.ProofsRigidity2.tau2 (As.length + 3))^[As.length] v))) :
    v = Hunter.ProofsRigidity2.runW ((a₁ :: As).rotate 1) b c 0 :=
  Hunter.ProofsRigidity2.forced_step he hv hover hvfresh hlast

/-- `Hunter.Proved.run_forced` — **intra-run determinism**: a run with fixed start and weight-2
profile is `D₀,…,D_m`. -/
theorem run_forced {k : ℕ} (hk : 2 ≤ k) {A : List ℕ} (hA : A.length = k - 2) {b c : ℕ}
    {q : ℕ → List ℕ} (h0 : q 0 = A ++ [b, c]) (hperm : ∀ i, IsPermWord k (q i))
    (hdist : ∀ i, i < A.length → rotClass (q (i + 1)) ≠ rotClass (q i))
    (hw2 : ∀ i, i < A.length → Hunter.ProofsRigidity2.bwt k (q i) (q (i + 1)) = 2) :
    ∀ i, i ≤ A.length → q i = Hunter.ProofsRigidity2.runW A b c i :=
  Hunter.ProofsRigidity2.run_forced hk hA h0 hperm hdist hw2

/-- `Hunter.Proved.runlen_pigeonhole` — **the counting collapse** (`PROOF_S2 §2`): `r ≤ m` runs of
length `≤ n` totalling `n·m` forces `m` full runs. -/
theorem runlen_pigeonhole {r m n : ℕ} (hn : 1 ≤ n) (hr : r ≤ m) (L : Fin r → ℕ)
    (hcap : ∀ i, L i ≤ n) (hsum : (∑ i, L i) = n * m) : r = m ∧ ∀ i, L i = n :=
  Hunter.ProofsRigidity2.runlen_pigeonhole hn hr L hcap hsum

end Hunter.Proved

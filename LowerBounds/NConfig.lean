import LowerBounds.SBridgePath
import PreimageChain.WeightTwo

/-!
# Standard configurations (the row-level model of the written model, section 4)

Vertices are permutation words (`Vtx k`), `ew` is the overlap weight, `sigma` the rotation,
`sigmaInv` its inverse and `tau2V v = tau (sigmaInv v)` the map `τ₂` (`x M m ↦ M x m`: rotate
the first `k - 1` letters, keep the marker).

* `NRow`: a row `(e, ℓ)`: the blocks entered at `e, τ₂ e, …, τ₂^(ℓ-1) e`.
* `NHanging`: a hanging component: a sequence of rows and the vertex `v_H` it is attached at.
* `NConfig`: a kernel (a sequence of rows) and a list of hanging components.
* `NConfig.Valid`: the conditions of the model: seams of weight at least 3, (R1) coverage,
  (R2) slot rule, the vertices of the attachments pairwise different ((V3) of the certificate),
  (R3) forest.
* `NConfig.cost`: rows + `Σ_seams (w - 3)` + `Σ_H (w₀ + w₁ - 4)`.  The defect of the paper is
  `cost - (k-2)!`.

The second half of the file is the passage from blocks to rows: a *line* is a list of block
entries, its cost is `1 + Σ_links (w - 2)` (`linkSum`), and `groupRows` cuts a line into its rows
(maximal runs of links of weight 2).  `groupRows_spec` says that this loses nothing.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-! ### The model -/

/-- A row `(e, ℓ)`: the blocks entered at `e, τ₂ e, …, τ₂^(ℓ-1) e`. -/
structure NRow (k : ℕ) where
  /-- the entry of the first block -/
  entry : Vtx k
  /-- the number of blocks -/
  len : ℕ

namespace NRow

/-- The block entries of a row, in order. -/
noncomputable def entries (r : NRow k) : List (Vtx k) :=
  (List.range r.len).map (fun i => tau2V^[i] r.entry)

/-- The exit of a row: the exit `σ⁻¹` of its last block. -/
noncomputable def exit (r : NRow k) : Vtx k := sigmaInv (tau2V^[r.len - 1] r.entry)

end NRow

/-- The block entries of a sequence of rows. -/
noncomputable def rowsEntries (rows : List (NRow k)) : List (Vtx k) := rows.flatMap NRow.entries

/-- The weights of the seams of a sequence of rows: from the exit of a row to the entry of the
next one. -/
noncomputable def seamWeights : List (NRow k) → List ℕ
  | [] => []
  | [_] => []
  | r :: r' :: rest => ew k r.exit r'.entry :: seamWeights (r' :: rest)

/-- Rows plus seam excess of a sequence of rows. -/
noncomputable def rowsCost (rows : List (NRow k)) : ℕ :=
  rows.length + ((seamWeights rows).map (fun w => w - 3)).sum

/-- A hanging component: its rows and the vertex `v_H` at which it is attached. -/
structure NHanging (k : ℕ) where
  /-- the rows, in order -/
  rows : List (NRow k)
  /-- the vertex `v_H` -/
  slot : Vtx k

namespace NHanging

/-- `w₀ = ew (head H) (σ v_H)`. -/
noncomputable def w0 (H : NHanging k) : ℕ :=
  match H.rows.getLast? with
  | some r => ew k r.exit (sigma H.slot)
  | none => 0

/-- `w₁ = ew v_H (tail H)`. -/
noncomputable def w1 (H : NHanging k) : ℕ :=
  match H.rows.head? with
  | some r => ew k H.slot r.entry
  | none => 0

/-- Rows, seam excess and attachment cost `w₀ + w₁ - 4` of a hanging component. -/
noncomputable def cost (H : NHanging k) : ℕ := rowsCost H.rows + (H.w0 + H.w1 - 4)

end NHanging

/-- A configuration: a kernel and hanging components. -/
structure NConfig (k : ℕ) where
  /-- the rows of the kernel, in order -/
  kernel : List (NRow k)
  /-- the hanging components -/
  hanging : List (NHanging k)

namespace NConfig

/-- All block entries of a configuration. -/
noncomputable def entries (c : NConfig k) : List (Vtx k) :=
  rowsEntries c.kernel ++ c.hanging.flatMap (fun H => rowsEntries H.rows)

/-- `rows + Σ_seams (w - 3) + Σ_H (w₀ + w₁ - 4)`; the defect is `cost - (k-2)!`. -/
noncomputable def cost (c : NConfig k) : ℕ :=
  rowsCost c.kernel + (c.hanging.map NHanging.cost).sum

/-- The component with rows `R` is a hanging component of `c` whose vertex `v_H` lies in a
block of the sequence of rows `R'`. -/
def HangsOn (c : NConfig k) (R R' : List (NRow k)) : Prop :=
  ∃ H ∈ c.hanging, H.rows = R ∧ ∃ e ∈ rowsEntries R', ((H.slot : Vtx k) : List ℕ) ~r (e : List ℕ)

/-- A standard configuration (the written model, section 4, "The row-level model"). -/
structure Valid (c : NConfig k) : Prop where
  kernel_ne : c.kernel ≠ []
  hanging_ne : ∀ H ∈ c.hanging, H.rows ≠ []
  kernel_len : ∀ r ∈ c.kernel, 1 ≤ r.len
  hanging_len : ∀ H ∈ c.hanging, ∀ r ∈ H.rows, 1 ≤ r.len
  /-- seams have weight at least 3 -/
  kernel_seams : ∀ w ∈ seamWeights c.kernel, 3 ≤ w
  hanging_seams : ∀ H ∈ c.hanging, ∀ w ∈ seamWeights H.rows, 3 ≤ w
  /-- (R1): the blocks are pairwise different rotation classes … -/
  distinct : c.entries.Pairwise (fun a b : Vtx k => ¬ ((a : List ℕ) ~r (b : List ℕ)))
  /-- … and every rotation class is a block -/
  cover : ∀ v : Vtx k, ∃ e ∈ c.entries, (v : List ℕ) ~r (e : List ℕ)
  /-- (R2): `v_H` is not the exit of its block -/
  slot : ∀ H ∈ c.hanging, sigma H.slot ∉ c.entries
  /-- (V3): different hanging components are attached at different vertices -/
  slots_nodup : (c.hanging.map NHanging.slot).Nodup
  w0_ge : ∀ H ∈ c.hanging, 2 ≤ H.w0
  w1_ge : ∀ H ∈ c.hanging, 2 ≤ H.w1
  /-- (R3): every hanging component reaches the kernel along "component that contains `v_H`" -/
  forest : ∀ H ∈ c.hanging, Relation.TransGen c.HangsOn H.rows c.kernel

end NConfig

/-! ### Lines of blocks and their rows -/

/-- `Σ (w - 2)` over the links of a line of block entries: the link from a block to the next
one is the edge from its exit to the next entry. -/
noncomputable def linkSum : List (Vtx k) → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (ew k (sigmaInv a) b - 2) + linkSum (b :: rest)

/-- The cost of a line of blocks: `1 + Σ_links (w - 2)`, which is rows plus seam excess. -/
noncomputable def lineCost (L : List (Vtx k)) : ℕ := 1 + linkSum L

/-- Put the block entered at `e` in front of a sequence of rows: it joins the first row if the
link has weight 2 and is a row of its own otherwise. -/
noncomputable def consRow (e : Vtx k) : List (NRow k) → List (NRow k)
  | [] => [⟨e, 1⟩]
  | r :: rs => if ew k (sigmaInv e) r.entry = 2 then ⟨e, r.len + 1⟩ :: rs else ⟨e, 1⟩ :: r :: rs

/-- The rows of a line of blocks. -/
noncomputable def groupRows : List (Vtx k) → List (NRow k)
  | [] => []
  | e :: rest => consRow e (groupRows rest)

/-- A link between two blocks of different classes: weight at least 2, and weight 2 only for
`τ₂`. -/
def GoodLink (k : ℕ) (a b : Vtx k) : Prop :=
  2 ≤ ew k (sigmaInv a) b ∧ (ew k (sigmaInv a) b = 2 → b = tau2V a)

theorem goodLink_of_not_isRotated (hk : 2 ≤ k) {a b : Vtx k}
    (h : ¬ ((a : List ℕ) ~r (b : List ℕ))) : GoodLink k a b := by
  have h1 := Hunter.ProofsExitless.ew_ge_one (by omega : 1 ≤ k) (sigmaInv a) b
  have hne : ew k (sigmaInv a) b ≠ 1 := by
    intro hone
    have hb : b = sigma (sigmaInv a) :=
      (Hunter.ProofsExitless.ew_eq_one_iff (by omega : 1 ≤ k)).mp hone
    rw [Hunter.ProofsStructure.sigma_sigmaInv] at hb
    exact h (hb ▸ List.IsRotated.refl _)
  refine ⟨by omega, fun h2 => ?_⟩
  rcases weight_two_successors hk h2 with hs | ht
  · exfalso
    apply h
    have hb : b = sigma a := by
      rw [hs]
      show sigma (sigma (sigmaInv a)) = sigma a
      rw [Hunter.ProofsStructure.sigma_sigmaInv]
    rw [hb]
    exact ⟨1, rfl⟩
  · exact ht

theorem NRow.entries_succ (e : Vtx k) (n : ℕ) :
    NRow.entries ⟨e, n + 1⟩ = e :: NRow.entries ⟨tau2V e, n⟩ := by
  unfold NRow.entries
  simp only
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem NRow.entries_one (e : Vtx k) : NRow.entries ⟨e, 1⟩ = [e] := rfl

theorem NRow.exit_one (e : Vtx k) : NRow.exit ⟨e, 1⟩ = sigmaInv e := rfl

theorem NRow.exit_succ (e : Vtx k) (n : ℕ) :
    NRow.exit ⟨e, n + 2⟩ = NRow.exit ⟨tau2V e, n + 1⟩ := by
  unfold NRow.exit
  simp only [Nat.add_sub_cancel]
  show sigmaInv (tau2V^[n + 1] e) = sigmaInv (tau2V^[n] (tau2V e))
  rw [Function.iterate_succ_apply]

theorem seamWeights_cons_congr {r r' : NRow k} (h : r.exit = r'.exit) (rs : List (NRow k)) :
    seamWeights (r :: rs) = seamWeights (r' :: rs) := by
  cases rs with
  | nil => rfl
  | cons s rs => simp only [seamWeights, h]

/-- What `groupRows` produces from a line `L`. -/
structure GroupInv (L : List (Vtx k)) (rows : List (NRow k)) : Prop where
  entries : rowsEntries rows = L
  len : ∀ r ∈ rows, 1 ≤ r.len
  seams : ∀ w ∈ seamWeights rows, 3 ≤ w
  cost : L ≠ [] → rowsCost rows = lineCost L
  head : rows.head?.map NRow.entry = L.head?
  last : rows.getLast?.map NRow.exit = L.getLast?.map sigmaInv

/-- **Blocks to rows.**  A line of blocks whose links are good (which holds whenever the blocks
are pairwise different classes) is cut by `groupRows` into rows with the same blocks, seams of
weight at least 3, and `rows + Σ_seams (w - 3) = 1 + Σ_links (w - 2)`. -/
theorem groupRows_spec : ∀ L : List (Vtx k), L.IsChain (GoodLink k) → GroupInv L (groupRows L)
  | [], _ => by
      refine ⟨rfl, ?_, ?_, fun h => absurd rfl h, rfl, rfl⟩
      · intro r hr
        simp [groupRows] at hr
      · intro w hw
        simp [groupRows, seamWeights] at hw
  | [e], _ => by
      refine ⟨rfl, ?_, ?_, fun _ => rfl, rfl, rfl⟩
      · intro r hr
        simp only [groupRows, consRow, List.mem_singleton] at hr
        rw [hr]
      · intro w hw
        simp [groupRows, consRow, seamWeights] at hw
  | e :: e' :: rest, hc => by
      rw [List.isChain_cons_cons] at hc
      obtain ⟨hlink, hc'⟩ := hc
      have ih := groupRows_spec (e' :: rest) hc'
      obtain ⟨rows, hrows⟩ : ∃ rows, rows = groupRows (e' :: rest) := ⟨_, rfl⟩
      have hg : groupRows (e :: e' :: rest) = consRow e rows := by
        rw [hrows]
        rfl
      rw [hg]
      rw [← hrows] at ih
      obtain ⟨ihE, ihL, ihS, ihC, ihH, ihT⟩ := ih
      -- the first row of `rows` starts at `e'`
      rcases rows with _ | ⟨r, rs⟩
      · simp [rowsEntries] at ihE
      obtain ⟨re, rl⟩ := r
      have hrl : 1 ≤ rl := ihL ⟨re, rl⟩ List.mem_cons_self
      obtain ⟨m, rfl⟩ : ∃ m, rl = m + 1 := ⟨rl - 1, by omega⟩
      have hre : re = e' := by
        have h := ihH
        simp only [List.head?_cons, Option.map_some] at h
        exact Option.some.inj h
      subst hre
      have ihC' := ihC (List.cons_ne_nil _ _)
      by_cases h2 : ew k (sigmaInv e) re = 2
      · -- the block joins the first row
        have hτ : re = tau2V e := hlink.2 h2
        have hcr : consRow e (⟨re, m + 1⟩ :: rs) = ⟨e, m + 2⟩ :: rs := by
          simp only [consRow, h2, if_true]
        rw [hcr]
        have hexit : NRow.exit ⟨e, m + 2⟩ = NRow.exit ⟨re, m + 1⟩ := by
          rw [NRow.exit_succ, hτ]
        have hseam : seamWeights ((⟨e, m + 2⟩ : NRow k) :: rs) =
            seamWeights ((⟨re, m + 1⟩ : NRow k) :: rs) := seamWeights_cons_congr hexit rs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h1 : rowsEntries ((⟨e, m + 2⟩ : NRow k) :: rs) =
              e :: rowsEntries ((⟨re, m + 1⟩ : NRow k) :: rs) := by
            unfold rowsEntries
            rw [List.flatMap_cons, List.flatMap_cons, NRow.entries_succ, ← hτ, List.cons_append]
          rw [h1, ihE]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · show 1 ≤ m + 2
            omega
          · exact ihL r (List.mem_cons_of_mem _ hr)
        · rw [hseam]
          exact ihS
        · intro _
          have hcost : rowsCost ((⟨e, m + 2⟩ : NRow k) :: rs) =
              rowsCost ((⟨re, m + 1⟩ : NRow k) :: rs) := by
            unfold rowsCost
            rw [hseam]
            rfl
          rw [hcost, ihC']
          unfold lineCost
          simp only [linkSum, h2]
          omega
        · rfl
        · rw [List.getLast?_cons_cons, ← ihT]
          cases rs with
          | nil =>
              simp only [List.getLast?_singleton, Option.map_some]
              rw [hexit]
          | cons s rs => simp only [List.getLast?_cons_cons]
      · -- the block is a row of its own
        have hcr : consRow e (⟨re, m + 1⟩ :: rs) = ⟨e, 1⟩ :: ⟨re, m + 1⟩ :: rs := by
          simp only [consRow, h2, if_false]
        rw [hcr]
        have h3 : 3 ≤ ew k (sigmaInv e) re := by
          have := hlink.1
          omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h1 : rowsEntries ((⟨e, 1⟩ : NRow k) :: ⟨re, m + 1⟩ :: rs) =
              e :: rowsEntries ((⟨re, m + 1⟩ : NRow k) :: rs) := by
            unfold rowsEntries
            rw [List.flatMap_cons, NRow.entries_one]
            rfl
          rw [h1, ihE]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact le_refl 1
          · exact ihL r hr
        · intro w hw
          simp only [seamWeights, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact h3
          · exact ihS w hw
        · intro _
          have hcost : rowsCost ((⟨e, 1⟩ : NRow k) :: ⟨re, m + 1⟩ :: rs) =
              rowsCost ((⟨re, m + 1⟩ : NRow k) :: rs) + 1 + (ew k (sigmaInv e) re - 3) := by
            unfold rowsCost
            simp only [seamWeights, List.length_cons, List.map_cons, List.sum_cons, NRow.exit_one]
            omega
          rw [hcost, ihC']
          unfold lineCost
          simp only [linkSum]
          omega
        · rfl
        · rw [List.getLast?_cons_cons, List.getLast?_cons_cons, ← ihT]

/-- The weights of the attachment of a hanging component whose rows come from a line. -/
theorem NHanging.w0_groupRows {L : List (Vtx k)} (hL : L.IsChain (GoodLink k)) {b : Vtx k}
    (hb : L.getLast? = some b) (v : Vtx k) :
    NHanging.w0 ⟨groupRows L, v⟩ = ew k (sigmaInv b) (sigma v) := by
  have h := (groupRows_spec L hL).last
  rw [hb] at h
  unfold NHanging.w0
  cases hr : (groupRows L).getLast? with
  | none => rw [hr] at h; simp at h
  | some r =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

theorem NHanging.w1_groupRows {L : List (Vtx k)} (hL : L.IsChain (GoodLink k)) {a : Vtx k}
    (ha : L.head? = some a) (v : Vtx k) :
    NHanging.w1 ⟨groupRows L, v⟩ = ew k v a := by
  have h := (groupRows_spec L hL).head
  rw [ha] at h
  unfold NHanging.w1
  cases hr : (groupRows L).head? with
  | none => rw [hr] at h; simp at h
  | some r =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

/-- The link sum of two lines put one after the other. -/
theorem linkSum_append : ∀ (A B : List (Vtx k)) (a b : Vtx k), A.getLast? = some a →
    B.head? = some b → linkSum (A ++ B) = linkSum A + (ew k (sigmaInv a) b - 2) + linkSum B
  | [], _, _, _, h, _ => by simp at h
  | [x], B, a, b, h, hb => by
      rcases B with _ | ⟨b', B'⟩
      · simp at hb
      · simp only [List.getLast?_singleton, Option.some.injEq] at h
        simp only [List.head?_cons, Option.some.injEq] at hb
        subst h
        subst hb
        simp only [List.cons_append, List.nil_append, linkSum]
        omega
  | x :: y :: A, B, a, b, h, hb => by
      rw [List.getLast?_cons_cons] at h
      have ih := linkSum_append (y :: A) B a b h hb
      have e1 : linkSum (x :: y :: A ++ B) =
          (ew k (sigmaInv x) y - 2) + linkSum (y :: A ++ B) := by
        simp only [List.cons_append, linkSum]
      rw [e1, ih]
      simp only [linkSum]
      omega

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.groupRows_spec
#print axioms SuperpermLowerBounds.linkSum_append

import LowerBounds.NPath
import Superperm.Bridge

/-!
# Theorems W and N of the written model: every Hamiltonian path gives a standard configuration

`k ≥ 5`.  For a Hamiltonian path `P` of weight `wt(P)`, with `D(P) = wt(P) + k - HPV(k)`:

* `stdConfig hk hP` is the standard configuration of Theorem N, built from the canonical
  certificate of `P` (the components of `F P`, joined along the junctions);
* `stdConfig_valid`: it is a valid standard configuration;
* `stdConfig_cost_le`: `HPV(k) + cost ≤ (k-2)! + wt(P) + k`, that is, its defect
  `cost - (k-2)!` is at most `D(P)`;
* `mem_stdConfig_entries`: its blocks are the blocks of the components of `F P`, with the same
  entries.

For the searches:

* `covers_length_gt_of_no_stdConfig`: if no valid standard configuration has defect at most `D`,
  every covering word has at least `HPV(k) + D + 1` letters.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain

variable {k : ℕ}

/-- The standard configuration of a Hamiltonian path (Theorem N). -/
noncomputable def stdConfig (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) : NConfig k :=
  (joinData hk hP).config

/-- **Theorem N, validity.** -/
theorem stdConfig_valid (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    (stdConfig hk hP).Valid :=
  (joinData hk hP).config_valid (by omega)

/-- **Theorem N, the defect**: `cost - (k-2)! ≤ wt(P) + k - HPV(k)`. -/
theorem stdConfig_cost_le (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    hpv k + (stdConfig hk hP).cost ≤ (k - 2).factorial + (P.wtP + k) := by
  have h1 := (joinData hk hP).config_cost_le (by omega)
  have h2 := sum_charge_le hk hP
  unfold stdConfig
  omega

/-- The blocks of the standard configuration are the blocks of the components of `F P`, with
the same entries. -/
theorem mem_stdConfig_entries (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) (e : Vtx k) :
    e ∈ (stdConfig hk hP).entries ↔
      ∃ (C : ActualComponent P) (j : ℕ), j < componentClassCount (actualComponentPath hP C) ∧
        e = blockEntry (actualComponentPath hP C) j := by
  unfold stdConfig
  rw [(joinData hk hP).config_entries (by omega), List.mem_flatMap]
  constructor
  · rintro ⟨C, _, he⟩
    obtain ⟨j, hj, hje⟩ := List.mem_map.mp he
    exact ⟨C, j, List.mem_range.mp hj, hje.symm⟩
  · rintro ⟨C, j, hj, rfl⟩
    exact ⟨C, (joinData hk hP).mem_allList C, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

/-- **Theorems W and N.**  Every Hamiltonian path gives a valid standard configuration whose
defect `cost - (k-2)!` is at most `D(P) = wt(P) + k - HPV(k)`. -/
theorem exists_stdConfig (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    ∃ c : NConfig k, c.Valid ∧ hpv k + c.cost ≤ (k - 2).factorial + (P.wtP + k) :=
  ⟨stdConfig hk hP, stdConfig_valid hk hP, stdConfig_cost_le hk hP⟩

/-- If no valid standard configuration has defect at most `D`, every Hamiltonian path has
weight at least `HPV(k) + D + 1 - k`. -/
theorem pathwise_of_no_stdConfig (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D)
    {P : HPath k} (hP : P.IsHamiltonian) : hpv k + D + 1 ≤ P.wtP + k := by
  obtain ⟨c, hv, hc⟩ := exists_stdConfig hk hP
  have h1 := h c hv
  omega

theorem ssuper_gt_of_no_stdConfig (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D) :
    hpv k + D + 1 ≤ Ssuper k :=
  ssuper_ge_of_pathwise (by omega) (fun _ hP => pathwise_of_no_stdConfig hk D h hP)

/-- **The lower direction, for the searches.**  If no valid standard configuration on `k`
symbols has defect at most `D` (cost at most `(k-2)! + D`), then every word over `Fin k` that
contains all permutations has at least `HPV(k) + D + 1` letters. -/
theorem covers_length_gt_of_no_stdConfig (hk : 5 ≤ k) (D : ℕ)
    (h : ∀ c : NConfig k, c.Valid → ¬ c.cost ≤ (k - 2).factorial + D) :
    ∀ w : List (Fin k), SuperpermutationBounds.Covers w → hpv k + D + 1 ≤ w.length :=
  (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (ssuper_gt_of_no_stdConfig hk D h)

/-- The same as an existence statement: a covering word of length `N` gives a valid standard
configuration of defect at most `N - HPV(k)`.  (The configuration is that of a Hamiltonian path
of least weight, not of the path of the word itself.) -/
theorem exists_stdConfig_of_covers (hk : 5 ≤ k) {w : List (Fin k)}
    (hw : SuperpermutationBounds.Covers w) :
    ∃ c : NConfig k, c.Valid ∧ hpv k + c.cost ≤ (k - 2).factorial + w.length := by
  have hk1 : 1 ≤ k := by omega
  have hset : {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty := by
    obtain ⟨P, hP⟩ := Hunter.ProofsSpine.exists_ham k
    exact ⟨P.wtP, P, hP, rfl⟩
  have hmin : L k ∈ {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m} := by
    unfold L
    exact Nat.sInf_mem hset
  obtain ⟨P, hP, hwt⟩ := hmin
  have hS : Ssuper k ≤ w.length :=
    (SuperpermBridge.hunter_le_ssuper_iff (by omega)).mp (le_refl _) w hw
  rw [← Hunter.bridge_Lstar_eq_Ssuper hk1] at hS
  change L k + k ≤ w.length at hS
  obtain ⟨c, hv, hc⟩ := exists_stdConfig hk hP
  exact ⟨c, hv, by omega⟩

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.stdConfig_valid
#print axioms SuperpermLowerBounds.stdConfig_cost_le
#print axioms SuperpermLowerBounds.exists_stdConfig
#print axioms SuperpermLowerBounds.covers_length_gt_of_no_stdConfig
#print axioms SuperpermLowerBounds.exists_stdConfig_of_covers

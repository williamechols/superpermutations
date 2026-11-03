import LowerBounds.PHanging

/-!
# No valid configuration of cost at most 134 on 7 symbols, from the finite statements
(the written proof, sections 5 and 7)

* `famC c`: the family of trails of a configuration; `famC_trailFam`, `famC_num` (Lemma FAM).
* `no_config_134`: given the caps `Caps` (F0–F5, FR) and the profile statements `Profiles` (FF),
  no valid `NConfig 7` has cost at most 134.  The proof is R1 (`family_le_49`: no excess of link
  costs), the bound on the number of trails (`family_le_44`), the component bounds
  (`Caps.rows_path` for the kernel, `hanging_item` for the hanging components) and the
  knapsack (`T5899.sum_le_HB`, `T5899.kern`).
* `covers_5899_of_caps`: every covering word on 7 symbols has at least 5,899 letters, from the
  finite statements.

No `native_decide`.
-/

namespace SuperpermLowerBounds

open Hunter PreimageChain T5899

variable {c : NConfig 7}

/-- The family of trails of a configuration. -/
noncomputable def famC (c : NConfig 7) : List (List (NRow 7)) :=
  cutRows c.kernel ++ c.hanging.flatMap famH

/-- The total excess of the link costs of a configuration. -/
noncomputable def epsC (c : NConfig 7) : ℕ := epsR c.kernel + (c.hanging.map epsH).sum

theorem nat_le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := ih h
        omega

/-- Lemma FAM, summed over a list of hanging components. -/
theorem hanging_sums (hv : c.Valid) : ∀ Hs : List (NHanging 7), (∀ H ∈ Hs, H ∈ c.hanging) →
    (∀ A ∈ Hs.flatMap famH, Trail 7 A) ∧
      (rowsEntries (Hs.flatMap famH).flatten).Subperm (Hs.flatMap fun H => rowsEntries H.rows) ∧
      (Hs.map vH).sum + 5 * (((Hs.map epsH).sum : ℕ) : ℤ) ≤ lE (prs (Hs.flatMap famH)) ∧
      lW (prs (Hs.flatMap famH)) + 6 * (Hs.map epsH).sum ≤ (Hs.map wH).sum
  | [], _ => by
      refine ⟨fun A hA => by simp at hA, ?_, ?_, ?_⟩
      · simp [rowsEntries]
      · simp [prs, lE]
      · simp [prs, lW]
  | H :: Hs, h => by
      obtain ⟨t1, s1, e1, w1⟩ := famH_spec hv (h H List.mem_cons_self)
      obtain ⟨t2, s2, e2, w2⟩ :=
        hanging_sums hv Hs (fun H' hH' => h H' (List.mem_cons_of_mem _ hH'))
      rw [List.flatMap_cons, List.flatMap_cons]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro A hA
        rcases List.mem_append.mp hA with h1 | h1
        · exact t1 A h1
        · exact t2 A h1
      · rw [List.flatten_append, rowsEntries_append]
        exact s1.append s2
      · rw [prs_append, lE_append, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          Nat.cast_add]
        linarith
      · rw [prs_append, lW_append, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
        omega

theorem famC_trailFam (hv : c.Valid) : TrailFam 7 (famC c) := by
  have hk := kernel_ok hv
  obtain ⟨t2, s2, _, _⟩ := hanging_sums hv c.hanging (fun H hH => hH)
  refine ⟨?_, ?_⟩
  · intro A hA
    unfold famC at hA
    rcases List.mem_append.mp hA with h1 | h1
    · exact hk.fam.trails A h1
    · exact t2 A h1
  · unfold famC
    rw [List.flatten_append, rowsEntries_append, hk.inv.flat]
    have hsub : (rowsEntries c.kernel ++ rowsEntries (c.hanging.flatMap famH).flatten).Subperm
        c.entries := by
      unfold NConfig.entries
      exact (List.Subperm.refl _).append s2
    obtain ⟨l, hl, hls⟩ := hsub
    exact pairwise_of_perm (hv.distinct.sublist hls) hl.symm

/-- **Lemma FAM.** -/
theorem famC_num (hv : c.Valid) :
    valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum + 5 * (epsC c : ℤ) ≤
        lE (prs (famC c)) + 5 ∧
      lW (prs (famC c)) + 6 * epsC c ≤ wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum + 6 := by
  have hk := kernel_ok hv
  obtain ⟨k1, k2⟩ := hk.seg_num 0
  simp only [Nat.add_zero] at k1 k2
  obtain ⟨_, _, e2, w2⟩ := hanging_sums hv c.hanging (fun H hH => hH)
  unfold famC epsC
  rw [prs_append, lE_append, lW_append]
  constructor
  · rw [Nat.cast_add]
    linarith
  · omega

/-- **No valid configuration of cost at most 134**, from the finite statements. -/
theorem no_config_134 (hC : Caps) (hF : Profiles) (c : NConfig 7) (hv : c.Valid) :
    ¬ c.cost ≤ 134 := by
  intro hc
  have hav := acc_value hv hc
  have haw := acc_weight hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  -- R1: no excess of link costs
  have heps : epsC c = 0 := by
    by_contra hne
    have h1 : 1 ≤ epsC c := by omega
    have hW : lW (prs (famC c)) ≤ 84 := by omega
    have hE := family_le_49 hC.chain hF hfam hW
    have h1' : (1 : ℤ) ≤ (epsC c : ℤ) := by exact_mod_cast h1
    linarith
  rw [heps] at n1 n2
  simp only [Nat.cast_zero, mul_zero, add_zero] at n1 n2
  -- at most 6 trails
  have hlen : (famC c).length ≤ 6 := by
    by_contra hne
    have hE := family_le_44 hC.chain hfam (by omega) (by omega)
    linarith
  have hk := kernel_ok hv
  have heK : epsR c.kernel = 0 := by
    unfold epsC at heps
    omega
  have heH : ∀ H ∈ c.hanging, epsH H = 0 := by
    intro H hH
    have h1 := nat_le_sum_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩ : epsH H ∈ c.hanging.map epsH)
    unfold epsC at heps
    omega
  have hposK := hk.pos
  have hlenC : (famC c).length =
      (cutRows c.kernel).length + (c.hanging.flatMap famH).length := by
    unfold famC
    rw [List.length_append]
  have hnH : ∀ H ∈ c.hanging, (famH H).length ≤ 5 := by
    intro H hH
    have hs : (famH H).Sublist (c.hanging.flatMap famH) := by
      rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩)
    have := hs.length_le
    omega
  have hwH : ∀ H ∈ c.hanging, wH H ≤ 84 := by
    intro H hH
    have h1 := nat_le_sum_of_mem (List.mem_map.mpr ⟨H, hH, rfl⟩ : wH H ∈ c.hanging.map wH)
    omega
  -- the hanging components: the knapsack
  have hitems : ∀ H ∈ c.hanging, vH H ≤ (hvf (wH H) : ℤ) :=
    fun H hH => hanging_item hC hv hH (heH H hH) (hnH H hH) (hwH H hH)
  have hsum := sum_le_HB vH wH c.hanging hitems (by omega)
  -- the kernel
  have hlinks : rX c.kernel + 1 = (cutRows c.kernel).length := by
    have := hk.eps_add
    omega
  have hchain := hk.inv.eq4 hlinks
  have hwK : rowsHoles 7 c.kernel + 6 * rX c.kernel + (c.hanging.map wH).sum ≤ 84 := haw
  have hcapK := hC.rows_path hk.fam hchain (s := (cutRows c.kernel).length - 1) (by omega)
    (by omega) (by rw [hk.inv.flat]; omega)
  rw [hk.inv.flat] at hcapK
  have hkern := kern ((cutRows c.kernel).length - 1) (by omega) (rowsHoles 7 c.kernel) (by omega)
    (by omega)
  have hmono := HB_mono ((c.hanging.map wH).sum) (by omega)
    (84 - rowsHoles 7 c.kernel - 6 * ((cutRows c.kernel).length - 1)) (by omega) (by omega)
  unfold valR at hav
  omega

/-- **Every covering word on 7 symbols has at least 5,899 letters**, from the finite
statements. -/
theorem covers_5899_of_caps (hC : Caps) (hF : Profiles) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length := by
  have e1 : (7 - 2).factorial + 14 = 134 := by decide
  have e2 : hpv 7 + 14 + 1 = 5899 := by decide
  have h := covers_length_gt_of_no_stdConfig (k := 7) (by norm_num) 14
    (by rw [e1]; exact no_config_134 hC hF)
  rw [e2] at h
  exact h

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.famC_trailFam
#print axioms SuperpermLowerBounds.famC_num
#print axioms SuperpermLowerBounds.no_config_134
#print axioms SuperpermLowerBounds.covers_5899_of_caps

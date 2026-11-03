import LowerBounds.PTheorem
import K5897.Arith

/-!
# No valid configuration of cost at most 132 on 7 symbols, from the chain caps

This is the argument of Halfar's `no_config_134` (`LowerBounds/PTheorem.lean`) at defect 12 in
place of 14. A configuration of cost at most `5! + 12 = 132` has values adding up to at least 60
and weights adding up to at most 72 (Lemma ACC, `acc_value_132`, `acc_weight_132`, the proofs of
`acc_value` and `acc_weight` with the new constants). Its family of trails (`famC`) then has
weight at most 78 and value at least 55 (Lemma FAM, `famC_num`), while the chain caps `T` and the
knapsack bound every such family by 54 (`lE_le_54`). So the finer analysis of `PTheorem.lean`
(sequences, rings, hanging items, profiles) is not needed at this defect.

* `no_config_132`: no valid `NConfig 7` has cost at most 132, given the caps `ChainCap Tf 72`.
* `covers_5897_of_cap`: every covering word on 7 symbols then has at least 5,897 letters.
-/

namespace SuperpermLowerBounds
namespace K5897

open Hunter PreimageChain T5899

/-- **Lemma ACC, values**, at cost 132. -/
theorem acc_value_132 {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 132) :
    60 ≤ valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  rw [valR_eq hlen.1, sum_vH c.hanging hlen.2]
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 132 := by
    exact_mod_cast (hC ▸ hc)
  linarith

/-- **Lemma ACC, weights**, at cost 132. -/
theorem acc_weight_132 {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 132) :
    wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum ≤ 72 := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  have h0 := wtR_eq hlen.1 (rX c.kernel)
  have h3 := sum_wH c.hanging hlen.2
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 132 := by
    exact_mod_cast (hC ▸ hc)
  have : ((wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum : ℕ) : ℤ) ≤ 72 := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast this

/-- The trails of a family of weight at most 78 obey the chain caps. -/
theorem pairs_ok_72 {M : ℕ → ℕ} (h0 : ChainCap M 72) {S : List (List (NRow 7))}
    (h : TrailFam 7 S) (hW : lW (prs S) ≤ 78) : ∀ p ∈ prs S, p.2 ≤ M p.1 := by
  have hx : ∀ p ∈ prs S, p.1 ≤ 72 := by
    intro p hp
    have := mem_le_lW hp
    omega
  intro p hp
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hp
  exact chain_cap_rows h0 (h.trails A hA) (h.classes.sublist (rowsEntries_sublist_flatten hA))
    (hx _ hp)

/-- **No valid configuration of cost at most 132**, from the chain caps. -/
theorem no_config_132 (h0 : ChainCap Tf 72) (c : NConfig 7) (hv : c.Valid) :
    ¬ c.cost ≤ 132 := by
  intro hc
  have hav := acc_value_132 hv hc
  have haw := acc_weight_132 hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  have hW : lW (prs (famC c)) ≤ 78 := by omega
  have hE := lE_le_54 (pairs_ok_72 h0 hfam hW) hW
  have he : (0 : ℤ) ≤ (epsC c : ℤ) := Int.natCast_nonneg _
  linarith

/-- **Every covering word on 7 symbols has at least 5,897 letters**, from the chain caps. -/
theorem covers_5897_of_cap (h0 : ChainCap Tf 72) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5897 ≤ w.length := by
  have e1 : (7 - 2).factorial + 12 = 132 := by decide
  have e2 : hpv 7 + 12 + 1 = 5897 := by decide
  have h := covers_length_gt_of_no_stdConfig (k := 7) (by norm_num) 12
    (by rw [e1]; exact no_config_132 h0)
  rw [e2] at h
  exact h

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.no_config_132
#print axioms SuperpermLowerBounds.K5897.covers_5897_of_cap

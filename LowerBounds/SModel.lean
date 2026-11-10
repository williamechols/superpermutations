import LowerBounds.SModelDef
import LowerBounds.SSound

/-!
# From the search on numbers to `ModelStatement`

`modelStatement_of_search`: if `S.search k A q2 C1 C2 bn fuel = false` (with
`A = q (k - 3) - cn`, `q2 = 2 q`, `C1 = 2 q (k - 4)`, `C2 = 2 q (k - 3)`) and
`S.runSearch k = false`, then every model chain on `k` symbols (`5 ≤ k ≤ 15`) whose list of
deficits is a window satisfies the window bound with `c = cn / q`, `b = bn / q`.

The proof is `S.wstatement_of_search` (`SSound.lean`), applied to the words of the vertices.
-/

namespace SuperpermLowerBounds

open Hunter

/-- The word of a vertex is a permutation word in the sense of `SWord.lean`. -/
theorem permW_of_vtx {k : ℕ} (v : Vtx k) : S.PermW k (v : List ℕ) := by
  have h := v.2
  refine ⟨h.1, h.length, fun a => ?_⟩
  rw [← List.mem_toFinset, h.2, Finset.mem_Icc]

/-- A model chain, read as a chain of words. -/
theorem isWChain_of_modelChain {k : ℕ} {L : List (List (Vtx k))} (h : IsModelChain k L) :
    S.IsWChain k (L.map (List.map Subtype.val)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP w hw
    obtain ⟨P0, _, rfl⟩ := List.mem_map.mp hP
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    exact permW_of_vtx v
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    exact fun e => h.pieces_ne P0 hP0 (List.map_eq_nil_iff.mp e)
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    rw [List.length_map]
    exact h.size_le P0 hP0
  · intro P hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
    rw [List.isChain_map]
    exact h.doors P0 hP0
  · rw [List.isChain_map]
    refine h.seams.imp ?_
    intro P Q hPQ hP hQ
    have hP0 : P ≠ [] := fun e => hP (by rw [e]; rfl)
    have hQ0 : Q ≠ [] := fun e => hQ (by rw [e]; rfl)
    rw [List.getLast_map, List.head_map]
    exact hPQ hP0 hQ0
  · rw [← List.map_flatten, List.pairwise_map]
    exact h.classes

theorem modelDeficits_eq {k : ℕ} (L : List (List (Vtx k))) :
    modelDeficits k L = S.wdef k (L.map (List.map Subtype.val)) := by
  simp [modelDeficits, S.wdef, List.map_map, Function.comp_def]

/-- The statement for chains of words gives the statement for model chains. -/
theorem modelStatement_of_wstatement {k cn bn q : ℕ} (h : S.WStatement k cn bn q) :
    ModelStatement k cn bn q := by
  intro L hL hwin
  rw [modelDeficits_eq] at hwin ⊢
  exact h _ (isWChain_of_modelChain hL) hwin

/-- The search on numbers proves the statement for model chains. -/
theorem modelStatement_of_search {k cn bn q A q2 C1 C2 fuel : ℕ} (hk : 5 ≤ k) (hk15 : k ≤ 15)
    (hc : cn ≤ q * (k - 5)) (hA : A = q * (k - 3) - cn) (hq2 : q2 = 2 * q)
    (hC1 : C1 = 2 * q * (k - 4)) (hC2 : C2 = 2 * q * (k - 3))
    (hrun : S.runSearch k = false) (hs : S.search k A q2 C1 C2 bn fuel = false) :
    ModelStatement k cn bn q :=
  modelStatement_of_wstatement (S.wstatement_of_search hk hk15 hc hA hq2 hC1 hC2 hrun hs)

end SuperpermLowerBounds

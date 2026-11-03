import LowerBounds.PArith
import K5897.Caps

/-!
# The arithmetic for 5,897

A family of chains on 7 symbols, each with `rows ≤ T holes`, of weight `Σ (holes + 6) ≤ 78` has
value `Σ (rows - holes - 5) ≤ 54`. The closed statements about the tables are proved by
`decide +kernel`; `lE_le_Bc` is the induction of Halfar's `T5899.lE_le_B` with the new tables.
-/

namespace SuperpermLowerBounds
namespace K5897

open T5899

/-- Chain cap. -/
def Tf (x : ℕ) : ℕ := Tcap.getD x 0

/-- The knapsack certificate. -/
def Bc (W : ℕ) : ℕ := Bcert.getD W 0

theorem Bc_closure : ∀ x < 73, ∀ W < 73, W + x + 6 ≤ 78 →
    Tf x + Bc W ≤ Bc (W + x + 6) + x + 5 := by decide +kernel

theorem Bc_mono : ∀ a < 79, ∀ b < 79, a ≤ b → Bc a ≤ Bc b := by decide +kernel

theorem Bc_top : Bc 78 = 54 := by decide +kernel

/-- Every pair has `rows ≤ T holes`. -/
def lOKc (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, p.2 ≤ Tf p.1

theorem lE_le_Bc : ∀ l : List (ℕ × ℕ), lOKc l → lW l ≤ 78 → lE l ≤ (Bc (lW l) : ℤ)
  | [], _, _ => by
      rw [lE_nil]
      exact Int.natCast_nonneg _
  | p :: l, hok, hW => by
      rw [lW_cons] at hW
      have ih := lE_le_Bc l (fun q hq => hok q (List.mem_cons_of_mem _ hq)) (by omega)
      have hp := hok p List.mem_cons_self
      have hc := Bc_closure p.1 (by omega) (lW l) (by omega) (by omega)
      have e : lW l + p.1 + 6 = p.1 + 6 + lW l := by omega
      rw [e] at hc
      rw [lW_cons, lE_cons]
      omega

/-- **The family bound.** A family of pairs with `rows ≤ T holes` and weight at most 78 has value
at most 54. -/
theorem lE_le_54 {l : List (ℕ × ℕ)} (hok : lOKc l) (hW : lW l ≤ 78) : lE l ≤ 54 := by
  have h1 := lE_le_Bc l hok hW
  have h2 := Bc_mono (lW l) (by omega) 78 (by omega) hW
  rw [Bc_top] at h2
  omega

end K5897
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5897.lE_le_54

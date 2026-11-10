import Hunter.ProofsHeadline
import PreimageChain.PathwisePivotCore

/-!
# Pointwise Bound-2 regrouping for an actual image
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- The actual Bound-1 value attached to the Hunter image of a path. -/
noncomputable def actualBaselineCore {k : ℕ} (P : HPath k) : ℕ :=
  (numComps (F P) - 1) + MinThrough (F P) + wEdges (F P)

/-- Real cast of the actual Bound-1 value. -/
theorem actualBaselineCore_cast
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualBaselineCore P : ℝ) =
      (numComps (F P) : ℝ) - 1 + (MinThrough (F P) : ℝ) +
        (wEdges (F P) : ℝ) := by
  have hnc : 1 ≤ numComps (F P) :=
    Hunter.ProofsWP.one_le_numComps_F hP hk
  unfold actualBaselineCore
  push_cast [Nat.cast_sub hnc]
  ring

/-- Fixed-image Bound 1 dominates the global concrete `gInner` expression at `R_k`. -/
theorem actualBaselineCore_ge_Rk_gInner
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (actualBaselineCore P : ℝ) ≥
      Rk k * (k.factorial : ℝ) + Hunter.ProofsGB2.gInner k (Rk k) := by
  let X := F P
  have hX : X ∈ Xk k := ⟨P, hP, rfl⟩
  have hlocal := Hunter.Proved.prp_gives_b2_amended hk hX
  let localSet : Set ℝ := {q : ℝ | ∃ p, IsPathComponent p X ∧
    q = (p.wtP : ℝ) - Rk k * (p.numVerts : ℝ)}
  have hlocalNonempty : localSet.Nonempty :=
    Hunter.ProofsB2.innerSet_nonempty hk hX
  have hglobal_le_local : Hunter.ProofsGB2.gInner k (Rk k) ≤ sInf localSet := by
    rw [Hunter.ProofsGB2.gInner]
    apply le_csInf hlocalNonempty
    rintro q ⟨p, hpc, rfl⟩
    exact csInf_le (Hunter.ProofsGB2.innerSet_bddBelow k (Rk k))
      ⟨p, ⟨X, hX, hpc⟩, rfl⟩
  rw [actualBaselineCore_cast hP hk]
  change _ ≥ Rk k * (k.factorial : ℝ) + sInf localSet at hlocal
  linarith

end PreimageChain

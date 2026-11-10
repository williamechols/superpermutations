import PreimageChain.ComponentEndpointRigidity

/-!
# 实际 Hunter 分量的本原块稳定性

无条件组件端点容量、最小入权二的首端刚性以及末端门户指标共同给出正文
本原块稳定性与仿射形式。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 实际组件容量的整数版本。 -/
theorem actual_component_capacity_int
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) :
    let g := actualComponentGeometry hP C
    let p := actualComponentPath hP C
    let hp := actualComponentPath_stronglyExitless hP (by omega) C
    2 * g.r ≤ ((k : ℤ) - 2) *
      (g.Delta + 2 * g.x +
        (componentFirstFullBit p (by omega) hp : ℤ) +
          (componentLastFullBit p (by omega) hp : ℤ)) := by
  dsimp
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless :=
    actualComponentPath_stronglyExitless hP (by omega) C
  have hcap := actual_component_capacity hk hp
  have hcap' :
      (2 : ℤ) * (componentPieceCount p : ℤ) ≤
        ((k - 2 : ℕ) : ℤ) *
          ((componentPieceDeficit p : ℤ) +
            2 * (componentSeamResidual p : ℤ) +
              (componentFirstFullBit p (by omega) hp : ℤ) +
                (componentLastFullBit p (by omega) hp : ℤ)) := by
    exact_mod_cast hcap
  rw [Nat.cast_sub (by omega : 2 ≤ k)] at hcap'
  simpa [actualComponentGeometry, componentGeometry, p] using hcap'

/-- 正文稳定性证明所用的精确缺陷恒等式。 -/
theorem actual_component_stability_identity
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) :
    let g := actualComponentGeometry hP C
    2 * g.defect - ((k : ℤ) - 2) * g.m =
      (D (k : ℤ) - 1) * (g.x + g.mu - 2) +
        ((k : ℤ) - 2) * g.Delta - 2 * g.r := by
  dsimp
  have hdef := actual_component_defect_geometry hP (by omega : 4 ≤ k) C
  have hm := (actualComponentGeometry_defectEquations hP C).2
  rw [hdef, hm]
  simp only [D]
  ring

/-- 首满指标为零时，首片缺口严格为正。 -/
theorem componentPieceDeficit_pos_of_firstFullBit_zero
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hfirst : componentFirstFullBit p (by omega) hp = 0) :
    1 ≤ componentPieceDeficit p := by
  obtain ⟨first, rest, hpieces⟩ :=
    List.exists_cons_of_ne_nil (componentIntervalPieces_ne_nil (by omega) hp)
  have hfirstPos : 1 ≤ first.deficit := by
    unfold componentFirstFullBit firstNatValue at hfirst
    rw [hpieces] at hfirst
    have hne : first.deficit ≠ 0 := by
      intro hzero
      simp [actualPieceFullBit, hzero] at hfirst
    exact Nat.one_le_iff_ne_zero.mpr hne
  have htotal := componentIntervalPieces_totalDeficit (by omega : 4 ≤ k) hp
  unfold pieceListTotalDeficit at htotal
  rw [hpieces] at htotal
  simp only [List.map_cons, List.sum_cons] at htotal
  omega

/-- 实际组件正规形中的 `m` 至少为其零一门户指标。 -/
theorem actual_component_m_ge_portal
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hnonspanning : C.1 ≠ Finset.univ) :
    (actualPortalBit hP C : ℤ) ≤ (actualComponentGeometry hP C).m := by
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless :=
    actualComponentPath_stronglyExitless hP (by omega) C
  have hmuNat := actual_component_minto_ge_two hP (by omega : 2 ≤ k) C hnonspanning
  have hmuPath : p.minto = compMinto (F P) C.1 :=
    actualComponentPath_minto hP C
  have hm := (actualComponentGeometry_defectEquations hP C).2
  have hx : 0 ≤ (actualComponentGeometry hP C).x := by
    dsimp [actualComponentGeometry, componentGeometry, p]
    positivity
  have hDelta : 0 ≤ (actualComponentGeometry hP C).Delta := by
    dsimp [actualComponentGeometry, componentGeometry, p]
    positivity
  by_cases hportal : actualPortalBit hP C = 1
  · have hterminal := actualPortalBit_one_implies_terminalPortal hk hP C hportal
    have hfirstNat := componentFirstFullBit_eq_zero_of_minto_two hk hp (by
      rw [actualComponentPath_vertsFinset hP C]
      exact hnonspanning) (by
        rw [hmuPath]
        exact hterminal.1)
    have hDeltaPosNat := componentPieceDeficit_pos_of_firstFullBit_zero hk hp hfirstNat
    have hDeltaPos : 1 ≤ (actualComponentGeometry hP C).Delta := by
      dsimp [actualComponentGeometry, componentGeometry, p]
      exact_mod_cast hDeltaPosNat
    rw [hportal]
    norm_num
    rw [hm]
    have hmuEq : (actualComponentGeometry hP C).mu = 2 := by
      dsimp [actualComponentGeometry, componentGeometry, p]
      rw [hmuPath]
      exact_mod_cast hterminal.1
    rw [hmuEq]
    nlinarith
  · have hportalZero : actualPortalBit hP C = 0 := by
      have hle := actualPortalBit_le_one hP C
      omega
    rw [hportalZero]
    norm_num
    rw [hm]
    have hmuEq : (actualComponentGeometry hP C).mu =
        (compMinto (F P) C.1 : ℤ) := by
      dsimp [actualComponentGeometry, componentGeometry, p]
      rw [hmuPath]
    have hmuInt : 2 ≤ (actualComponentGeometry hP C).mu := by
      rw [hmuEq]
      exact_mod_cast hmuNat
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (k : ℤ) - 1 by omega)
      (show 0 ≤ (actualComponentGeometry hP C).x +
        (actualComponentGeometry hP C).mu - 2 by linarith)]

/-- 非满实际组件满足本原块稳定性。 -/
theorem actual_component_block_stability
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hnonspanning : C.1 ≠ Finset.univ) :
    let g := actualComponentGeometry hP C
    ((k : ℤ) - 2) * (g.m - (actualPortalBit hP C : ℤ)) ≤
      2 * g.defect := by
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless :=
    actualComponentPath_stronglyExitless hP (by omega) C
  let g := actualComponentGeometry hP C
  let a := componentFirstFullBit p (by omega) hp
  let b := componentLastFullBit p (by omega) hp
  have hcapacity : 2 * g.r ≤ ((k : ℤ) - 2) *
      (g.Delta + 2 * g.x + (a : ℤ) + (b : ℤ)) := by
    simpa [g, p, a, b] using actual_component_capacity_int hk hP C
  have hidentity := actual_component_stability_identity hk hP C
  dsimp at hidentity
  have hx : 0 ≤ g.x := by
    dsimp [g, actualComponentGeometry, componentGeometry, p]
    positivity
  have hmuNat := actual_component_minto_ge_two hP (by omega : 2 ≤ k) C hnonspanning
  have hmuEq : g.mu = (compMinto (F P) C.1 : ℤ) := by
    dsimp [g, actualComponentGeometry, componentGeometry, p]
    rw [actualComponentPath_minto hP C]
  by_cases hmu2 : compMinto (F P) C.1 = 2
  · have hmuPath : p.minto = 2 := by
      rw [actualComponentPath_minto hP C]
      exact hmu2
    have haNat : a = 0 := by
      dsimp [a]
      apply componentFirstFullBit_eq_zero_of_minto_two hk hp
      · rw [actualComponentPath_vertsFinset hP C]
        exact hnonspanning
      · exact hmuPath
    have hbNat : b = actualPortalBit hP C := by
      unfold actualPortalBit
      rw [dif_pos (by omega : 2 ≤ k)]
      by_cases hb1 : b = 1
      · simp [hmu2, hb1, b, p]
      · have hble : b ≤ 1 := by
          dsimp [b]
          exact componentLastFullBit_le_one p (by omega) hp
        have hb0 : b = 0 := by omega
        simp [hmu2, hb0, b, p]
    have hidTwo :
        2 * g.defect - ((k : ℤ) - 2) * g.m =
          (D (k : ℤ) - 1) * g.x +
            ((k : ℤ) - 2) * g.Delta - 2 * g.r := by
      rw [hmuEq, hmu2] at hidentity
      simpa using hidentity
    apply block_stability_mu_two
      (k := (k : ℤ)) (d := g.defect) (m := g.m) (x := g.x)
      (Delta := g.Delta) (r := g.r) (a := (a : ℤ))
      (b := (b : ℤ)) (pi := (actualPortalBit hP C : ℤ))
    · exact_mod_cast hk
    · exact hx
    · exact hidTwo
    · exact hcapacity
    · exact_mod_cast haNat
    · exact_mod_cast hbNat
  · have hmu3Nat : 3 ≤ compMinto (F P) C.1 := by omega
    have hmu3 : 3 ≤ g.mu := by
      rw [hmuEq]
      exact_mod_cast hmu3Nat
    have habNat : a + b ≤ 2 := by
      have ha := componentFirstFullBit_le_one p (by omega) hp
      have hb := componentLastFullBit_le_one p (by omega) hp
      dsimp [a, b]
      omega
    have hpiNat : actualPortalBit hP C = 0 := by
      unfold actualPortalBit
      rw [dif_pos (by omega : 2 ≤ k)]
      simp [hmu2]
    apply block_stability_mu_ge_three
      (k := (k : ℤ)) (d := g.defect) (m := g.m) (x := g.x)
      (mu := g.mu) (Delta := g.Delta) (r := g.r)
      (a := (a : ℤ)) (b := (b : ℤ))
      (pi := (actualPortalBit hP C : ℤ))
    · exact_mod_cast hk
    · exact hx
    · exact hmu3
    · exact hidentity
    · exact hcapacity
    · exact_mod_cast habNat
    · exact_mod_cast hpiNat

/-- 非满实际组件的费率缺陷非负。 -/
theorem actual_component_defect_nonneg
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hnonspanning : C.1 ≠ Finset.univ) :
    0 ≤ (actualComponentGeometry hP C).defect := by
  have hstable := actual_component_block_stability hk hP C hnonspanning
  have hm := actual_component_m_ge_portal hk hP C hnonspanning
  have hk2 : 0 ≤ (k : ℤ) - 2 := by omega
  have hlhs : 0 ≤ ((k : ℤ) - 2) *
      ((actualComponentGeometry hP C).m - (actualPortalBit hP C : ℤ)) :=
    mul_nonneg hk2 (sub_nonneg.mpr hm)
  linarith

/-- 非满实际组件满足正文仿射本原块不等式。 -/
theorem actual_component_block_affine
    (hk : 5 ≤ k) {P : HPath k} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hnonspanning : C.1 ≠ Finset.univ) :
    let g := actualComponentGeometry hP C
    ((k : ℤ) - 2) * g.t ≤
      ((k : ℤ) - 2) * D (k : ℤ) * (actualPortalBit hP C : ℤ) +
        (D (k : ℤ) - 1) * g.defect := by
  dsimp
  apply block_affine_of_stability (k := (k : ℤ))
  · exact_mod_cast hk
  · exact actual_component_t_normal_form hP (by omega : 4 ≤ k) C
  · exact actual_component_block_stability hk hP C hnonspanning

end PreimageChain

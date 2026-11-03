import Hunter.Statements
import Hunter.ProofsConfinement
import Hunter.ProofsStructure
import PreimageChain.Numerics

/-!
# 权二后继、约化路径与零成本门户

本模块直接复用固定 Hunter–Raudvere 基线的排列字和重叠权定义，形式化正文引理 3.1
以及引理 8.3 中由 `σ²` 约化性强迫两个 proper-door 选择的部分。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 双旋转后继。 -/
def sigma2 (v : Vtx k) : Vtx k := sigma (sigma v)

/-- 路径不含任何 `u → σ²u` 边。 -/
def Sigma2Reduced (P : HPath k) : Prop :=
  ∀ u : Vtx k, (u, sigma2 u) ∉ P.edges

/-- `σ⁻¹ ∘ σ = id`。上游已有另一个方向 `σ ∘ σ⁻¹ = id`。 -/
theorem sigmaInv_sigma (hk : 1 ≤ k) (v : Vtx k) : sigmaInv (sigma v) = v := by
  apply Subtype.ext
  change ((v.1.rotate 1).rotate (k - 1)) = v.1
  rw [List.rotate_rotate]
  have hsum : 1 + (k - 1) = k := by omega
  rw [hsum]
  have hlen := v.2.length
  simpa [hlen] using List.rotate_length v.1

/-- 正文引理 3.1 的“仅有两个后继”方向。 -/
theorem weight_two_successors (hk : 2 ≤ k) {u v : Vtx k}
    (hweight : ew k u v = 2) : v = sigma2 u ∨ v = tau u := by
  have hover : u.1.drop 2 = v.1.take (k - 2) := by
    have hs := wt_spec (u := u.1) (v := v.1) (by omega) (le_of_eq u.2.length)
    change wt k u.1 v.1 = 2 at hweight
    rw [hweight] at hs
    exact hs.2.2
  rcases Hunter.ProofsConfinement.wt_two_word_cases hk u.2 v.2 hover with hrot | hdoor
  · left
    apply Subtype.ext
    rw [hrot]
    change u.1.rotate 2 = (u.1.rotate 1).rotate 1
    rw [List.rotate_rotate]
  · right
    apply Subtype.ext
    rw [Hunter.tau_val_of_door (door_isPermWord hk u.2)]
    exact hdoor

/-- 双旋转边的权重恰为二。 -/
theorem weight_sigma2 (hk : 3 ≤ k) (u : Vtx k) : ew k u (sigma2 u) = 2 := by
  have hle : ew k u (sigma2 u) ≤ 2 := by
    have htri := Hunter.ImpRed.ew_triangle (show 1 ≤ k by omega)
      u (sigma u) (sigma2 u)
    change ew k u (sigma (sigma u)) ≤ 2
    change ew k u (sigma (sigma u)) ≤
      ew k u (sigma u) + ew k (sigma u) (sigma (sigma u)) at htri
    rw [Hunter.ew_sigma (by omega), Hunter.ew_sigma (by omega)] at htri
    exact htri
  have hpos : 1 ≤ ew k u (sigma2 u) := by
    rw [ew]
    exact (wt_spec (by omega) (le_of_eq u.2.length)).1
  have hne : ew k u (sigma2 u) ≠ 1 := by
    intro hone
    have heq : sigma2 u = sigma u :=
      (Hunter.ProofsExitless.ew_eq_one_iff (show 1 ≤ k by omega)).mp hone
    have hfixed : sigma u = u := Hunter.ProofsSpine.sigma_inj heq
    have hinj := Hunter.ProofsExitless.sigma_iter_inj u
      (a := 1) (b := 0) (by omega) (by omega)
    have hiter : (sigma^[1]) u = (sigma^[0]) u := by
      simpa using hfixed
    have hab : (1 : ℕ) = 0 := hinj hiter
    omega
  omega

/-- 正文引理 3.2 的已验证局部手术：删除指定 `u → σ²u` 边且不增权。 -/
theorem sigma2_surgery
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hedge : (u, sigma2 u) ∈ P.edges) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧
      (u, sigma2 u) ∉ P'.edges ∧ P'.wtP ≤ P.wtP := by
  have htri : ew k u (sigma2 u) =
      ew k u (sigma u) + ew k (sigma u) (sigma2 u) := by
    rw [weight_sigma2 hk, Hunter.ew_sigma (by omega), sigma2,
      Hunter.ew_sigma (by omega)]
  exact Hunter.imp_reduced hP htri hedge

/-- 终端门户坐标 `Ψ(h)=τ(σ⁻¹(τh))`。 -/
noncomputable def psi (h : Vtx k) : Vtx k := tau (sigmaInv (tau h))

/-- 约化零成本链的两个权二边都被强迫为 proper door。 -/
theorem reduced_zero_cost_dichotomy
    (hk : 2 ≤ k) {P : HPath k} (hred : Sigma2Reduced P)
    {head slot target : Vtx k}
    (hentryEdge : (head, sigma slot) ∈ P.edges)
    (hentryWeight : ew k head (sigma slot) = 2)
    (htargetEdge : (slot, target) ∈ P.edges)
    (htargetWeight : ew k slot target = 2) :
    slot = sigmaInv (tau head) ∧ target = psi head := by
  have hslot : slot = sigmaInv (tau head) := by
    rcases weight_two_successors hk hentryWeight with hdouble | hdoor
    · exfalso
      apply hred head
      rw [← hdouble]
      exact hentryEdge
    · have h := congrArg sigmaInv hdoor
      rw [sigmaInv_sigma (by omega)] at h
      exact h
  have htarget : target = tau slot := by
    rcases weight_two_successors hk htargetWeight with hdouble | hdoor
    · exfalso
      apply hred slot
      rw [← hdouble]
      exact htargetEdge
    · exact hdoor
  refine ⟨hslot, ?_⟩
  rw [htarget, psi, hslot]

/-- 路径中的旋转边数量，作为约化手术的严格进度量。 -/
noncomputable def rotationEdgeCount (P : HPath k) : ℕ :=
  (P.edges.filter fun e => e.2 = sigma e.1).card

theorem rotationEdgeCount_le_edges (P : HPath k) :
    rotationEdgeCount P ≤ P.edges.card :=
  Finset.card_filter_le _ _

/-- 有界严格进度关系必然到达正规形；这是正文定理 3.3 的终止论证本身。 -/
theorem normal_form_of_bounded_progress
    {α : Type*} (cost measure : α → ℕ) (Normal : α → Prop) (bound : ℕ)
    (hbound : ∀ x, measure x ≤ bound)
    (hstep : ∀ x, ¬Normal x → ∃ y, cost y ≤ cost x ∧ measure x + 1 ≤ measure y)
    (x : α) :
    ∃ y, Normal y ∧ cost y ≤ cost x := by
  classical
  induction hrem : bound - measure x using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hx : Normal x
      · exact ⟨x, hx, le_rfl⟩
      · obtain ⟨y, hcost, hprogress⟩ := hstep x hx
        have hmx := hbound x
        have hmy := hbound y
        have hlt : bound - measure y < bound - measure x := by omega
        have hlt' : bound - measure y < n := by simpa [hrem] using hlt
        obtain ⟨z, hz, hzy⟩ := ih (bound - measure y) hlt' y rfl
        exact ⟨z, hz, le_trans hzy hcost⟩

/-- 若每个非约化 Hamilton 路径都有论文手术所给的严格旋转边进度，则存在不增权约化路径。 -/
theorem sigma2_reduced_normal_form_of_surgery
    {P : HPath k} (hP : P.IsHamiltonian) (bound : ℕ)
    (hbound : ∀ Q : HPath k, Q.IsHamiltonian → rotationEdgeCount Q ≤ bound)
    (hsurgery : ∀ Q : HPath k, Q.IsHamiltonian → ¬Sigma2Reduced Q →
      ∃ Q' : HPath k, Q'.IsHamiltonian ∧ Q'.wtP ≤ Q.wtP ∧
        rotationEdgeCount Q + 1 ≤ rotationEdgeCount Q') :
    ∃ P' : HPath k, P'.IsHamiltonian ∧ Sigma2Reduced P' ∧ P'.wtP ≤ P.wtP := by
  let State := {Q : HPath k // Q.IsHamiltonian}
  let cost : State → ℕ := fun Q => Q.1.wtP
  let measure : State → ℕ := fun Q => rotationEdgeCount Q.1
  let Normal : State → Prop := fun Q => Sigma2Reduced Q.1
  have hb : ∀ Q : State, measure Q ≤ bound := fun Q => hbound Q.1 Q.2
  have hs : ∀ Q : State, ¬Normal Q →
      ∃ Q', cost Q' ≤ cost Q ∧ measure Q + 1 ≤ measure Q' := by
    intro Q hQ
    obtain ⟨Q', hQ', hw, hm⟩ := hsurgery Q.1 Q.2 hQ
    exact ⟨⟨Q', hQ'⟩, hw, hm⟩
  obtain ⟨Q, hnormal, hcost⟩ :=
    normal_form_of_bounded_progress cost measure Normal bound hb hs ⟨P, hP⟩
  exact ⟨Q.1, Q.2, hnormal, hcost⟩

end PreimageChain

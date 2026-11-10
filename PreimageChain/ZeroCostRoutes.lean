import PreimageChain.PortalAssignment

/-!
# 约化路径中的零成本真实链

本模块把槽位成本桥接回正文的零成本二分引理：实际链成本为零时，内部路线
只能有一个槽位；若非终端目标组件的最小进入权为二，则两个边权都被强迫为二，
从而可应用 `σ²` 约化下的 proper-door 坐标结论。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 无重复实际路线的内部成本为零时，路线只能由其起点一个槽位组成。 -/
theorem actualChainRoute_eq_singleton_of_internalCost_zero
    {P : HPath k} (hk : 1 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hzero : slotInternalCost (actualChainSlotSequence s) = 0) :
    actualChainRoute s = [s.1] := by
  cases hroute : actualChainRoute s with
  | nil =>
      exact False.elim ((actualChainRoute_ne_nil s) hroute)
  | cons a l =>
      cases l with
      | nil =>
          have ha : a = s.1 := by
            simpa [hroute] using actualChainRoute_head s
          simp [ha]
      | cons b l =>
          exfalso
          unfold slotInternalCost actualChainSlotSequence at hzero
          change (((actualChainRoute s).zip (actualChainRoute s).tail).map
            (fun d => ew k d.1 (sigma d.2) - 1)).sum = 0 at hzero
          rw [hroute] at hzero
          simp only [List.tail_cons, List.zip_cons_cons, List.map_cons,
            List.sum_cons] at hzero
          have hterm : ew k a (sigma b) - 1 = 0 := by omega
          have hpos : 1 ≤ ew k a (sigma b) := by
            rw [ew]
            exact (wt_spec hk (le_of_eq a.2.length)).1
          have hone : ew k a (sigma b) = 1 := by omega
          have hsigma : sigma b = sigma a :=
            (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
          have hab : b = a := Hunter.ProofsSpine.sigma_inj hsigma
          have hnodup := actualChainRoute_nodup s
          rw [hroute, List.nodup_cons] at hnodup
          exact hnodup.1 (by simp [hab])

/-- 真实完整链成本为零时，其内部槽位成本也为零。 -/
theorem actualChainInternalCost_zero_of_routeNatCost_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hzero : actualChainRouteNatCost hP hk s = 0) :
    slotInternalCost (actualChainSlotSequence s) = 0 := by
  unfold actualChainRouteNatCost at hzero
  by_cases hsEnd : actualChainRouteEnd s = P.last
  · rw [dif_pos hsEnd] at hzero
    unfold slotRouteStarCost at hzero
    omega
  · rw [dif_neg hsEnd] at hzero
    dsimp only at hzero
    unfold slotRouteCost slotRouteStarCost at hzero
    omega

/-- 真实完整链成本为零时，路线是单槽位路线。 -/
theorem actualChainRoute_eq_singleton_of_routeNatCost_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hzero : actualChainRouteNatCost hP hk s = 0) :
    actualChainRoute s = [s.1] :=
  actualChainRoute_eq_singleton_of_internalCost_zero (by omega) s
    (actualChainInternalCost_zero_of_routeNatCost_zero hP hk s hzero)

theorem actualChainRouteEnd_eq_start_of_routeNatCost_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hzero : actualChainRouteNatCost hP hk s = 0) :
    actualChainRouteEnd s = s.1 := by
  have hmem := actualChainRouteEnd_mem_route s
  rw [actualChainRoute_eq_singleton_of_routeNatCost_zero hP hk s hzero,
    List.mem_singleton] at hmem
  exact hmem

/--
正文约化零成本二分引理在实际预像链上的形式：若非终端目标组件满足 `μ=2`，
则唯一槽位和目标尾分别被强迫为 `σ⁻¹(τh)` 与 `Ψ(h)`。
-/
theorem actual_reduced_zero_cost_dichotomy
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hsEnd : actualChainRouteEnd s ≠ P.last)
    (hzero : actualChainRouteNatCost hP hk s = 0)
    (hmu : compMinto (F P)
      (actualNonterminalTargetComponent hP hk
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2) :
    s.1 = sigmaInv (tau (chainSourceHead hP s).1) ∧
      (chainTargetTail hP
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 =
        psi (chainSourceHead hP s).1 := by
  let e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
    ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩
  have hcost := hzero
  unfold actualChainRouteNatCost at hcost
  rw [dif_neg hsEnd] at hcost
  dsimp only at hcost
  unfold slotRouteCost slotRouteStarCost at hcost
  rw [actualChainSourceComponent_head hP hk s,
    actualChainSlotSequence_first, actualChainSlotSequence_last,
    actualNonterminalTargetComponent_tail hP hk e] at hcost
  rw [hmu] at hcost
  change compMinto (F P)
      (Hunter.ProofsWP.block (F P) (chainTargetTail hP e).1) = 2 at hmu
  have hentryLower : 2 ≤ ew k (chainSourceHead hP s).1 (sigma s.1) := by
    exact_mod_cast (sub_nonneg.mp (chainEntry_excess_nonneg hP hk s))
  have hexitLower : compMinto (F P)
      (Hunter.ProofsWP.block (F P) (chainTargetTail hP e).1) ≤
      ew k (actualChainRouteEnd s) (chainTargetTail hP e).1 := by
    exact_mod_cast (sub_nonneg.mp (chainExit_excess_nonneg hP hk e))
  have hentryWeight : ew k (chainSourceHead hP s).1 (sigma s.1) = 2 := by
    omega
  have hexitWeight : ew k (actualChainRouteEnd s) (chainTargetTail hP e).1 = 2 := by
    omega
  have hend := actualChainRouteEnd_eq_start_of_routeNatCost_zero hP hk s hzero
  have hentryEdge : ((chainSourceHead hP s).1, sigma s.1) ∈ P.edges :=
    E2removed_subset P (Sset P) (chainSourceHead_spec hP s)
  have hexitEdge : (s.1, (chainTargetTail hP e).1) ∈ P.edges := by
    have h := E1removed_subset P (Sset P) (chainTargetTail_spec hP e)
    change (actualChainRouteEnd s, (chainTargetTail hP e).1) ∈ P.edges at h
    rw [hend] at h
    exact h
  have hexitWeight' : ew k s.1 (chainTargetTail hP e).1 = 2 := by
    change ew k (actualChainRouteEnd s) (chainTargetTail hP e).1 = 2 at hexitWeight
    rwa [hend] at hexitWeight
  exact reduced_zero_cost_dichotomy hk hred hentryEdge hentryWeight
    hexitEdge hexitWeight'

end PreimageChain

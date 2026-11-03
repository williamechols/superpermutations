import PreimageChain.ComponentPaths

/-!
# 终端满片访问证书与刚性门户

正文 terminal-full rigidity 实际只使用最后满片提供的一个坐标事实：`Ψ(h_C)`
在组件路径首点之后已经出现。本模块把该事实记录为可核查证书，并证明它排除
`t_C = Ψ(h_C)`；再与真实零成本链二分及组件不交性合并，得到刚性终端门户。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 最后满片所需交付的坐标访问证书：`Ψ(h_C)` 已在组件首点之后出现。 -/
def TerminalFullVisitCertificate
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : Prop :=
  psi (actualComponentHead hP C) ∈ (actualComponentPath hP C).verts.tail

theorem terminalFullVisit_mem_component
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hcert : TerminalFullVisitCertificate hP C) :
    psi (actualComponentHead hP C) ∈ C.1 := by
  rw [← actualComponentPath_vertsFinset hP C, HPath.mem_vertsFinset]
  exact List.mem_of_mem_tail hcert

/-- 正文 terminal-full rigidity：访问证书排除 `t_C = Ψ(h_C)`。 -/
theorem terminal_full_visit_rigidity
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hcert : TerminalFullVisitCertificate hP C) :
    actualComponentTail hP C ≠ psi (actualComponentHead hP C) := by
  intro heq
  let p := actualComponentPath hP C
  have hfirstPsi : p.first = psi (actualComponentHead hP C) := by
    change (actualComponentPath hP C).first = _
    rw [actualComponentPath_first hP C, heq]
  have hfirstTail : p.first ∈ p.verts.tail := by
    rw [hfirstPsi]
    exact hcert
  obtain ⟨a, l, hverts⟩ := List.exists_cons_of_ne_nil p.ne
  have hfirstA : p.first = a := by
    change p.verts.head p.ne = a
    simp [hverts]
  have hnodup := p.nodup
  rw [hverts, List.nodup_cons] at hnodup
  apply hnodup.1
  rw [hfirstA] at hfirstTail
  simpa [hverts] using hfirstTail

/--
真实刚性终端门户：带终端满片访问证书的源组件，不能通过零成本链进入任何
最小进入权为二的组件；自嵌套情形由同一个证明自动排除。
-/
theorem actual_terminal_full_portal_positive
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hred : Sigma2Reduced P)
    (s : {v : Vtx k // v ∈ chainStarts P})
    (hsEnd : actualChainRouteEnd s ≠ P.last)
    (hcert : TerminalFullVisitCertificate hP
      (actualChainSourceComponent hP hk s))
    (hmu : compMinto (F P)
      (actualNonterminalTargetComponent hP hk
        ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩).1 = 2) :
    1 ≤ actualChainRouteNatCost hP hk s := by
  by_contra hnot
  have hzero : actualChainRouteNatCost hP hk s = 0 := by omega
  let B := actualChainSourceComponent hP hk s
  let e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
    ⟨actualChainRouteEnd s, actualChainRouteEnd_mem_chainEnds s, hsEnd⟩
  let A := actualNonterminalTargetComponent hP hk e
  have hdich := actual_reduced_zero_cost_dichotomy hP hk hred s hsEnd hzero hmu
  rw [← actualChainSourceComponent_head hP hk s] at hdich
  have hpsiB : psi (actualComponentHead hP B) ∈ B.1 :=
    terminalFullVisit_mem_component hP B hcert
  have hpsiA : psi (actualComponentHead hP B) ∈ A.1 := by
    have htail := actualComponentTail_mem_component hP A
    rw [actualNonterminalTargetComponent_tail hP hk e, hdich.2] at htail
    exact htail
  have hBA : B = A := by
    apply Subtype.ext
    exact (Hunter.ProofsWP.comp_eq_block_of_mem B.2 hpsiB).trans
      ((Hunter.ProofsWP.comp_eq_block_of_mem A.2 hpsiA).symm)
  have hrigid := terminal_full_visit_rigidity hP B hcert
  apply hrigid
  calc
    actualComponentTail hP B = actualComponentTail hP A := by rw [hBA]
    _ = (chainTargetTail hP e).1 :=
      actualNonterminalTargetComponent_tail hP hk e
    _ = psi (actualComponentHead hP B) := hdich.2

end PreimageChain

import PreimageChain.ZeroCostRoutes

/-!
# 实际 Hunter 组件的有序路径表示

每个 `F(P)` 弱组件已知是唯一方向上的简单路径。本模块为每个实际组件选择
一个 `HPath` 表示，并把它的首尾、强 exitless 性质及最小进入权接回组件接口。
这是构造正文区间片与终端满片证书的有序基础。
-/

namespace PreimageChain

open Hunter
open scoped Classical

variable {k : ℕ}

/-- 一个实际 `F(P)` 组件的有序简单路径表示。 -/
noncomputable def actualComponentPath
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) : HPath k :=
  Classical.choose (Hunter.lem_pathrule hP C.1 C.2)

theorem actualComponentPath_vertsFinset
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (actualComponentPath hP C).vertsFinset = C.1 :=
  (Classical.choose_spec (Hunter.lem_pathrule hP C.1 C.2)).1

theorem actualComponentPath_isPathComponent
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    IsPathComponent (actualComponentPath hP C) (F P) :=
  (Classical.choose_spec (Hunter.lem_pathrule hP C.1 C.2)).2

/-- 组件路径的末点就是组件的唯一有向头。 -/
theorem actualComponentPath_last
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (actualComponentPath hP C).last = actualComponentHead hP C := by
  have hpath := Hunter.ProofsWP.compHeads_eq
    (actualComponentPath_isPathComponent hP C)
  rw [actualComponentPath_vertsFinset hP C,
    actualComponentHead_spec hP C] at hpath
  exact Finset.singleton_injective hpath.symm

/-- 组件路径的首点就是组件的唯一有向尾。 -/
theorem actualComponentPath_first
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (actualComponentPath hP C).first = actualComponentTail hP C := by
  have hpath := Hunter.ProofsSpine.compTails_eq
    (actualComponentPath_isPathComponent hP C)
  rw [actualComponentPath_vertsFinset hP C,
    actualComponentTail_spec hP C] at hpath
  exact Finset.singleton_injective hpath.symm

/-- 每个实际组件路径都是 strongly exitless。 -/
theorem actualComponentPath_stronglyExitless
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) :
    (actualComponentPath hP C).StronglyExitless :=
  Hunter.ProofsB2.stronglyExitless_of_isPathComponent hP hk
    (actualComponentPath_isPathComponent hP C)

/-- 组件接口的 `compMinto` 等于所选组件路径的 `minto`。 -/
theorem actualComponentPath_minto
    {P : HPath k} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    (actualComponentPath hP C).minto = compMinto (F P) C.1 := by
  rw [← actualComponentPath_vertsFinset hP C]
  exact (Hunter.Proved.bridge_compMinto_eq_minto
    (actualComponentPath_isPathComponent hP C)).symm

end PreimageChain

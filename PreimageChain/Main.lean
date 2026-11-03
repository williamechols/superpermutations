import Hunter.Pointwise
import PreimageChain.ChainGraph

/-!
# 全局下界的最终桥接接口

本模块把论文的逐 Hamilton 路径分层修正与真正的最短超排列长度 `Ssuper` 连接。
该接口使剩余结构义务完全显式：一旦对每条 Hamilton 路径证明 `PathwiseNewBound`，
取最小值及词/图等价不再需要任何额外假设。
-/

namespace PreimageChain

open Hunter
open scoped Classical

/-- 论文全局分层论证最终需要交付的逐路径陈述。 -/
def PathwiseNewBound (k : ℕ) (hk : 5 ≤ k) : Prop :=
  ∀ P : HPath k, P.IsHamiltonian →
    Numerics.hunterBound k + Numerics.gamma k hk ≤ P.wtP + k

/-- 从逐路径修正取 Hamilton 路径最小值，并经 `Lstar=Ssuper` 得到全局结论。 -/
theorem superperm_bound_of_pathwise
    {k : ℕ} (hk : 5 ≤ k) (hpath : PathwiseNewBound k hk) :
    Numerics.hunterBound k + Numerics.gamma k hk ≤ Ssuper k := by
  have hham : ∃ P : HPath k, P.IsHamiltonian :=
    Hunter.ProofsSpine.exists_ham k
  have hset :
      {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty := by
    obtain ⟨P, hP⟩ := hham
    exact ⟨P.wtP, P, hP, rfl⟩
  have hmin : L k ∈ {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m} := by
    unfold L
    exact Nat.sInf_mem hset
  obtain ⟨P, hP, hwt⟩ := hmin
  rw [← Hunter.bridge_Lstar_eq_Ssuper (show 1 ≤ k by omega)]
  change Numerics.hunterBound k + Numerics.gamma k hk ≤ L k + k
  have hp := hpath P hP
  simpa [hwt] using hp

end PreimageChain

import PreimageChain.ComponentPortalChains
import PreimageChain.PortalCapacity

/-!
# 实际精确权三链的容量统计接口

本模块把实际片链的缺口列表分类为满片、单位缺口片和至少二缺口片，并将局部几何
最终需要提供的三个游程不等式封装为证书。证书一旦生成，正文整数版
`endpoint_matching_capacity` 可自动应用并返回自然数容量界。
-/

namespace PreimageChain

open Hunter

variable {k : ℕ}

/-- 缺口列表中的零缺口（满片）数量。 -/
def deficitFullCount : List ℕ → ℕ
  | [] => 0
  | d :: ds => (if d = 0 then 1 else 0) + deficitFullCount ds

/-- 缺口列表中的单位缺口片数量。 -/
def deficitUnitCount : List ℕ → ℕ
  | [] => 0
  | d :: ds => (if d = 1 then 1 else 0) + deficitUnitCount ds

/-- 缺口列表中的至少二缺口片数量。 -/
def deficitLargeCount : List ℕ → ℕ
  | [] => 0
  | d :: ds => (if 2 ≤ d then 1 else 0) + deficitLargeCount ds

/-- 零、单位和至少二三类缺口精确分割整个列表。 -/
theorem deficitCounts_partition (ds : List ℕ) :
    deficitFullCount ds + deficitUnitCount ds + deficitLargeCount ds =
      ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      by_cases hd0 : d = 0
      · simp [deficitFullCount, deficitUnitCount, deficitLargeCount, hd0]
        omega
      · by_cases hd1 : d = 1
        · simp [deficitFullCount, deficitUnitCount, deficitLargeCount,
            hd1]
          omega
        · have hd2 : 2 ≤ d := by omega
          simp [deficitFullCount, deficitUnitCount, deficitLargeCount,
            hd0, hd1, hd2]
          omega

/-- 单位缺口计一次、至少二缺口计两次仍不超过总缺口。 -/
theorem deficitUnit_add_two_large_le_sum (ds : List ℕ) :
    deficitUnitCount ds + 2 * deficitLargeCount ds ≤ ds.sum := by
  induction ds with
  | nil => simp [deficitUnitCount, deficitLargeCount]
  | cons d ds ih =>
      by_cases hd0 : d = 0
      · simp [deficitUnitCount, deficitLargeCount, hd0, ih]
      · by_cases hd1 : d = 1
        · simp [deficitUnitCount, deficitLargeCount, hd1]
          omega
        · have hd2 : 2 ≤ d := by omega
          simp only [deficitUnitCount, deficitLargeCount, hd1, hd2,
            if_false, if_pos, List.sum_cons]
          omega

/-- 精确权三链的逐片缺口列表。 -/
def exactChainDeficits {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : List ℕ :=
  chain.pieces.map ComponentIntervalPiece.deficit

/-- 精确权三链的片数 `r`。 -/
def exactChainPieceCount {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  chain.pieces.length

/-- 精确权三链的总缺口 `Δ`。 -/
def exactChainTotalDeficit {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  (exactChainDeficits chain).sum

/-- 精确权三链中的满片数 `F`。 -/
def exactChainFullCount {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  deficitFullCount (exactChainDeficits chain)

/-- 精确权三链中的单位缺口片数 `n₁`。 -/
def exactChainUnitCount {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  deficitUnitCount (exactChainDeficits chain)

/-- 精确权三链中的至少二缺口片数 `n₂`。 -/
def exactChainLargeCount {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  deficitLargeCount (exactChainDeficits chain)

/-- 每条链的片数精确分为满片、单位缺口片和至少二缺口片。 -/
theorem exactChain_pieceCount_eq_full_add_partial {p : HPath k}
    (chain : ExactWeightThreePieceChain p) :
    exactChainPieceCount chain = exactChainFullCount chain +
      (exactChainUnitCount chain + exactChainLargeCount chain) := by
  have hpartition := deficitCounts_partition (exactChainDeficits chain)
  change chain.pieces.length = deficitFullCount (exactChainDeficits chain) +
    (deficitUnitCount (exactChainDeficits chain) +
      deficitLargeCount (exactChainDeficits chain))
  have hlength : (exactChainDeficits chain).length = chain.pieces.length := by
    simp [exactChainDeficits]
  omega

/-- 链的单位/大缺口计数受真实总缺口控制。 -/
theorem exactChain_unit_add_two_large_le_totalDeficit {p : HPath k}
    (chain : ExactWeightThreePieceChain p) :
    exactChainUnitCount chain + 2 * exactChainLargeCount chain ≤
      exactChainTotalDeficit chain := by
  exact deficitUnit_add_two_large_le_sum (exactChainDeficits chain)

/-- 部分片数量不超过总缺口，故自然数 excess `Δ-p` 无截断。 -/
theorem exactChain_partialCount_le_totalDeficit {p : HPath k}
    (chain : ExactWeightThreePieceChain p) :
    exactChainUnitCount chain + exactChainLargeCount chain ≤
      exactChainTotalDeficit chain := by
  have h := exactChain_unit_add_two_large_le_totalDeficit chain
  omega

/--
四项局部几何汇总后需要生成的游程证书。`fullRunCount=R`，
`longInternalRunCount=N`，`endpointFullCount=e`；三个字段分别对应正文证明中的
单位缺口单侧性、满游程长度总计和长内部游程 excess 消耗。
-/
structure ExactWeightThreeChainRunCertificate {p : HPath k}
    (chain : ExactWeightThreePieceChain p) where
  fullRunCount : ℕ
  longInternalRunCount : ℕ
  endpointFullCount : ℕ
  oneSided :
    2 * fullRunCount ≤ exactChainUnitCount chain +
      2 * exactChainLargeCount chain + endpointFullCount
  fullBound :
    exactChainFullCount chain ≤
      (k - 4) * fullRunCount + endpointFullCount + longInternalRunCount
  longBound :
    (k - 3) * longInternalRunCount ≤
      2 * (exactChainTotalDeficit chain -
        (exactChainUnitCount chain + exactChainLargeCount chain))

/--
一旦实际链生成游程证书，整数版 `endpoint_matching_capacity` 自动给出自然数版
`2r ≤ (k-2)(Δ+e)`。
-/
theorem exactWeightThreeChain_capacity_of_runCertificate
    (hk : 5 ≤ k) {p : HPath k} (chain : ExactWeightThreePieceChain p)
    (certificate : ExactWeightThreeChainRunCertificate chain) :
    2 * exactChainPieceCount chain ≤
      (k - 2) * (exactChainTotalDeficit chain +
        certificate.endpointFullCount) := by
  let n1 := exactChainUnitCount chain
  let n2 := exactChainLargeCount chain
  let F := exactChainFullCount chain
  let R := certificate.fullRunCount
  let N := certificate.longInternalRunCount
  let e := certificate.endpointFullCount
  let Delta := exactChainTotalDeficit chain
  let partialCount := n1 + n2
  let excess := Delta - partialCount
  let r := exactChainPieceCount chain
  have hpartialLe : partialCount ≤ Delta := by
    dsimp [partialCount, n1, n2, Delta]
    exact exactChain_partialCount_le_totalDeficit chain
  have hOneSidedNat : 2 * R ≤ n1 + 2 * n2 + e := by
    exact certificate.oneSided
  have hDeficitNat : n1 + 2 * n2 ≤ Delta := by
    exact exactChain_unit_add_two_large_le_totalDeficit chain
  have hFullNat : F ≤ (k - 4) * R + e + N := by
    exact certificate.fullBound
  have hLongNat : (k - 3) * N ≤ 2 * excess := by
    exact certificate.longBound
  have hrNat : r = partialCount + F := by
    dsimp [r, partialCount, F, n1, n2]
    have h := exactChain_pieceCount_eq_full_add_partial chain
    omega
  have hk2Cast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
    rw [Int.ofNat_sub (by omega)]
    norm_num
  have hk3Cast : ((k - 3 : ℕ) : ℤ) = (k : ℤ) - 3 := by
    rw [Int.ofNat_sub (by omega)]
    norm_num
  have hk4Cast : ((k - 4 : ℕ) : ℤ) = (k : ℤ) - 4 := by
    rw [Int.ofNat_sub (by omega)]
    norm_num
  have hOneSidedIntRaw :
      2 * (R : ℤ) ≤ (n1 : ℤ) + 2 * (n2 : ℤ) + (e : ℤ) := by
    exact_mod_cast hOneSidedNat
  have hOneSidedInt :
      2 * (R : ℤ) - (e : ℤ) ≤ (n1 : ℤ) + 2 * (n2 : ℤ) := by
    linarith
  have hDeficitInt :
      (n1 : ℤ) + 2 * (n2 : ℤ) ≤ (Delta : ℤ) := by
    exact_mod_cast hDeficitNat
  have hFullIntRaw :
      (F : ℤ) ≤ ((k - 4 : ℕ) : ℤ) * (R : ℤ) + (e : ℤ) + (N : ℤ) := by
    exact_mod_cast hFullNat
  have hFullInt :
      (F : ℤ) ≤ ((k : ℤ) - 4) * (R : ℤ) + (e : ℤ) + (N : ℤ) := by
    rwa [← hk4Cast]
  have hLongIntRaw :
      ((k - 3 : ℕ) : ℤ) * (N : ℤ) ≤ 2 * (excess : ℤ) := by
    exact_mod_cast hLongNat
  have hLongInt :
      ((k : ℤ) - 3) * (N : ℤ) ≤ 2 * (excess : ℤ) := by
    rwa [← hk3Cast]
  have hcapInt := endpoint_matching_capacity
    (k := (k : ℤ)) (n1 := (n1 : ℤ)) (n2 := (n2 : ℤ))
    (e := (e : ℤ)) (R := (R : ℤ)) (F := (F : ℤ)) (N := (N : ℤ))
    (p := (partialCount : ℤ)) (Delta := (Delta : ℤ))
    (excess := (excess : ℤ)) (r := (r : ℤ))
    (by exact_mod_cast hk)
    (by positivity)
    hOneSidedInt
    hDeficitInt
    hFullInt
    (by
      dsimp [excess]
      rw [Int.ofNat_sub hpartialLe])
    hLongInt
    (by exact_mod_cast hrNat)
  rw [← hk2Cast] at hcapInt
  have hcapNat : 2 * r ≤ (k - 2) * (Delta + e) := by
    exact_mod_cast hcapInt
  simpa [r, Delta, e] using hcapNat

/-- 自然数版列表容量求和：逐项容量与端点总预算推出全列表容量。 -/
theorem component_capacity_nat_list
    {ι : Type} {k endpointBudget : ℕ} (_hk : 2 ≤ k)
    (items : List ι) (r delta endpoints : ι → ℕ)
    (hlocal : ∀ item ∈ items,
      2 * r item ≤ (k - 2) * (delta item + endpoints item))
    (hendpoints : (items.map endpoints).sum ≤ endpointBudget) :
    2 * (items.map r).sum ≤
      (k - 2) * ((items.map delta).sum + endpointBudget) := by
  have hsum :
      2 * (items.map r).sum ≤
        (k - 2) * ((items.map delta).sum + (items.map endpoints).sum) := by
    clear hendpoints
    induction items with
    | nil => simp
    | cons item items ih =>
        have hhead := hlocal item List.mem_cons_self
        have htail : ∀ tailItem ∈ items,
            2 * r tailItem ≤
              (k - 2) * (delta tailItem + endpoints tailItem) := by
          intro tailItem hmem
          exact hlocal tailItem (List.mem_cons_of_mem item hmem)
        have hi := ih htail
        simp only [List.map_cons, List.sum_cons]
        calc
          2 * (r item + (items.map r).sum) =
              2 * r item + 2 * (items.map r).sum := by ring
          _ ≤ (k - 2) * (delta item + endpoints item) +
              (k - 2) *
                ((items.map delta).sum + (items.map endpoints).sum) :=
            Nat.add_le_add hhead hi
          _ = (k - 2) *
              ((delta item + (items.map delta).sum) +
                (endpoints item + (items.map endpoints).sum)) := by ring
  have hbudget :
      (items.map delta).sum + (items.map endpoints).sum ≤
        (items.map delta).sum + endpointBudget :=
    Nat.add_le_add_left hendpoints _
  exact le_trans hsum (Nat.mul_le_mul_left (k - 2) hbudget)

/--
实际组件的精确权三链分区若逐链带游程证书，且满端点总数受
`2x+a+b` 控制，则自动得到正文自然数版 `component_capacity`。
-/
theorem actual_component_capacity_of_chainRunCertificates
    (hk : 5 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p))
    (hflatten : (chains.map ExactWeightThreePieceChain.pieces).flatten =
      componentIntervalPieces p (by omega) hp)
    (certificate : ∀ chain, ExactWeightThreeChainRunCertificate chain)
    (a b : ℕ)
    (hendpoints :
      (chains.map fun chain => (certificate chain).endpointFullCount).sum ≤
        2 * componentSeamResidual p + a + b) :
    2 * componentPieceCount p ≤
      (k - 2) *
        (componentPieceDeficit p + 2 * componentSeamResidual p + a + b) := by
  have hlocal : ∀ chain ∈ chains,
      2 * exactChainPieceCount chain ≤
        (k - 2) * (exactChainTotalDeficit chain +
          (certificate chain).endpointFullCount) := by
    intro chain _
    exact exactWeightThreeChain_capacity_of_runCertificate hk chain
      (certificate chain)
  have hcap := component_capacity_nat_list (by omega : 2 ≤ k) chains
    exactChainPieceCount exactChainTotalDeficit
    (fun chain => (certificate chain).endpointFullCount)
    hlocal hendpoints
  have hr := exactWeightThreeChainPartition_pieceCount_sum
    p (by omega) hp chains hflatten
  have hDelta := exactWeightThreeChainPartition_totalDeficit_sum
    (by omega : 4 ≤ k) hp chains hflatten
  change 2 * (chains.map fun chain => chain.pieces.length).sum ≤
      (k - 2) *
        ((chains.map fun chain => pieceListTotalDeficit chain.pieces).sum +
          (2 * componentSeamResidual p + a + b)) at hcap
  rw [hr, hDelta] at hcap
  simpa [Nat.add_assoc] using hcap

end PreimageChain

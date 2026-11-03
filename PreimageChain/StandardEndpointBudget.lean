import PreimageChain.ChainCapacity

/-!
# 标准链容量证书的端点预算

每条精确权三链只记录首、末片是否为满片。除组件最外侧的两个端点外，链分区
产生的每个内部切口至多贡献两个端点，因此端点总数受 `2x+a+b` 控制。
-/

namespace PreimageChain

open Hunter

variable {α : Type*}

/-- 列表首元素的函数值；空列表取零。 -/
def firstNatValue (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: _ => f x

/-- 列表末元素的函数值；空列表取零。 -/
def lastNatValue (f : α → ℕ) (xs : List α) : ℕ :=
  firstNatValue f xs.reverse

/-- 任意逐项至多一的自然数函数，其列表和至多列表长度。 -/
theorem sum_map_bit_le_length (f : α → ℕ) (hf : ∀ x, f x ≤ 1) :
    ∀ xs : List α, (xs.map f).sum ≤ xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- 将最前一项单独保留后，其余零一项至多贡献 `length-1`。 -/
theorem sum_map_bit_le_first
    (f : α → ℕ) (hf : ∀ x, f x ≤ 1) (xs : List α) :
    (xs.map f).sum ≤ xs.length - 1 + firstNatValue f xs := by
  cases xs with
  | nil => simp [firstNatValue]
  | cons x xs =>
      have htail := sum_map_bit_le_length f hf xs
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_sub_cancel, firstNatValue]
      omega

/-- 保留末项的反转版本。 -/
theorem sum_map_bit_le_last
    (f : α → ℕ) (hf : ∀ x, f x ≤ 1) (xs : List α) :
    (xs.map f).sum ≤ xs.length - 1 + lastNatValue f xs := by
  have h := sum_map_bit_le_first f hf xs.reverse
  simpa [lastNatValue] using h

/-- 两个零一端点函数的总和满足链切口预算。 -/
theorem sum_two_chain_endpoints_le
    (left right : α → ℕ)
    (hleft : ∀ x, left x ≤ 1) (hright : ∀ x, right x ≤ 1)
    (xs : List α) :
    (xs.map fun x => left x + right x).sum ≤
      2 * (xs.length - 1) + firstNatValue left xs + lastNatValue right xs := by
  have hsplit :
      (xs.map fun x => left x + right x).sum =
        (xs.map left).sum + (xs.map right).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        omega
  have hl := sum_map_bit_le_first left hleft xs
  have hr := sum_map_bit_le_last right hright xs
  rw [hsplit]
  omega

/-- 实际片是否为满片的零一指标。 -/
def actualPieceFullBit {k : ℕ} {p : HPath k}
    (piece : ComponentIntervalPiece p) : ℕ :=
  if piece.deficit = 0 then 1 else 0

@[simp] theorem actualPieceFullBit_le_one
    {k : ℕ} {p : HPath k} (piece : ComponentIntervalPiece p) :
    actualPieceFullBit piece ≤ 1 := by
  unfold actualPieceFullBit
  split <;> omega

/-- 精确权三链首片是否为满片。 -/
def chainFirstFullBit {k : ℕ} {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  firstNatValue actualPieceFullBit chain.pieces

/-- 精确权三链末片是否为满片。 -/
def chainLastFullBit {k : ℕ} {p : HPath k}
    (chain : ExactWeightThreePieceChain p) : ℕ :=
  lastNatValue actualPieceFullBit chain.pieces

@[simp] theorem chainFirstFullBit_le_one
    {k : ℕ} {p : HPath k} (chain : ExactWeightThreePieceChain p) :
    chainFirstFullBit chain ≤ 1 := by
  unfold chainFirstFullBit firstNatValue
  cases chain.pieces with
  | nil => simp
  | cons piece pieces => exact actualPieceFullBit_le_one piece

@[simp] theorem chainLastFullBit_le_one
    {k : ℕ} {p : HPath k} (chain : ExactWeightThreePieceChain p) :
    chainLastFullBit chain ≤ 1 := by
  unfold chainLastFullBit lastNatValue firstNatValue
  cases chain.pieces.reverse with
  | nil => simp
  | cons piece pieces => exact actualPieceFullBit_le_one piece

/-- 端点字段等于真实首末满片指标时，全部链自动满足切口预算。 -/
theorem standardCertificateEndpoints_le
    {k : ℕ} {p : HPath k}
    (chains : List (ExactWeightThreePieceChain p))
    (certificate : ∀ chain, ExactWeightThreeChainRunCertificate chain)
    (hendpoint : ∀ chain ∈ chains,
      (certificate chain).endpointFullCount =
        chainFirstFullBit chain + chainLastFullBit chain) :
    (chains.map fun chain => (certificate chain).endpointFullCount).sum ≤
      2 * (chains.length - 1) + firstNatValue chainFirstFullBit chains +
        lastNatValue chainLastFullBit chains := by
  have hgeneric := sum_two_chain_endpoints_le
    chainFirstFullBit chainLastFullBit
    (fun chain => chainFirstFullBit_le_one chain)
    (fun chain => chainLastFullBit_le_one chain) chains
  have heq :
      (chains.map fun chain => (certificate chain).endpointFullCount).sum =
        (chains.map fun chain =>
          chainFirstFullBit chain + chainLastFullBit chain).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro chain hchain
    exact hendpoint chain hchain
  rw [heq]
  exact hgeneric

/-- 非空组列表扁平化保持最外侧首元素。 -/
theorem firstNatValue_groups_flatten
    (f : α → ℕ) {β : Type*} (pieces : β → List α) (groups : List β)
    (hnonempty : ∀ group ∈ groups, pieces group ≠ []) :
    firstNatValue (fun group => firstNatValue f (pieces group)) groups =
      firstNatValue f ((groups.map pieces).flatten) := by
  cases groups with
  | nil => simp [firstNatValue]
  | cons group groups =>
      have hgroup := hnonempty group List.mem_cons_self
      cases hpieces : pieces group with
      | nil => exact False.elim (hgroup hpieces)
      | cons x xs => simp [firstNatValue, hpieces]

/-- 反转扁平列表等于反转组序后逐组反转再扁平化。 -/
theorem reverse_flatten_piece_groups (groups : List (List α)) :
    groups.flatten.reverse = (groups.reverse.map List.reverse).flatten := by
  induction groups with
  | nil => simp
  | cons group groups ih => simp [ih]

/-- 链分区的首端点与扁平片列表首端点一致。 -/
theorem chainPartition_firstFullBit
    {k : ℕ} {p : HPath k}
    (chains : List (ExactWeightThreePieceChain p)) :
    firstNatValue chainFirstFullBit chains =
      firstNatValue actualPieceFullBit
        ((chains.map ExactWeightThreePieceChain.pieces).flatten) := by
  exact firstNatValue_groups_flatten actualPieceFullBit
    ExactWeightThreePieceChain.pieces chains
    (by intro chain _; exact chain.nonempty)

/-- 链分区的末端点与扁平片列表末端点一致。 -/
theorem chainPartition_lastFullBit
    {k : ℕ} {p : HPath k}
    (chains : List (ExactWeightThreePieceChain p)) :
    lastNatValue chainLastFullBit chains =
      lastNatValue actualPieceFullBit
        ((chains.map ExactWeightThreePieceChain.pieces).flatten) := by
  change firstNatValue
      (fun chain : ExactWeightThreePieceChain p =>
        firstNatValue actualPieceFullBit chain.pieces.reverse)
      chains.reverse =
    firstNatValue actualPieceFullBit
      ((chains.map ExactWeightThreePieceChain.pieces).flatten.reverse)
  have hfirst := firstNatValue_groups_flatten actualPieceFullBit
    (fun chain : ExactWeightThreePieceChain p => chain.pieces.reverse)
    chains.reverse (by
      intro chain _
      simpa using chain.nonempty)
  have hflatten :
      (chains.reverse.map
        (fun chain : ExactWeightThreePieceChain p => chain.pieces.reverse)).flatten =
        (chains.map ExactWeightThreePieceChain.pieces).flatten.reverse := by
    rw [reverse_flatten_piece_groups
      (chains.map ExactWeightThreePieceChain.pieces)]
    simp [List.map_map, Function.comp_def]
  rw [hflatten] at hfirst
  exact hfirst

/-- 组件最左、最右实际片是否为满片。 -/
noncomputable def componentFirstFullBit
    {k : ℕ} (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) : ℕ :=
  firstNatValue actualPieceFullBit (componentIntervalPieces p hk hp)

noncomputable def componentLastFullBit
    {k : ℕ} (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) : ℕ :=
  lastNatValue actualPieceFullBit (componentIntervalPieces p hk hp)

@[simp] theorem componentFirstFullBit_le_one
    {k : ℕ} (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    componentFirstFullBit p hk hp ≤ 1 := by
  unfold componentFirstFullBit firstNatValue
  cases componentIntervalPieces p hk hp with
  | nil => simp
  | cons piece pieces => exact actualPieceFullBit_le_one piece

@[simp] theorem componentLastFullBit_le_one
    {k : ℕ} (p : HPath k) (hk : 1 ≤ k) (hp : p.StronglyExitless) :
    componentLastFullBit p hk hp ≤ 1 := by
  unfold componentLastFullBit lastNatValue firstNatValue
  cases (componentIntervalPieces p hk hp).reverse with
  | nil => simp
  | cons piece pieces => exact actualPieceFullBit_le_one piece

/-- 实际链分区的端点总数至多为 `2x` 加组件两个外端点。 -/
theorem actualComponent_standardEndpointBudget
    {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p))
    (hflatten : (chains.map ExactWeightThreePieceChain.pieces).flatten =
      componentIntervalPieces p hk hp)
    (hlength : chains.length = (componentPositiveSeams p).card + 1)
    (certificate : ∀ chain, ExactWeightThreeChainRunCertificate chain)
    (hendpoint : ∀ chain ∈ chains,
      (certificate chain).endpointFullCount =
        chainFirstFullBit chain + chainLastFullBit chain) :
    (chains.map fun chain => (certificate chain).endpointFullCount).sum ≤
      2 * componentSeamResidual p +
        componentFirstFullBit p hk hp + componentLastFullBit p hk hp := by
  have hgeneric := standardCertificateEndpoints_le chains certificate hendpoint
  have hfirst := chainPartition_firstFullBit chains
  have hlast := chainPartition_lastFullBit chains
  rw [hflatten] at hfirst hlast
  have hcuts := componentPositiveSeams_card_le_residual (p := p)
  unfold componentFirstFullBit componentLastFullBit
  rw [hfirst, hlast] at hgeneric
  rw [hlength] at hgeneric
  omega

end PreimageChain

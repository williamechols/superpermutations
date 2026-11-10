import PreimageChain.WeightTwo

/-!
# `σ²` 手术的严格进度

本模块在原始顶点列表上计数连续的 `u → σu` 边。这使论文引理 3.2
中“删除 `σu` 的旧位置不损失旋转边，新位置增加两条旋转边”可以
由 Lean 直接计算。
-/

namespace PreimageChain

open Hunter
open List
open scoped Classical

variable {k : ℕ}

/-- 列表中的权一旋转边数。 -/
def rotationCount : List (Vtx k) → ℕ
  | [] => 0
  | [_] => 0
  | u :: v :: t => (if v = sigma u then 1 else 0) + rotationCount (v :: t)

/-- 在标记顶点处切分列表计数。 -/
theorem rotationCount_append_cons
    (l : List (Vtx k)) (x : Vtx k) (m : List (Vtx k)) :
    rotationCount (l ++ x :: m) =
      rotationCount (l ++ [x]) + rotationCount (x :: m) := by
  induction l with
  | nil => simp [rotationCount]
  | cons a l ih =>
      cases l with
      | nil => simp [rotationCount]
      | cons b t =>
          simp only [List.cons_append, rotationCount]
          have ih' :
              rotationCount (b :: (t ++ x :: m)) =
                rotationCount (b :: (t ++ [x])) + rotationCount (x :: m) := by
            simpa only [List.cons_append] using ih
          rw [ih']
          omega

/-- `σu ≠ u`，当旋转类长度至少三时。 -/
theorem sigma_ne_self (hk : 3 ≤ k) (u : Vtx k) : sigma u ≠ u := by
  intro h
  have hinj := Hunter.ProofsExitless.sigma_iter_inj u
    (a := 1) (b := 0) (by omega) (by omega)
  have hiter : (sigma^[1]) u = (sigma^[0]) u := by simpa using h
  have : (1 : ℕ) = 0 := hinj hiter
  omega

/-- `σ²u ≠ σu`。 -/
theorem sigma2_ne_sigma (hk : 3 ≤ k) (u : Vtx k) : sigma2 u ≠ sigma u := by
  intro h
  apply sigma_ne_self hk u
  exact Hunter.ProofsSpine.sigma_inj h

/-- 在 `u → σ²u` 中插入 `σu` 恰好新增两条旋转边。 -/
theorem rotationCount_insert_sigma2
    (hk : 3 ≤ k) (pre suf : List (Vtx k)) (u : Vtx k) :
    rotationCount (pre ++ u :: sigma u :: sigma2 u :: suf) =
      rotationCount (pre ++ u :: sigma2 u :: suf) + 2 := by
  have hne : sigma (sigma u) ≠ sigma u := by
    simpa [sigma2] using sigma2_ne_sigma hk u
  rw [rotationCount_append_cons pre u (sigma u :: sigma2 u :: suf),
    rotationCount_append_cons pre u (sigma2 u :: suf)]
  simp [rotationCount, sigma2, hne]
  omega

/--
删除一个旧顶点时，若两条旧邻接边均不是旋转边，则旋转边数不减。
-/
theorem rotationCount_splice
    (p s : List (Vtx k)) (b : Vtx k)
    (hprev : ∀ c, (c, b) ∈ (p ++ b :: s).zip (p ++ b :: s).tail → b ≠ sigma c)
    (hnext : ∀ d, (b, d) ∈ (p ++ b :: s).zip (p ++ b :: s).tail → d ≠ sigma b) :
    rotationCount (p ++ b :: s) ≤ rotationCount (p ++ s) := by
  induction p with
  | nil =>
      cases s with
      | nil => simp [rotationCount]
      | cons d t =>
          have hbd : d ≠ sigma b := hnext d (by simp)
          simp [rotationCount, hbd]
  | cons c p ih =>
      cases p with
      | nil =>
          have hcb : b ≠ sigma c := hprev c (by simp)
          cases s with
          | nil => simp [rotationCount, hcb]
          | cons d t =>
              have hbd : d ≠ sigma b := hnext d (by simp)
              simp [rotationCount, hcb, hbd]
      | cons d t =>
          have ih' := ih
            (fun x hx => hprev x (by
              simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
                List.mem_cons]
              exact Or.inr hx))
            (fun x hx => hnext x (by
              simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
                List.mem_cons]
              exact Or.inr hx))
          simp only [List.cons_append, rotationCount]
          exact Nat.add_le_add_left ih' _

/--
局部 `σ²` 手术的加强版核心：显式构造新路径，并同时记录权重不增与
旋转边计数至少增加二。
-/
theorem sigma2_assemble_progress
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hedge : (u, sigma2 u) ∈ P.edges)
    {p s pre suf : List (Vtx k)}
    (hLdef : P.verts = p ++ sigma u :: s)
    (hMeq : p ++ s = pre ++ u :: sigma2 u :: suf) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧
      (u, sigma2 u) ∉ P'.edges ∧ P'.wtP ≤ P.wtP ∧
      rotationCount P.verts + 2 ≤ rotationCount P'.verts := by
  have htri : ew k u (sigma2 u) =
      ew k u (sigma u) + ew k (sigma u) (sigma2 u) := by
    rw [weight_sigma2 hk, Hunter.ew_sigma (by omega), sigma2,
      Hunter.ew_sigma (by omega)]
  have hne : pre ++ u :: sigma u :: sigma2 u :: suf ≠ [] :=
    List.ne_nil_of_mem (a := u) (by simp)
  have hperm1 : P.verts ~ (sigma u :: (p ++ s)) := by
    rw [hLdef]
    exact List.perm_middle
  have hperm2 : (pre ++ u :: sigma u :: sigma2 u :: suf) ~
      (sigma u :: (p ++ s)) := by
    have hrw : pre ++ u :: sigma u :: sigma2 u :: suf =
        (pre ++ [u]) ++ sigma u :: (sigma2 u :: suf) := by simp
    have heq : (pre ++ [u]) ++ (sigma2 u :: suf) = p ++ s := by
      rw [hMeq]
      simp
    rw [hrw]
    calc
      (pre ++ [u]) ++ sigma u :: (sigma2 u :: suf)
          ~ (sigma u :: ((pre ++ [u]) ++ (sigma2 u :: suf))) := List.perm_middle
      _ = sigma u :: (p ++ s) := by rw [heq]
  have hPL' : P.verts ~ (pre ++ u :: sigma u :: sigma2 u :: suf) :=
    hperm1.trans hperm2.symm
  have hnodup : (pre ++ u :: sigma u :: sigma2 u :: suf).Nodup :=
    hPL'.nodup P.nodup
  let P' : HPath k := ⟨pre ++ u :: sigma u :: sigma2 u :: suf, hne, hnodup⟩
  have hprev : ∀ c,
      (c, sigma u) ∈ (p ++ sigma u :: s).zip (p ++ sigma u :: s).tail →
        sigma u ≠ sigma c := by
    intro c hc hrot
    have hcP : (c, sigma u) ∈ P.edges := by
      rw [Hunter.ProofsSpine.mem_edges_iff, hLdef]
      exact hc
    have hcu : u = c := Hunter.ProofsSpine.sigma_inj hrot
    subst c
    have hfirst : (u, sigma2 u) ∈ Hunter.outV P.edges u := by
      rw [Hunter.outV, Hunter.mem_out]
      exact ⟨hedge, Finset.mem_singleton_self u⟩
    have hsecond : (u, sigma u) ∈ Hunter.outV P.edges u := by
      rw [Hunter.outV, Hunter.mem_out]
      exact ⟨hcP, Finset.mem_singleton_self u⟩
    have hpairs := Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_out_le_one P u)
      (u, sigma2 u) hfirst (u, sigma u) hsecond
    exact sigma2_ne_sigma hk u (congrArg Prod.snd hpairs)
  have hnext : ∀ d,
      (sigma u, d) ∈ (p ++ sigma u :: s).zip (p ++ sigma u :: s).tail →
        d ≠ sigma (sigma u) := by
    intro d hd hrot
    have hdP : (sigma u, d) ∈ P.edges := by
      rw [Hunter.ProofsSpine.mem_edges_iff, hLdef]
      exact hd
    have hds : d = sigma2 u := by simpa [sigma2] using hrot
    rw [hds] at hdP
    have hfirst : (u, sigma2 u) ∈ Hunter.intoV P.edges (sigma2 u) := by
      rw [Hunter.intoV, Hunter.mem_into]
      exact ⟨hedge, Finset.mem_singleton_self (sigma2 u)⟩
    have hsecond : (sigma u, sigma2 u) ∈ Hunter.intoV P.edges (sigma2 u) := by
      rw [Hunter.intoV, Hunter.mem_into]
      exact ⟨hdP, Finset.mem_singleton_self (sigma2 u)⟩
    have hpairs := Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_into_le_one P (sigma2 u))
      (u, sigma2 u) hfirst (sigma u, sigma2 u) hsecond
    exact sigma_ne_self hk u (congrArg Prod.fst hpairs).symm
  have hdelete : rotationCount P.verts ≤ rotationCount (p ++ s) := by
    rw [hLdef]
    exact rotationCount_splice p s (sigma u) hprev hnext
  have hinsert :
      rotationCount (pre ++ u :: sigma u :: sigma2 u :: suf) =
        rotationCount (p ++ s) + 2 := by
    rw [hMeq]
    exact rotationCount_insert_sigma2 hk pre suf u
  refine ⟨P', ?_, ?_, ?_, ?_⟩
  · intro v
    exact hPL'.mem_iff.mp (hP v)
  · intro hcontra
    have husigma : (u, sigma u) ∈ P'.edges :=
      Hunter.ImpRed.mem_edges_of_split (C := pre) (D := sigma2 u :: suf) rfl
    have hfirst : (u, sigma u) ∈ Hunter.outV P'.edges u := by
      rw [Hunter.outV, Hunter.mem_out]
      exact ⟨husigma, Finset.mem_singleton_self u⟩
    have hsecond : (u, sigma2 u) ∈ Hunter.outV P'.edges u := by
      rw [Hunter.outV, Hunter.mem_out]
      exact ⟨hcontra, Finset.mem_singleton_self u⟩
    have hpairs := Finset.card_le_one.mp
      (Hunter.ProofsSpine.path_out_le_one P' u)
      (u, sigma u) hfirst (u, sigma2 u) hsecond
    exact (sigma2_ne_sigma hk u) (congrArg Prod.snd hpairs).symm
  · show Hunter.ImpRed.pathW (pre ++ u :: sigma u :: sigma2 u :: suf) ≤ P.wtP
    have e1 : Hunter.ImpRed.pathW (pre ++ u :: sigma u :: sigma2 u :: suf) =
        Hunter.ImpRed.pathW (p ++ s) := by
      rw [Hunter.ImpRed.pathW_insert_eq htri pre suf, ← hMeq]
    have e3 : P.wtP = Hunter.ImpRed.pathW (p ++ sigma u :: s) := by
      change Hunter.ImpRed.pathW P.verts = _
      rw [hLdef]
    rw [e1, e3]
    exact Hunter.ImpRed.pathW_splice p s (sigma u) (by omega)
  · change rotationCount P.verts + 2 ≤
      rotationCount (pre ++ u :: sigma u :: sigma2 u :: suf)
    rw [hinsert]
    omega

/--
每条 `u → σ²u` 都可由一次显式手术删除；新路径保持 Hamilton 性、权重不增，
且原始列表中的旋转边计数至少增加二。
-/
theorem sigma2_surgery_progress
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) {u : Vtx k}
    (hedge : (u, sigma2 u) ∈ P.edges) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧
      (u, sigma2 u) ∉ P'.edges ∧ P'.wtP ≤ P.wtP ∧
      rotationCount P.verts + 2 ≤ rotationCount P'.verts := by
  have hzip : (u, sigma2 u) ∈ P.verts.zip P.verts.tail :=
    Hunter.ProofsSpine.mem_edges_iff.mp hedge
  obtain ⟨A, B, hAB⟩ := Hunter.ImpRed.zip_tail_split hzip
  have hsigmamem : sigma u ∈ P.verts := hP (sigma u)
  rw [hAB, List.mem_append, List.mem_cons, List.mem_cons] at hsigmamem
  rcases hsigmamem with hA | hequ | heqsigma2 | hB
  · obtain ⟨A1, A2, hAdef⟩ := List.mem_iff_append.mp hA
    refine sigma2_assemble_progress hk hP hedge
      (p := A1) (s := A2 ++ u :: sigma2 u :: B)
      (pre := A1 ++ A2) (suf := B) ?_ ?_
    · rw [hAB, hAdef]
      simp
    · simp
  · exact absurd hequ (sigma_ne_self hk u)
  · exact absurd heqsigma2 (sigma2_ne_sigma hk u).symm
  · obtain ⟨B1, B2, hBdef⟩ := List.mem_iff_append.mp hB
    refine sigma2_assemble_progress hk hP hedge
      (p := A ++ u :: sigma2 u :: B1) (s := B2)
      (pre := A) (suf := B1 ++ B2) ?_ ?_
    · rw [hAB, hBdef]
      simp
    · simp

/-- 旋转边计数不超过原始列表长度。 -/
theorem rotationCount_le_length : ∀ l : List (Vtx k), rotationCount l ≤ l.length
  | [] => by simp [rotationCount]
  | [u] => by simp [rotationCount]
  | u :: v :: t => by
      have ih := rotationCount_le_length (v :: t)
      simp only [List.length_cons] at ih
      simp only [rotationCount, List.length_cons]
      split <;> omega

/-- Hamilton 路径的旋转边计数由顶点类型的基数统一控制。 -/
theorem rotationCount_le_card {P : HPath k} (hP : P.IsHamiltonian) :
    rotationCount P.verts ≤ Fintype.card (Vtx k) := by
  calc
    rotationCount P.verts ≤ P.verts.length := rotationCount_le_length P.verts
    _ = Fintype.card (Vtx k) := P.numVerts_eq_card_of_hamiltonian hP

/--
无条件 `σ²` 正规形：任一 Hamilton 路径都可约化为不含 `u → σ²u` 的路径，
且总权重不增加。
-/
theorem sigma2_reduced_normal_form
    (hk : 3 ≤ k) {P : HPath k} (hP : P.IsHamiltonian) :
    ∃ P' : HPath k, P'.IsHamiltonian ∧ Sigma2Reduced P' ∧ P'.wtP ≤ P.wtP := by
  let State := {Q : HPath k // Q.IsHamiltonian}
  let cost : State → ℕ := fun Q => Q.1.wtP
  let measure : State → ℕ := fun Q => rotationCount Q.1.verts
  let Normal : State → Prop := fun Q => Sigma2Reduced Q.1
  have hbound : ∀ Q : State, measure Q ≤ Fintype.card (Vtx k) :=
    fun Q => rotationCount_le_card Q.2
  have hstep : ∀ Q : State, ¬Normal Q →
      ∃ Q', cost Q' ≤ cost Q ∧ measure Q + 1 ≤ measure Q' := by
    intro Q hnot
    simp only [Normal, Sigma2Reduced, not_forall] at hnot
    obtain ⟨u, hedge⟩ := hnot
    simp only [not_not] at hedge
    obtain ⟨Q', hQ', _hremoved, hcost, hprogress⟩ :=
      sigma2_surgery_progress hk Q.2 hedge
    refine ⟨⟨Q', hQ'⟩, hcost, ?_⟩
    change rotationCount Q.1.verts + 1 ≤ rotationCount Q'.verts
    omega
  obtain ⟨Q, hnormal, hcost⟩ := normal_form_of_bounded_progress
    cost measure Normal (Fintype.card (Vtx k)) hbound hstep ⟨P, hP⟩
  exact ⟨Q.1, Q.2, hnormal, hcost⟩

end PreimageChain

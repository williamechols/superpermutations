import Hunter.ProofsChartEq
import PreimageChain.PortalGeometry

/-!
# 门户附录的符号坐标

本模块把正文附录中的部分片占用坐标与候选满片坐标写成列表，并逐行证明六方向
碰撞表。有限程序只作转录审计；这里的等式对任意列表长度成立。
-/

namespace PreimageChain

open Hunter

/-- 部分片在标号 `i` 处的带标记旋转类代表元。 -/
def partialIncidenceWord (R : List ℕ) (m a b i : ℕ) : List ℕ :=
  m :: (a :: b :: R).rotate i

/-- 方向 `(p,q,t)` 的第 `j` 个候选满片在标号 `l` 处的代表元。 -/
def successorIncidenceWord
    (R : List ℕ) (p q t j l : ℕ) : List ℕ :=
  t :: (((R ++ [p]).rotate j ++ [q]).rotate l)

/-- 把末尾 marker 转到词首不改变旋转类。 -/
theorem rotClass_append_marker (B : List ℕ) (t : ℕ) :
    rotClass (B ++ [t]) = rotClass (t :: B) := by
  calc
    rotClass (B ++ [t]) = rotClass ((B ++ [t]).rotate B.length) :=
      (Hunter.ProofsClosure3.rotClass_rotate (B ++ [t]) B.length).symm
    _ = rotClass (t :: B) := by rw [List.rotate_append_length_eq]; rfl

/-- 满片走完门游程后的 `α` 后继把长度 `k-2` 的前缀左转一位。 -/
theorem alphaWord_bexit_runW_last
    {k : ℕ} (hk : 3 ≤ k) {A : List ℕ} (hA : A.length = k - 2)
    (q t : ℕ) :
    alphaWord (Hunter.ProofsRigidity2.bexit k
      (Hunter.ProofsRigidity2.runW A q t A.length)) =
      A.rotate 1 ++ [q, t] := by
  obtain ⟨a₁, As, hAcons⟩ : ∃ a₁ As, A = a₁ :: As := by
    cases A with
    | nil => simp at hA; omega
    | cons a₁ As => exact ⟨a₁, As, rfl⟩
  subst A
  rw [Hunter.ProofsRigidity2.bexit_runW_last (by omega)
    (by simpa using hA) q t]
  simp [alphaWord, List.rotate_cons_succ]

/-- 块边界源点是前一块起点的右旋出口。 -/
theorem blockBoundarySource_eq_bexit
    {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless) {t : ℕ}
    (ht : 1 ≤ t) (hN : k * t < p.numVerts) :
    (p.vert (k * t - 1) : List ℕ) =
      Hunter.ProofsRigidity2.bexit k (Hunter.ProofsChartEq.blockWord p (t - 1)) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hB : k * t' + (k - 1) < p.numVerts := by
    have hmul : k * (t' + 1) = k * t' + k := by ring
    rw [hmul] at hN
    omega
  have hcycle := Hunter.ProofsExitless.block_is_full_cycle hk hp
    (B := k * t') (r := k - 1) ⟨t', rfl⟩ (by omega) hB
  have hidx : k * t' + (k - 1) = k * (t' + 1) - 1 := by
    have hmul : k * (t' + 1) = k * t' + k := by ring
    omega
  rw [hidx] at hcycle
  rw [hcycle, Hunter.ProofsExitless.sigma_iter_val]
  rfl

/--
真实满片的内部门游程若在末端取 `α` 接缝，则下一片起点精确为前缀左转一位。
-/
theorem fullPiece_alpha_next_start
    {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start : ℕ} {A : List ℕ} (hA : A.length = k - 2) {q t : ℕ}
    (hnextRange : k * (start + (k - 1)) < p.numVerts)
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 2 →
      Hunter.ProofsLedger.IsDoor p (start + r))
    (hstart : Hunter.ProofsChartEq.blockWord p start = A ++ [q, t])
    (halpha : Hunter.ProofsLedger.IsAlpha p (start + (k - 1))) :
    Hunter.ProofsChartEq.blockWord p (start + (k - 1)) =
      A.rotate 1 ++ [q, t] := by
  have hlastRange : k * (start + (k - 2)) < p.numVerts := by
    have hle : start + (k - 2) ≤ start + (k - 1) := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k hle) hnextRange
  have hrun := Hunter.ProofsFillPath.blockrun_eq (by omega : 2 ≤ k) hp
    start (k - 2) hlastRange (by
      intro r hr1 hr2
      simpa [Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] using
        hdoors r hr1 hr2)
  have hnd : (A ++ [q, t]).Nodup := by
    rw [← hstart]
    exact (Hunter.ProofsChartEq.blockWord_isPermWord p start).nodup
  have hroot : (p.vert (k * start) : List ℕ) = A ++ [q, t] := hstart
  have hlastRaw := hrun (k - 2) (le_refl _)
  change Hunter.ProofsChartEq.blockWord p (start + (k - 2)) = _ at hlastRaw
  rw [hroot, Hunter.ProofsConfinement.erase_getLastD hnd] at hlastRaw
  have hlast : Hunter.ProofsChartEq.blockWord p (start + (k - 2)) =
      Hunter.ProofsRigidity2.runW A q t A.length := by
    simpa [Hunter.ProofsRigidity2.runW, hA] using hlastRaw
  have hnextPos : 1 ≤ start + (k - 1) := by omega
  have hsource := blockBoundarySource_eq_bexit (by omega : 1 ≤ k) hp
    hnextPos hnextRange
  have hprev : start + (k - 1) - 1 = start + (k - 2) := by omega
  rw [hprev, hlast] at hsource
  have htarget := halpha.2.2
  change Hunter.ProofsChartEq.blockWord p (start + (k - 1)) =
    alphaWord (p.vert (k * (start + (k - 1)) - 1) : List ℕ) at htarget
  rw [hsource, alphaWord_bexit_runW_last hk hA q t] at htarget
  exact htarget

/-- 满片内第 `l` 个块起点的精确词坐标。 -/
theorem fullPiece_block_word
    {k : ℕ} (hk : 3 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start : ℕ} {A : List ℕ} (hA : A.length = k - 2) {q t l : ℕ}
    (hl : l ≤ k - 2)
    (hlastRange : k * (start + (k - 2)) < p.numVerts)
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 2 →
      Hunter.ProofsLedger.IsDoor p (start + r))
    (hstart : Hunter.ProofsChartEq.blockWord p start = A ++ [q, t]) :
    Hunter.ProofsChartEq.blockWord p (start + l) =
      (A ++ [q]).rotate l ++ [t] := by
  have hrun := Hunter.ProofsFillPath.blockrun_eq (by omega : 2 ≤ k) hp
    start (k - 2) hlastRange (by
      intro r hr1 hr2
      simpa [Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] using
        hdoors r hr1 hr2)
  have hnd : (A ++ [q, t]).Nodup := by
    rw [← hstart]
    exact (Hunter.ProofsChartEq.blockWord_isPermWord p start).nodup
  have hroot : (p.vert (k * start) : List ℕ) = A ++ [q, t] := hstart
  have hword := hrun l hl
  change Hunter.ProofsChartEq.blockWord p (start + l) = _ at hword
  rw [hroot, Hunter.ProofsConfinement.erase_getLastD hnd] at hword
  simpa using hword

/-- 任意门段内第 `l` 个块的精确旋转词；满片和部分片共用这一接口。 -/
theorem doorSegment_block_word
    {k : ℕ} (hk : 2 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start r l : ℕ} {base : List ℕ} {marker : ℕ}
    (hl : l ≤ r)
    (hrange : k * (start + r) < p.numVerts)
    (hdoors : ∀ i, 1 ≤ i → i ≤ r →
      Hunter.ProofsLedger.IsDoor p (start + i))
    (hstart : Hunter.ProofsChartEq.blockWord p start = base ++ [marker]) :
    Hunter.ProofsChartEq.blockWord p (start + l) =
      base.rotate l ++ [marker] := by
  have hrun := Hunter.ProofsFillPath.blockrun_eq hk hp start r hrange (by
    intro i hi1 hi2
    simpa [Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] using
      hdoors i hi1 hi2)
  have hnd : (base ++ [marker]).Nodup := by
    rw [← hstart]
    exact (Hunter.ProofsChartEq.blockWord_isPermWord p start).nodup
  have hroot : (p.vert (k * start) : List ℕ) = base ++ [marker] := hstart
  have hword := hrun l hl
  change Hunter.ProofsChartEq.blockWord p (start + l) = _ at hword
  rw [hroot, Hunter.ProofsConfinement.erase_getLastD hnd] at hword
  simpa using hword

/--
若满片的 `α` 后继是 `R,a,b,m`，则该满片内部的第二个块必为 `R,b,a,m`。
这是单位缺口两侧碰撞所需的纯列表换位恒等式。
-/
theorem fullPiece_second_word_of_alpha_target
    {A R : List ℕ} {q t a b m : ℕ}
    (hA : A.length = R.length + 1)
    (htarget : A.rotate 1 ++ [q, t] = R ++ [a, b, m]) :
    (A ++ [q]).rotate 1 ++ [t] = R ++ [b, a, m] := by
  cases A with
  | nil => simp at hA
  | cons x As =>
      have hlen : As.length = R.length := by simpa using hA
      have htarget' : As ++ [x, q, t] = R ++ [a, b, m] := by
        simpa [List.rotate_cons_succ, List.append_assoc] using htarget
      obtain ⟨hAs, htail⟩ := List.append_inj htarget' hlen
      subst R
      simp at htail
      obtain ⟨rfl, rfl, rfl⟩ := htail
      simp [List.rotate_cons_succ, List.append_assoc]

/-! ## 内部长满游程右端的坐标碰撞 -/

/-- 权三后继的六种尾部方向。 -/
inductive PortalOrientation where
  | mab | mba | abm | amb | bma | bam
  deriving DecidableEq

-- Lean 4.35 port: the derived `Fintype` instance no longer elaborates; it is written out.
instance : Fintype PortalOrientation where
  elems := {.mab, .mba, .abm, .amb, .bma, .bam}
  complete := by intro x; cases x <;> decide

/-- 左端长方向产生的第 `j` 个满片之第 `l` 个实际块词。 -/
def longRunBlockWord (U : List ℕ) (m a b c j l : ℕ) : List ℕ :=
  ((((U ++ [c, b]).rotate j) ++ [a]).rotate l) ++ [m]

/-- 右部分片起始方向 `(p,q,t)` 的第 `l` 个实际块词。 -/
def rightPartialBlockWord (U : List ℕ) (b p q t l : ℕ) : List ℕ :=
  ((b :: U ++ [p, q]).rotate l) ++ [t]

/-- 长方向最后满片的最后块词。 -/
theorem longRunBlockWord_last (U : List ℕ) (m a b c : ℕ) :
    longRunBlockWord U m a b c U.length (U.length + 2) =
      a :: c :: b :: U ++ [m] := by
  simp [longRunBlockWord, List.rotate_append_length_eq,
    List.rotate_cons_succ, List.append_assoc]

/-- 当 `|U|=k-4` 时，上述最后块的右旋出口为 `m,a,c,b,U`。 -/
theorem bexit_longRunBlockWord_last
    {k : ℕ} (hk : 4 ≤ k) (U : List ℕ) (m a b c : ℕ)
    (hU : U.length = k - 4) :
    Hunter.ProofsRigidity2.bexit k
      (longRunBlockWord U m a b c U.length (U.length + 2)) =
        m :: a :: c :: b :: U := by
  rw [longRunBlockWord_last]
  unfold Hunter.ProofsRigidity2.bexit
  rw [show k - 1 = (a :: c :: b :: U).length by simp [hU]; omega,
    List.rotate_append_length_eq]
  rfl

/-- 右方向 `(m,a,c)` 在其起点撞到最后满片。 -/
theorem internalCollision_mac (U : List ℕ) (m a b c : ℕ) :
    rotClass (rightPartialBlockWord U b m a c 0) =
      rotClass (longRunBlockWord U m a b c U.length (U.length + 2)) := by
  let w := longRunBlockWord U m a b c U.length (U.length + 2)
  calc
    rotClass (rightPartialBlockWord U b m a c 0) = rotClass (w.rotate 2) := by
      apply congrArg rotClass
      dsimp [w, longRunBlockWord, rightPartialBlockWord]
      rw [List.rotate_zero, List.rotate_append_length_eq]
      simp [List.append_assoc, List.rotate_append_length_eq]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w 2

/-- 右方向 `(m,c,a)` 在其第二个块撞到首个满片。 -/
theorem internalCollision_mca (U : List ℕ) (m a b c : ℕ) :
    rotClass (rightPartialBlockWord U b m c a 1) =
      rotClass (longRunBlockWord U m a b c 0 U.length) := by
  let w := longRunBlockWord U m a b c 0 U.length
  calc
    rotClass (rightPartialBlockWord U b m c a 1) = rotClass (w.rotate 3) := by
      apply congrArg rotClass
      dsimp [w, longRunBlockWord, rightPartialBlockWord]
      rw [List.rotate_zero,
        show U ++ [c, b] ++ [a] = U ++ [c, b, a] by simp,
        List.rotate_append_length_eq]
      simp [List.rotate_cons_succ, List.append_assoc,
        List.rotate_append_length_eq]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w 3

/-- 右方向 `(a,m,c)` 在其起点撞到最后满片。 -/
theorem internalCollision_amc (U : List ℕ) (m a b c : ℕ) :
    rotClass (rightPartialBlockWord U b a m c 0) =
      rotClass (longRunBlockWord U m a b c U.length 0) := by
  let w := longRunBlockWord U m a b c U.length 0
  calc
    rotClass (rightPartialBlockWord U b a m c 0) = rotClass (w.rotate 1) := by
      apply congrArg rotClass
      dsimp [w, longRunBlockWord, rightPartialBlockWord]
      rw [List.rotate_zero, List.rotate_append_length_eq]
      simp [List.rotate_cons_succ, List.append_assoc]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w 1

/-- 右方向 `(a,c,m)` 在其起点精确撞到最后满片的第二个块。 -/
theorem internalCollision_acm (U : List ℕ) (m a b c : ℕ) :
    rightPartialBlockWord U b a c m 0 =
      longRunBlockWord U m a b c U.length 1 := by
  simp [longRunBlockWord, rightPartialBlockWord,
    List.rotate_append_length_eq, List.rotate_cons_succ, List.append_assoc]

/-- 右方向 `(c,m,a)` 在其第二个块撞到首个满片。 -/
theorem internalCollision_cma (U : List ℕ) (m a b c : ℕ) :
    rotClass (rightPartialBlockWord U b c m a 1) =
      rotClass (longRunBlockWord U m a b c 0 (U.length + 1)) := by
  let w := longRunBlockWord U m a b c 0 (U.length + 1)
  calc
    rotClass (rightPartialBlockWord U b c m a 1) = rotClass (w.rotate 2) := by
      apply congrArg rotClass
      dsimp [w, longRunBlockWord, rightPartialBlockWord]
      rw [List.rotate_zero,
        show U ++ [c, b] ++ [a] = (U ++ [c]) ++ [b, a] by simp,
        show U.length + 1 = (U ++ [c]).length by simp,
        List.rotate_append_length_eq]
      simp [List.rotate_cons_succ, List.append_assoc,
        List.rotate_append_length_eq]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w 2

/--
剩余方向 `(c,a,m)` 中，左缺口的 incidence `delta+1` 与右缺口的 incidence
`delta` 是同一个带标记词。
-/
theorem internalCollision_cam (U : List ℕ) (m a b c delta : ℕ) :
    partialIncidenceWord (U ++ [c]) m a b (delta + 1) =
      m :: (b :: U ++ [c, a]).rotate delta := by
  simp only [partialIncidenceWord]
  rw [List.rotate_cons_succ]
  simp [List.append_assoc]

/-- 六种右部分片方向的第 `l` 个实际块词。 -/
def orientedRightPartialBlockWord
    (U : List ℕ) (b m a c : ℕ) (o : PortalOrientation) (l : ℕ) : List ℕ :=
  match o with
  | .mab => rightPartialBlockWord U b m a c l
  | .mba => rightPartialBlockWord U b m c a l
  | .abm => rightPartialBlockWord U b a c m l
  | .amb => rightPartialBlockWord U b a m c l
  | .bma => rightPartialBlockWord U b c m a l
  | .bam => rightPartialBlockWord U b c a m l

/--
内部长度 `|U|+1=k-3` 满游程与左右部分片支持不交的坐标接口。右部分片有
`|U|+3-rightDeficit` 个块。
-/
def InternalLongCoordinateDisjoint
    (U : List ℕ) (m a b c leftDeficit rightDeficit : ℕ)
    (o : PortalOrientation) : Prop :=
  (∀ j, j < U.length + 1 → ∀ l, l < U.length + 3 →
      ∀ r, r < U.length + 3 - rightDeficit →
        rotClass (longRunBlockWord U m a b c j l) ≠
          rotClass (orientedRightPartialBlockWord U b m a c o r)) ∧
  (∀ r, r < U.length + 3 - rightDeficit →
      rotClass (partialIncidenceWord (U ++ [c]) m a b (leftDeficit + 1)) ≠
        rotClass (orientedRightPartialBlockWord U b m a c o r))

/--
正文局部结论 (iv) 的坐标核心：若长度 `|U|+1` 的内部满游程两侧支持不交，
则相邻缺口之和至少为完整 incidence 周期长度 `|U|+3`。
-/
theorem internalLongRun_threshold_coordinates
    (U : List ℕ) (m a b c leftDeficit rightDeficit : ℕ)
    (o : PortalOrientation)
    (hleft : 1 ≤ leftDeficit) (hright : 1 ≤ rightDeficit)
    (hdisjoint : InternalLongCoordinateDisjoint U m a b c
      leftDeficit rightDeficit o) :
    U.length + 3 ≤ leftDeficit + rightDeficit := by
  by_contra hsum
  push Not at hsum
  have hr0 : 0 < U.length + 3 - rightDeficit := by omega
  have hr1 : 1 < U.length + 3 - rightDeficit := by omega
  have hrDelta : leftDeficit < U.length + 3 - rightDeficit := by omega
  cases o with
  | mab =>
      have h := hdisjoint.1 U.length (by omega) (U.length + 2) (by omega)
        0 hr0
      exact h (internalCollision_mac U m a b c).symm
  | mba =>
      have h := hdisjoint.1 0 (by omega) U.length (by omega) 1 hr1
      exact h (internalCollision_mca U m a b c).symm
  | abm =>
      have h := hdisjoint.1 U.length (by omega) 1 (by omega) 0 hr0
      exact h (congrArg rotClass (internalCollision_acm U m a b c)).symm
  | amb =>
      have h := hdisjoint.1 U.length (by omega) 0 (by omega) 0 hr0
      exact h (internalCollision_amc U m a b c).symm
  | bma =>
      have h := hdisjoint.1 0 (by omega) (U.length + 1) (by omega) 1 hr1
      exact h (internalCollision_cma U m a b c).symm
  | bam =>
      have h := hdisjoint.2 leftDeficit hrDelta
      apply h
      calc
        rotClass (partialIncidenceWord (U ++ [c]) m a b (leftDeficit + 1)) =
            rotClass (m :: (b :: U ++ [c, a]).rotate leftDeficit) := by
          rw [internalCollision_cam]
        _ = rotClass (rightPartialBlockWord U b c a m leftDeficit) :=
          (rotClass_append_marker ((b :: U ++ [c, a]).rotate leftDeficit) m).symm

/-- 碰撞表第一行 `(m,a,b)`：首个候选满片立即碰撞。 -/
theorem portalCollision_mab (R : List ℕ) (m a b : ℕ) :
    rotClass (partialIncidenceWord R m a b 0) =
      rotClass (successorIncidenceWord R m a b 0 0) := by
  let w := successorIncidenceWord R m a b 0 0
  calc
    rotClass (partialIncidenceWord R m a b 0) =
        rotClass (w.rotate (R.length + 1)) := by
      apply congrArg rotClass
      simp [partialIncidenceWord, w, successorIncidenceWord,
        List.rotate_zero, List.append_assoc, List.rotate_append_length_eq]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w (R.length + 1)

/-- 碰撞表第二行 `(m,b,a)`：首个候选满片立即碰撞。 -/
theorem portalCollision_mba (R : List ℕ) (m a b : ℕ) :
    rotClass (partialIncidenceWord R m a b 0) =
      rotClass (successorIncidenceWord R m b a 0 (R.length + 1)) := by
  let w := successorIncidenceWord R m b a 0 (R.length + 1)
  have hw : w = (a :: b :: R) ++ [m] := by
    dsimp [w, successorIncidenceWord]
    rw [List.rotate_zero,
      show R.length + 1 = (R ++ [m]).length by simp,
      List.rotate_append_length_eq]
    simp
  calc
    rotClass (partialIncidenceWord R m a b 0) =
        rotClass (w.rotate (R.length + 2)) := by
      apply congrArg rotClass
      rw [hw, show R.length + 2 = (a :: b :: R).length by simp,
        List.rotate_append_length_eq]
      simp [partialIncidenceWord]
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w (R.length + 2)

/-- `abR` 左转两位等于 `Rab`。 -/
theorem rotate_abR_two (R : List ℕ) (a b : ℕ) :
    (a :: b :: R).rotate 2 = R ++ [a, b] := by
  rw [show a :: b :: R = [a, b] ++ R from rfl,
    show (2 : ℕ) = ([a, b] : List ℕ).length from rfl,
    List.rotate_append_length_eq]

/-- `abR` 左转一位等于 `bRa`。 -/
theorem rotate_abR_one (R : List ℕ) (a b : ℕ) :
    (a :: b :: R).rotate 1 = b :: R ++ [a] := by
  rw [show a :: b :: R = [a] ++ (b :: R) from rfl,
    show (1 : ℕ) = ([a] : List ℕ).length from rfl,
    List.rotate_append_length_eq]

/-- 碰撞表第三行 `(a,b,m)`。 -/
theorem portalCollision_abm (R : List ℕ) (m a b delta : ℕ)
    (hdelta : 1 ≤ delta) :
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
      rotClass (successorIncidenceWord R a b m 0 (delta - 1)) := by
  apply congrArg rotClass
  unfold partialIncidenceWord successorIncidenceWord
  simp only [List.rotate_zero]
  apply congrArg (List.cons m)
  symm
  calc
    (R ++ [a] ++ [b]).rotate (delta - 1) =
        ((a :: b :: R).rotate 2).rotate (delta - 1) := by
      rw [rotate_abR_two]
      simp
    _ = (a :: b :: R).rotate (2 + (delta - 1)) :=
      List.rotate_rotate _ _ _
    _ = (a :: b :: R).rotate (delta + 1) := by
      rw [show 2 + (delta - 1) = delta + 1 by omega]

/-- 碰撞表第六行 `(b,a,m)`，首次回返编号为 `|R|=n-2`。 -/
theorem portalCollision_bam (R : List ℕ) (m a b delta : ℕ) :
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
      rotClass (successorIncidenceWord R b a m R.length delta) := by
  apply congrArg rotClass
  unfold partialIncidenceWord successorIncidenceWord
  apply congrArg (List.cons m)
  symm
  calc
    (((R ++ [b]).rotate R.length) ++ [a]).rotate delta =
        ((b :: R) ++ [a]).rotate delta := by
      rw [List.rotate_append_length_eq]
      simp
    _ = ((a :: b :: R).rotate 1).rotate delta := by
      rw [rotate_abR_one]
    _ = (a :: b :: R).rotate (1 + delta) := List.rotate_rotate _ _ _
    _ = (a :: b :: R).rotate (delta + 1) := by rw [Nat.add_comm]

/-- 碰撞表第四行 `(a,m,b)`，碰撞满片编号为 `delta-1`。 -/
theorem portalCollision_amb (R : List ℕ) (m a b delta : ℕ)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1) :
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
      rotClass (successorIncidenceWord R a m b (delta - 1)
        (R.length + 2 - delta)) := by
  let d := delta - 1
  let U := R.take d
  let V := R.drop d
  have hd : d ≤ R.length := by dsimp [d]; omega
  have hUlen : U.length = d := by
    dsimp [U]
    rw [List.length_take, Nat.min_eq_left hd]
  have hVlen : V.length = R.length - d := by
    dsimp [V]
    rw [List.length_drop]
  have hsplit : R = U ++ V := by
    dsimp [U, V]
    exact (List.take_append_drop d R).symm
  have hrotRA : (R ++ [a]).rotate d = (V ++ [a]) ++ U := by
    rw [hsplit, ← hUlen]
    simp only [List.append_assoc]
    rw [List.rotate_append_length_eq]
    simp [List.append_assoc]
  let w := successorIncidenceWord R a m b (delta - 1) (R.length + 2 - delta)
  have hw : w = b :: U ++ [m] ++ V ++ [a] := by
    dsimp [w, successorIncidenceWord, d] at ⊢
    rw [show delta - 1 = d by rfl, hrotRA]
    have hl : R.length + 2 - delta = (V ++ [a]).length := by
      simp only [List.length_append, List.length_singleton, hVlen]
      dsimp [d]
      omega
    rw [hl]
    rw [List.append_assoc (V ++ [a]) U [m]]
    rw [List.rotate_append_length_eq]
    simp [List.append_assoc]
  have hpword : partialIncidenceWord R m a b (delta + 1) =
      m :: V ++ [a, b] ++ U := by
    dsimp [partialIncidenceWord]
    rw [hsplit]
    have hi : delta + 1 = ([a, b] ++ U).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hUlen]
      dsimp [d]
      omega
    change m :: ((([a, b] ++ U) ++ V).rotate (delta + 1)) = _
    rw [hi, List.rotate_append_length_eq]
    simp [List.append_assoc]
  calc
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
        rotClass (w.rotate delta) := by
      apply congrArg rotClass
      rw [hpword, hw]
      have hi : delta = (b :: U).length := by
        simp only [List.length_cons, hUlen]
        dsimp [d]
        omega
      rw [show b :: U ++ [m] ++ V ++ [a] =
          (b :: U) ++ (m :: V ++ [a]) by simp, hi,
        List.rotate_append_length_eq]
      simp
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w delta

/-- 碰撞表第五行 `(b,m,a)`，碰撞满片编号同为 `delta-1`。 -/
theorem portalCollision_bma (R : List ℕ) (m a b delta : ℕ)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1) :
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
      rotClass (successorIncidenceWord R b m a (delta - 1)
        (R.length + 1 - delta)) := by
  let d := delta - 1
  let U := R.take d
  let V := R.drop d
  have hd : d ≤ R.length := by dsimp [d]; omega
  have hUlen : U.length = d := by
    dsimp [U]
    rw [List.length_take, Nat.min_eq_left hd]
  have hVlen : V.length = R.length - d := by
    dsimp [V]
    rw [List.length_drop]
  have hsplit : R = U ++ V := by
    dsimp [U, V]
    exact (List.take_append_drop d R).symm
  have hrotRB : (R ++ [b]).rotate d = (V ++ [b]) ++ U := by
    rw [hsplit, ← hUlen]
    simp only [List.append_assoc]
    rw [List.rotate_append_length_eq]
    simp [List.append_assoc]
  let w := successorIncidenceWord R b m a (delta - 1) (R.length + 1 - delta)
  have hw : w = a :: b :: U ++ [m] ++ V := by
    dsimp [w, successorIncidenceWord, d] at ⊢
    rw [show delta - 1 = d by rfl, hrotRB]
    have hl : R.length + 1 - delta = V.length := by
      rw [hVlen]
      dsimp [d]
      omega
    rw [hl]
    simp only [List.append_assoc]
    rw [List.rotate_append_length_eq]
    simp
  have hpword : partialIncidenceWord R m a b (delta + 1) =
      m :: V ++ [a, b] ++ U := by
    dsimp [partialIncidenceWord]
    rw [hsplit]
    have hi : delta + 1 = ([a, b] ++ U).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hUlen]
      dsimp [d]
      omega
    change m :: ((([a, b] ++ U) ++ V).rotate (delta + 1)) = _
    rw [hi, List.rotate_append_length_eq]
    simp [List.append_assoc]
  calc
    rotClass (partialIncidenceWord R m a b (delta + 1)) =
        rotClass (w.rotate (delta + 1)) := by
      apply congrArg rotClass
      rw [hpword, hw]
      have hi : delta + 1 = (a :: b :: U).length := by
        simp only [List.length_cons, hUlen]
        dsimp [d]
        omega
      rw [show a :: b :: U ++ [m] ++ V =
          (a :: b :: U) ++ (m :: V) by simp, hi,
        List.rotate_append_length_eq]
      simp
    _ = rotClass w := Hunter.ProofsClosure3.rotClass_rotate w (delta + 1)

/-! ## 六方向汇总与端点游程界 -/

/-- 按六种方向生成候选满片的带标记 incidence word。 -/
def orientedSuccessorIncidenceWord
    (R : List ℕ) (m a b : ℕ) (o : PortalOrientation) (j l : ℕ) : List ℕ :=
  match o with
  | .mab => successorIncidenceWord R m a b j l
  | .mba => successorIncidenceWord R m b a j l
  | .abm => successorIncidenceWord R a b m j l
  | .amb => successorIncidenceWord R a m b j l
  | .bma => successorIncidenceWord R b m a j l
  | .bam => successorIncidenceWord R b a m j l

/-- 六方向下第 `j` 个候选满片的实际起始词。 -/
def orientedSuccessorStartWord
    (R : List ℕ) (m a b : ℕ) (o : PortalOrientation) (j : ℕ) : List ℕ :=
  match o with
  | .mab => (R ++ [m]).rotate j ++ [a, b]
  | .mba => (R ++ [m]).rotate j ++ [b, a]
  | .abm => (R ++ [a]).rotate j ++ [b, m]
  | .amb => (R ++ [a]).rotate j ++ [m, b]
  | .bma => (R ++ [b]).rotate j ++ [m, a]
  | .bam => (R ++ [b]).rotate j ++ [a, m]

/--
若权三边界源词为 `m,a,c,V`，则目标起始词必为尾部三字母的六种排列之一，并
由 `PortalOrientation` 唯一记录所选分支。
-/
theorem weightThreeTarget_normalizes_from_head
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} {target : ℕ}
    {V : List ℕ} {m a c : ℕ}
    (hV : V.length = k - 3)
    (hsource : (p.vert (k * target - 1) : List ℕ) = m :: a :: c :: V)
    (hweight : Hunter.ProofsLedger.bw p target = 3) :
    ∃ o : PortalOrientation,
      Hunter.ProofsChartEq.blockWord p target =
        orientedSuccessorStartWord V m a c o 0 := by
  have hsourcePerm : IsPermWord (V.length + 3)
      (Hunter.ProofsClosure3.finalExit V c a m) := by
    have hpw : IsPermWord k (m :: a :: c :: V) := by
      rw [← hsource]
      exact (p.vert (k * target - 1)).2
    rw [hV, show k - 3 + 3 = k by omega]
    simpa [Hunter.ProofsClosure3.finalExit] using hpw
  have htargetPerm : IsPermWord (V.length + 3)
      (Hunter.ProofsChartEq.blockWord p target) := by
    rw [hV, show k - 3 + 3 = k by omega]
    exact Hunter.ProofsChartEq.blockWord_isPermWord p target
  have hoverRaw := (wt_spec
    (u := (p.vert (k * target - 1) : List ℕ))
    (v := Hunter.ProofsChartEq.blockWord p target)
    (by omega : 1 ≤ k)
    (le_of_eq (p.vert (k * target - 1)).2.length)).2.2
  have hweight' : wt k (p.vert (k * target - 1) : List ℕ)
      (Hunter.ProofsChartEq.blockWord p target) = 3 := by
    exact hweight
  rw [hweight'] at hoverRaw
  have hover : (Hunter.ProofsClosure3.finalExit V c a m).drop 3 =
      (Hunter.ProofsChartEq.blockWord p target).take (V.length + 3 - 3) := by
    rw [show Hunter.ProofsClosure3.finalExit V c a m = m :: a :: c :: V by rfl,
      ← hsource, hV]
    exact hoverRaw
  rcases Hunter.ProofsClosure3.w3_six_cases V c a m hsourcePerm htargetPerm hover with
    hcam | hcma | hacm | hamc | hmca | hmac
  · exact ⟨.bam, by simpa [orientedSuccessorStartWord] using hcam⟩
  · exact ⟨.bma, by simpa [orientedSuccessorStartWord] using hcma⟩
  · exact ⟨.abm, by simpa [orientedSuccessorStartWord] using hacm⟩
  · exact ⟨.amb, by simpa [orientedSuccessorStartWord] using hamc⟩
  · exact ⟨.mba, by simpa [orientedSuccessorStartWord] using hmca⟩
  · exact ⟨.mab, by simpa [orientedSuccessorStartWord] using hmac⟩

/-- 候选满片的实际第 `l` 个块与附录 incidence word 表示同一旋转类。 -/
theorem orientedSuccessor_block_incidence_class
    (R : List ℕ) (m a b : ℕ) (o : PortalOrientation) (j l : ℕ) :
    rotClass
        (match o with
        | .mab => (((R ++ [m]).rotate j ++ [a]).rotate l) ++ [b]
        | .mba => (((R ++ [m]).rotate j ++ [b]).rotate l) ++ [a]
        | .abm => (((R ++ [a]).rotate j ++ [b]).rotate l) ++ [m]
        | .amb => (((R ++ [a]).rotate j ++ [m]).rotate l) ++ [b]
        | .bma => (((R ++ [b]).rotate j ++ [m]).rotate l) ++ [a]
        | .bam => (((R ++ [b]).rotate j ++ [a]).rotate l) ++ [m]) =
      rotClass (orientedSuccessorIncidenceWord R m a b o j l) := by
  cases o <;> simp only [orientedSuccessorIncidenceWord, successorIncidenceWord] <;>
    apply rotClass_append_marker

/--
真实权三满片游程一旦首片采用某个附录方向，其每一片起点都等于相应的第 `j`
个候选词。
-/
theorem weightThreeFullRun_start_words
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start M : ℕ} {R : List ℕ} {m a b : ℕ} {o : PortalOrientation}
    (hR : R.length = k - 3) (hrun : WeightThreeFullRun p start M)
    (hzero : Hunter.ProofsChartEq.blockWord p start =
      orientedSuccessorStartWord R m a b o 0) :
    ∀ j, j < M → Hunter.ProofsChartEq.blockWord p
      (start + j * (R.length + 2)) =
        orientedSuccessorStartWord R m a b o j := by
  have hperiod : R.length + 2 = k - 1 := by rw [hR]; omega
  have go : ∀ pp qq tt : ℕ,
      Hunter.ProofsChartEq.blockWord p start = R ++ [pp, qq, tt] →
      ∀ j, j < M → Hunter.ProofsChartEq.blockWord p
        (start + j * (R.length + 2)) = (R ++ [pp]).rotate j ++ [qq, tt] := by
    intro pp qq tt hstart
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
        have hjm : j < M := by omega
        have hprev := ih hjm
        let pieceStart := start + j * (R.length + 2)
        let A := (R ++ [pp]).rotate j
        have hA : A.length = k - 2 := by
          dsimp [A]
          rw [List.length_rotate, List.length_append, hR]
          simp
          omega
        have hnextIndex : pieceStart + (k - 1) =
            start + (j + 1) * (R.length + 2) := by
          dsimp [pieceStart]
          rw [hperiod, Nat.add_mul]
          omega
        have hnextBlockLt : start + (j + 1) * (R.length + 2) <
            start + M * (k - 1) := by
          rw [← hperiod]
          have hmul := Nat.mul_lt_mul_of_pos_right hj (by omega : 0 < R.length + 2)
          omega
        have hnextRange : k * (pieceStart + (k - 1)) < p.numVerts := by
          rw [hnextIndex]
          have hmul := Nat.mul_lt_mul_of_pos_left hnextBlockLt (by omega : 0 < k)
          exact lt_of_lt_of_le hmul hrun.inRange
        have hdoors : ∀ r, 1 ≤ r → r ≤ k - 2 →
            Hunter.ProofsLedger.IsDoor p (pieceStart + r) := by
          intro r hr1 hr2
          dsimp [pieceStart]
          rw [hperiod]
          simpa [Nat.add_assoc] using hrun.doors j r hjm hr1 hr2
        have halpha := weightThreeFullRun_seam_isAlpha (by omega : 3 ≤ k) hp hrun
          (c := j + 1) (by omega) hj
        have halpha' : Hunter.ProofsLedger.IsAlpha p (pieceStart + (k - 1)) := by
          rw [hnextIndex]
          rw [hperiod]
          exact halpha
        have hpieceStart : Hunter.ProofsChartEq.blockWord p pieceStart = A ++ [qq, tt] := by
          dsimp [pieceStart, A]
          exact hprev
        have hnext := fullPiece_alpha_next_start (by omega : 3 ≤ k) hp hA
          hnextRange hdoors hpieceStart halpha'
        rw [hnextIndex] at hnext
        dsimp [A] at hnext
        rw [List.rotate_rotate] at hnext
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnext
  cases o with
  | mab =>
      apply go m a b
      simpa [orientedSuccessorStartWord] using hzero
  | mba =>
      apply go m b a
      simpa [orientedSuccessorStartWord] using hzero
  | abm =>
      apply go a b m
      simpa [orientedSuccessorStartWord] using hzero
  | amb =>
      apply go a m b
      simpa [orientedSuccessorStartWord] using hzero
  | bma =>
      apply go b m a
      simpa [orientedSuccessorStartWord] using hzero
  | bam =>
      apply go b a m
      simpa [orientedSuccessorStartWord] using hzero

/-- 真实满片游程的全部块旋转类等于附录候选 incidence 坐标。 -/
theorem weightThreeFullRun_block_classes
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {start M : ℕ} {R : List ℕ} {m a b : ℕ} {o : PortalOrientation}
    (hR : R.length = k - 3) (hrun : WeightThreeFullRun p start M)
    (hzero : Hunter.ProofsChartEq.blockWord p start =
      orientedSuccessorStartWord R m a b o 0) :
    ∀ j, j < M → ∀ l, l < R.length + 2 →
      rotClass (Hunter.ProofsChartEq.blockWord p
        (start + j * (R.length + 2) + l)) =
      rotClass (orientedSuccessorIncidenceWord R m a b o j l) := by
  have hperiod : R.length + 2 = k - 1 := by rw [hR]; omega
  have hstarts := weightThreeFullRun_start_words hk hp hR hrun hzero
  intro j hj l hl
  let pieceStart := start + j * (R.length + 2)
  have hjEnd : pieceStart + (k - 2) < start + M * (k - 1) := by
    dsimp [pieceStart]
    have hjSucc : j + 1 ≤ M := by omega
    have hmul := Nat.mul_le_mul_right (k - 1) hjSucc
    rw [Nat.add_mul] at hmul
    rw [← hperiod] at hmul ⊢
    omega
  have hlastRange : k * (pieceStart + (k - 2)) < p.numVerts := by
    have hmul := Nat.mul_lt_mul_of_pos_left hjEnd (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hrun.inRange
  have hdoors : ∀ r, 1 ≤ r → r ≤ k - 2 →
      Hunter.ProofsLedger.IsDoor p (pieceStart + r) := by
    intro r hr1 hr2
    dsimp [pieceStart]
    rw [hperiod]
    simpa [Nat.add_assoc] using hrun.doors j r hj hr1 hr2
  have hlPeriod := hl
  rw [hperiod] at hlPeriod
  have hl' : l ≤ k - 2 := by omega
  have hstartWord := hstarts j hj
  cases o with
  | mab =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [m]).rotate j) (q := a) (t := b)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [m]).rotate j) ++ [a]).rotate l) ++ [b]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .mab j l) :=
          orientedSuccessor_block_incidence_class R m a b .mab j l
  | mba =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [m]).rotate j) (q := b) (t := a)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [m]).rotate j) ++ [b]).rotate l) ++ [a]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .mba j l) :=
          orientedSuccessor_block_incidence_class R m a b .mba j l
  | abm =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [a]).rotate j) (q := b) (t := m)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [a]).rotate j) ++ [b]).rotate l) ++ [m]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .abm j l) :=
          orientedSuccessor_block_incidence_class R m a b .abm j l
  | amb =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [a]).rotate j) (q := m) (t := b)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [a]).rotate j) ++ [m]).rotate l) ++ [b]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .amb j l) :=
          orientedSuccessor_block_incidence_class R m a b .amb j l
  | bma =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [b]).rotate j) (q := m) (t := a)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [b]).rotate j) ++ [m]).rotate l) ++ [a]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .bma j l) :=
          orientedSuccessor_block_incidence_class R m a b .bma j l
  | bam =>
      have hw := fullPiece_block_word (by omega : 3 ≤ k) hp
        (A := (R ++ [b]).rotate j) (q := a) (t := m)
        (by rw [List.length_rotate, List.length_append, hR]; simp; omega)
        hl' hlastRange hdoors (by
          dsimp [pieceStart]
          simpa [orientedSuccessorStartWord] using hstartWord)
      calc
        rotClass (Hunter.ProofsChartEq.blockWord p
            (start + j * (R.length + 2) + l)) =
            rotClass (((((R ++ [b]).rotate j) ++ [a]).rotate l) ++ [m]) := by
          simpa [pieceStart, Nat.add_assoc] using congrArg rotClass hw
        _ = rotClass (orientedSuccessorIncidenceWord R m a b .bam j l) :=
          orientedSuccessor_block_incidence_class R m a b .bam j l

/--
端点部分片与其后 `M` 个候选满片的局部不交条件。碰撞证明只需部分片的端点 incidence
`0` 与首个遗漏弧之后的 incidence `delta+1`。
-/
def EndpointCoordinateDisjoint
    (R : List ℕ) (m a b delta : ℕ) (o : PortalOrientation) (M : ℕ) : Prop :=
  ∀ j, j < M → ∀ l, l < R.length + 2 →
    rotClass (partialIncidenceWord R m a b 0) ≠
      rotClass (orientedSuccessorIncidenceWord R m a b o j l) ∧
    rotClass (partialIncidenceWord R m a b (delta + 1)) ≠
      rotClass (orientedSuccessorIncidenceWord R m a b o j l)

/--
附录六行碰撞表的统一推论：任何与部分片支持不交的端点满游程至多含 `|R|`
个满片；当 `|R|=k-3` 时即正文局部结论 (iii)。
-/
theorem endpointFullRun_length_le_coordinates
    (R : List ℕ) (m a b delta M : ℕ) (o : PortalOrientation)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1)
    (hdisjoint : EndpointCoordinateDisjoint R m a b delta o M) :
    M ≤ R.length := by
  by_contra hle
  push Not at hle
  cases o with
  | mab =>
      have h := (hdisjoint 0 (by omega) 0 (by omega)).1
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_mab R m a b)
  | mba =>
      have h := (hdisjoint 0 (by omega) (R.length + 1) (by omega)).1
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_mba R m a b)
  | abm =>
      have h := (hdisjoint 0 (by omega) (delta - 1) (by omega)).2
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_abm R m a b delta hdelta)
  | amb =>
      have hj : delta - 1 < M := by omega
      have hl : R.length + 2 - delta < R.length + 2 := by omega
      have h := (hdisjoint (delta - 1) hj (R.length + 2 - delta) hl).2
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_amb R m a b delta hdelta hdeltaMax)
  | bma =>
      have hj : delta - 1 < M := by omega
      have hl : R.length + 1 - delta < R.length + 2 := by omega
      have h := (hdisjoint (delta - 1) hj (R.length + 1 - delta) hl).2
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_bma R m a b delta hdelta hdeltaMax)
  | bam =>
      have h := (hdisjoint R.length hle delta (by omega)).2
      exact h (by simpa [orientedSuccessorIncidenceWord] using
        portalCollision_bam R m a b delta)

/--
单位缺口之后只要确实出现一个满片，六种权三方向中只有 `(b,a,m)` 不会立刻撞回
部分片。这个结论不使用长度反证，只使用碰撞表的前五行。
-/
theorem unitPositiveRun_orientation_bam_coordinates
    (R : List ℕ) (m a b M : ℕ) (o : PortalOrientation)
    (hM : 1 ≤ M)
    (hdisjoint : EndpointCoordinateDisjoint R m a b 1 o M) :
    o = .bam := by
  cases o with
  | mab =>
      have h := (hdisjoint 0 (by omega) 0 (by omega)).1
      exfalso
      apply h
      simpa [orientedSuccessorIncidenceWord] using portalCollision_mab R m a b
  | mba =>
      have h := (hdisjoint 0 (by omega) (R.length + 1) (by omega)).1
      exfalso
      apply h
      simpa [orientedSuccessorIncidenceWord] using portalCollision_mba R m a b
  | abm =>
      have h := (hdisjoint 0 (by omega) 0 (by omega)).2
      exfalso
      apply h
      simpa [orientedSuccessorIncidenceWord] using
        portalCollision_abm R m a b 1 (by omega)
  | amb =>
      have h := (hdisjoint 0 (by omega) (R.length + 1) (by omega)).2
      exfalso
      apply h
      simpa [orientedSuccessorIncidenceWord] using
        portalCollision_amb R m a b 1 (by omega) (by omega)
  | bma =>
      have h := (hdisjoint 0 (by omega) R.length (by omega)).2
      exfalso
      apply h
      simpa [orientedSuccessorIncidenceWord] using
        portalCollision_bma R m a b 1 (by omega) (by omega)
  | bam => rfl

/--
端点满游程达到 `|R|` 片且左缺口不超过 `|R|` 时，前五种方向都会在游程结束前
撞回左部分片，因此唯一方向为 `(b,a,m)`。
-/
theorem maximalRun_orientation_bam_coordinates
    (R : List ℕ) (m a b delta M : ℕ) (o : PortalOrientation)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length)
    (hM : R.length ≤ M)
    (hdisjoint : EndpointCoordinateDisjoint R m a b delta o M) :
    o = .bam := by
  cases o with
  | mab =>
      exfalso
      exact (hdisjoint 0 (by omega) 0 (by omega)).1
        (by simpa [orientedSuccessorIncidenceWord] using portalCollision_mab R m a b)
  | mba =>
      exfalso
      exact (hdisjoint 0 (by omega) (R.length + 1) (by omega)).1
        (by simpa [orientedSuccessorIncidenceWord] using portalCollision_mba R m a b)
  | abm =>
      exfalso
      exact (hdisjoint 0 (by omega) (delta - 1) (by omega)).2
        (by simpa [orientedSuccessorIncidenceWord] using
          portalCollision_abm R m a b delta hdelta)
  | amb =>
      exfalso
      exact (hdisjoint (delta - 1) (by omega)
          (R.length + 2 - delta) (by omega)).2
        (by simpa [orientedSuccessorIncidenceWord] using
          portalCollision_amb R m a b delta hdelta (by omega))
  | bma =>
      exfalso
      exact (hdisjoint (delta - 1) (by omega)
          (R.length + 1 - delta) (by omega)).2
        (by simpa [orientedSuccessorIncidenceWord] using
          portalCollision_bma R m a b delta hdelta (by omega))
  | bam => rfl

/-- 正文记号下的一般端点界：`|R|=k-3` 时满游程长度至多 `k-3`。 -/
theorem endpointFullRun_length_le_km3_coordinates
    {k : ℕ} (R : List ℕ) (m a b delta M : ℕ) (o : PortalOrientation)
    (hR : R.length = k - 3)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1)
    (hdisjoint : EndpointCoordinateDisjoint R m a b delta o M) :
    M ≤ k - 3 := by
  rw [← hR]
  exact endpointFullRun_length_le_coordinates R m a b delta M o
    hdelta hdeltaMax hdisjoint

/-! ## 实际“部分片后接满游程”的自动坐标化 -/

/-- 一个实际部分片经精确权三接缝后接正满游程。 -/
structure PartialThenFullRun
    {k : ℕ} (p : HPath k) (partialStart delta M : ℕ) : Prop where
  deltaPos : 1 ≤ delta
  deltaMax : delta ≤ k - 2
  runPos : 1 ≤ M
  partialDoors : ∀ r, 1 ≤ r → r ≤ k - 2 - delta →
    Hunter.ProofsLedger.IsDoor p (partialStart + r)
  seamWeight : Hunter.ProofsLedger.bw p
    (partialStart + (k - 1 - delta)) = 3
  fullRun : WeightThreeFullRun p
    (partialStart + (k - 1 - delta)) M

/--
实际部分片—满游程配置自动产生附录标准坐标。返回的两个部分片旋转类等式和首片
方向正是 `endpointRunPathCoordinates_of_normalized` 所需接口。
-/
theorem partialThenFullRun_normalizes
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart delta M : ℕ} (hcfg : PartialThenFullRun p partialStart delta M) :
    ∃ (R : List ℕ) (m a b : ℕ) (o : PortalOrientation),
      R.length = k - 3 ∧
      Hunter.ProofsChartEq.blockWord p partialStart =
        (a :: b :: R).rotate (delta + 1) ++ [m] ∧
      Hunter.ProofsChartEq.blockWord p (partialStart + (k - 1 - delta)) =
        orientedSuccessorStartWord R m a b o 0 ∧
      rotClass (Hunter.ProofsChartEq.blockWord p
        (partialStart + (R.length + 1 - delta))) =
        rotClass (partialIncidenceWord R m a b 0) ∧
      rotClass (Hunter.ProofsChartEq.blockWord p partialStart) =
        rotClass (partialIncidenceWord R m a b (delta + 1)) := by
  let fullStart := partialStart + (k - 1 - delta)
  let lastPartial := partialStart + (k - 2 - delta)
  let root := Hunter.ProofsChartEq.blockWord p partialStart
  let m := root.getLastD 0
  let base := root.dropLast
  have hperiodPos : 1 ≤ k - 1 := by omega
  have hfullEndPos : fullStart < fullStart + M * (k - 1) := by
    have : 1 ≤ M * (k - 1) := Nat.mul_pos hcfg.runPos hperiodPos
    omega
  have hfullStartRange : k * fullStart < p.numVerts := by
    have hmul := Nat.mul_lt_mul_of_pos_left hfullEndPos (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hcfg.fullRun.inRange
  have hlastBefore : lastPartial < fullStart := by
    have hdeltaMax := hcfg.deltaMax
    dsimp [lastPartial, fullStart]
    omega
  have hlastRange : k * lastPartial < p.numVerts :=
    lt_of_le_of_lt (Nat.mul_le_mul_left k (Nat.le_of_lt hlastBefore)) hfullStartRange
  have hrootNodup : root.Nodup :=
    (Hunter.ProofsChartEq.blockWord_isPermWord p partialStart).nodup
  have hrootNe : root ≠ [] := by
    intro hnil
    have hlen := (Hunter.ProofsChartEq.blockWord_isPermWord p partialStart).length
    change root.length = k at hlen
    rw [hnil] at hlen
    simp at hlen
    omega
  have hrootSplit : root = base ++ [m] := by
    dsimp [base, m]
    calc
      root = root.erase (root.getLastD 0) ++ [root.getLastD 0] :=
        Hunter.ProofsFillPath.marker_reconstruct hrootNodup hrootNe
      _ = root.dropLast ++ [root.getLastD 0] := by
        rw [Hunter.ProofsConfinement.erase_getLastD hrootNodup]
  have hbaseLen : base.length = k - 1 := by
    dsimp [base]
    rw [List.length_dropLast,
      (Hunter.ProofsChartEq.blockWord_isPermWord p partialStart).length]
  have hpartialRun := Hunter.ProofsFillPath.blockrun_eq (by omega : 2 ≤ k) hp
    partialStart (k - 2 - delta) (by
      change k * (partialStart + (k - 2 - delta)) < p.numVerts
      exact hlastRange) (by
        intro r hr1 hr2
        simpa [Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] using
          hcfg.partialDoors r hr1 hr2)
  have hlastRaw := hpartialRun (k - 2 - delta) (le_refl _)
  change Hunter.ProofsChartEq.blockWord p lastPartial = _ at hlastRaw
  have hrootVal : (p.vert (k * partialStart) : List ℕ) = root := rfl
  rw [hrootVal, Hunter.ProofsConfinement.erase_getLastD hrootNodup] at hlastRaw
  have hlastWord : Hunter.ProofsChartEq.blockWord p lastPartial =
      base.rotate (k - 2 - delta) ++ [m] := by
    simpa [base, m] using hlastRaw
  have hfullStartPos : 1 ≤ fullStart := by
    dsimp [fullStart]
    have : 1 ≤ k - 1 - delta := by omega
    omega
  have hsource := blockBoundarySource_eq_bexit (by omega : 1 ≤ k) hp
    hfullStartPos hfullStartRange
  have hprev : fullStart - 1 = lastPartial := by
    dsimp [fullStart, lastPartial]
    omega
  rw [hprev, hlastWord] at hsource
  have hbexit : Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 2 - delta) ++ [m]) =
      m :: base.rotate (k - 2 - delta) := by
    unfold Hunter.ProofsRigidity2.bexit
    rw [show k - 1 = (base.rotate (k - 2 - delta)).length by
      rw [List.length_rotate, hbaseLen], List.rotate_append_length_eq]
    rfl
  rw [hbexit] at hsource
  obtain ⟨a, b, R, htail⟩ : ∃ a b R,
      base.rotate (k - 2 - delta) = a :: b :: R := by
    have hlen : (base.rotate (k - 2 - delta)).length = k - 1 := by
      rw [List.length_rotate, hbaseLen]
    rcases hword : base.rotate (k - 2 - delta) with _ | ⟨a, rest⟩
    · rw [hword] at hlen
      simp at hlen
      omega
    · rcases rest with _ | ⟨b, R⟩
      · rw [hword] at hlen
        simp at hlen
        omega
      · exact ⟨a, b, R, rfl⟩
  have hR : R.length = k - 3 := by
    have hlen := congrArg List.length htail
    rw [List.length_rotate, hbaseLen] at hlen
    simp at hlen
    omega
  have hsourceWord : (p.vert (k * fullStart - 1) : List ℕ) = m :: a :: b :: R := by
    rw [hsource, htail]
  have hzeroIndex : partialStart + (R.length + 1 - delta) = lastPartial := by
    dsimp [lastPartial]
    rw [hR]
    omega
  have hpartialZero :
      rotClass (Hunter.ProofsChartEq.blockWord p
        (partialStart + (R.length + 1 - delta))) =
        rotClass (partialIncidenceWord R m a b 0) := by
    rw [hzeroIndex, hlastWord]
    calc
      rotClass (base.rotate (k - 2 - delta) ++ [m]) =
          rotClass (m :: base.rotate (k - 2 - delta)) :=
        rotClass_append_marker _ _
      _ = rotClass (partialIncidenceWord R m a b 0) := by
        rw [htail]
        simp [partialIncidenceWord]
  have hsum : (k - 2 - delta) + (delta + 1) = base.length := by
    rw [hbaseLen]
    omega
  have hrotateBack : (a :: b :: R).rotate (delta + 1) = base := by
    rw [← htail, List.rotate_rotate, hsum, List.rotate_length]
  have hpartialDelta :
      rotClass (Hunter.ProofsChartEq.blockWord p partialStart) =
        rotClass (partialIncidenceWord R m a b (delta + 1)) := by
    rw [show Hunter.ProofsChartEq.blockWord p partialStart = root from rfl,
      hrootSplit]
    calc
      rotClass (base ++ [m]) = rotClass (m :: base) := rotClass_append_marker _ _
      _ = rotClass (partialIncidenceWord R m a b (delta + 1)) := by
        rw [partialIncidenceWord, hrotateBack]
  have hpartialStartWord : Hunter.ProofsChartEq.blockWord p partialStart =
      (a :: b :: R).rotate (delta + 1) ++ [m] := by
    rw [show Hunter.ProofsChartEq.blockWord p partialStart = root from rfl,
      hrootSplit, hrotateBack]
  have hsourcePerm : IsPermWord (R.length + 3)
      (Hunter.ProofsClosure3.finalExit R b a m) := by
    have hpw : IsPermWord k (m :: a :: b :: R) := by
      rw [← hsourceWord]
      exact (p.vert (k * fullStart - 1)).2
    rw [hR, show k - 3 + 3 = k by omega]
    simpa [Hunter.ProofsClosure3.finalExit] using hpw
  have htargetPerm : IsPermWord (R.length + 3)
      (Hunter.ProofsChartEq.blockWord p fullStart) := by
    rw [hR, show k - 3 + 3 = k by omega]
    exact Hunter.ProofsChartEq.blockWord_isPermWord p fullStart
  have hweight : wt k (p.vert (k * fullStart - 1) : List ℕ)
      (Hunter.ProofsChartEq.blockWord p fullStart) = 3 := by
    exact hcfg.seamWeight
  have hoverRaw := (wt_spec (u := (p.vert (k * fullStart - 1) : List ℕ))
    (v := Hunter.ProofsChartEq.blockWord p fullStart) (by omega : 1 ≤ k)
    (le_of_eq (p.vert (k * fullStart - 1)).2.length)).2.2
  rw [hweight] at hoverRaw
  have hover : (Hunter.ProofsClosure3.finalExit R b a m).drop 3 =
      (Hunter.ProofsChartEq.blockWord p fullStart).take (R.length + 3 - 3) := by
    rw [show Hunter.ProofsClosure3.finalExit R b a m = m :: a :: b :: R by rfl,
      ← hsourceWord, hR]
    exact hoverRaw
  have hcases := Hunter.ProofsClosure3.w3_six_cases R b a m hsourcePerm
    htargetPerm hover
  rcases hcases with hbam | hbma | habm | hamb | hmba | hmab
  · exact ⟨R, m, a, b, .bam, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using hbam, hpartialZero,
      hpartialDelta⟩
  · exact ⟨R, m, a, b, .bma, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using hbma, hpartialZero,
      hpartialDelta⟩
  · exact ⟨R, m, a, b, .abm, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using habm, hpartialZero,
      hpartialDelta⟩
  · exact ⟨R, m, a, b, .amb, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using hamb, hpartialZero,
      hpartialDelta⟩
  · exact ⟨R, m, a, b, .mba, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using hmba, hpartialZero,
      hpartialDelta⟩
  · exact ⟨R, m, a, b, .mab, hR, hpartialStartWord, by
      simpa [fullStart, orientedSuccessorStartWord] using hmab, hpartialZero,
      hpartialDelta⟩

/-! ## 坐标证书到真实路径不重入的桥 -/

/--
端点部分片及其后满游程在真实 `HPath` 块序列中的坐标证书。部分片按附录坐标依次
访问 `delta+1,…,n-1,0`；满片 `j` 的全部 `n=|R|+2` 个 incidence 由连续块给出。
-/
structure EndpointRunPathCoordinates
    {k : ℕ} (p : HPath k) (partialStart fullStart : ℕ)
    (R : List ℕ) (m a b delta : ℕ) (o : PortalOrientation) (M : ℕ) : Prop where
  deltaPos : 1 ≤ delta
  deltaMax : delta ≤ R.length + 1
  partialZeroBefore : partialStart + (R.length + 1 - delta) < fullStart
  partialZeroRange :
    k * (partialStart + (R.length + 1 - delta)) < p.numVerts
  partialDeltaRange : k * partialStart < p.numVerts
  fullRange : ∀ j, j < M → ∀ l, l < R.length + 2 →
    k * (fullStart + j * (R.length + 2) + l) < p.numVerts
  partialZeroClass :
    rotClass (Hunter.ProofsChartEq.blockWord p
      (partialStart + (R.length + 1 - delta))) =
      rotClass (partialIncidenceWord R m a b 0)
  partialDeltaClass :
    rotClass (Hunter.ProofsChartEq.blockWord p partialStart) =
      rotClass (partialIncidenceWord R m a b (delta + 1))
  fullClass : ∀ j, j < M → ∀ l, l < R.length + 2 →
    rotClass (Hunter.ProofsChartEq.blockWord p
      (fullStart + j * (R.length + 2) + l)) =
      rotClass (orientedSuccessorIncidenceWord R m a b o j l)

/--
由标准化的部分片两端坐标、首个权三后继方向以及真实满游程，自动组装完整路径
坐标证书。
-/
theorem endpointRunPathCoordinates_of_normalized
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart fullStart M : ℕ} {R : List ℕ} {m a b delta : ℕ}
    {o : PortalOrientation}
    (hR : R.length = k - 3)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1)
    (hfullStart : fullStart = partialStart + (R.length + 2 - delta))
    (hM : 1 ≤ M) (hrun : WeightThreeFullRun p fullStart M)
    (hzero : Hunter.ProofsChartEq.blockWord p fullStart =
      orientedSuccessorStartWord R m a b o 0)
    (hpartialZero :
      rotClass (Hunter.ProofsChartEq.blockWord p
        (partialStart + (R.length + 1 - delta))) =
        rotClass (partialIncidenceWord R m a b 0))
    (hpartialDelta :
      rotClass (Hunter.ProofsChartEq.blockWord p partialStart) =
        rotClass (partialIncidenceWord R m a b (delta + 1))) :
    EndpointRunPathCoordinates p partialStart fullStart R m a b delta o M := by
  have hperiod : R.length + 2 = k - 1 := by rw [hR]; omega
  have hfullEndPos : fullStart < fullStart + M * (k - 1) := by
    have hmul : 1 ≤ M * (k - 1) := Nat.mul_pos hM (by omega)
    omega
  have hfullStartRange : k * fullStart < p.numVerts := by
    have hmul := Nat.mul_lt_mul_of_pos_left hfullEndPos (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hrun.inRange
  refine
    { deltaPos := hdelta
      deltaMax := hdeltaMax
      partialZeroBefore := ?_
      partialZeroRange := ?_
      partialDeltaRange := ?_
      fullRange := ?_
      partialZeroClass := hpartialZero
      partialDeltaClass := hpartialDelta
      fullClass := ?_ }
  · rw [hfullStart]
    omega
  · have hbefore : partialStart + (R.length + 1 - delta) < fullStart := by
      rw [hfullStart]
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k (Nat.le_of_lt hbefore)) hfullStartRange
  · have hbefore : partialStart < fullStart := by
      rw [hfullStart]
      have : 1 ≤ R.length + 2 - delta := by omega
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k (Nat.le_of_lt hbefore)) hfullStartRange
  · intro j hj l hl
    have hindex : fullStart + j * (R.length + 2) + l <
        fullStart + M * (k - 1) := by
      rw [← hperiod]
      have hjSucc : j + 1 ≤ M := by omega
      have hmul := Nat.mul_le_mul_right (R.length + 2) hjSucc
      rw [Nat.add_mul] at hmul
      omega
    have hmul := Nat.mul_lt_mul_of_pos_left hindex (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hrun.inRange
  · exact weightThreeFullRun_block_classes hk hp hR hrun hzero

/-- 路径块不重入把坐标证书自动变成端点支持不交证书。 -/
theorem endpointCoordinateDisjoint_of_path
    {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart fullStart : ℕ} {R : List ℕ} {m a b delta M : ℕ}
    {o : PortalOrientation}
    (hcoord : EndpointRunPathCoordinates p partialStart fullStart
      R m a b delta o M) :
    EndpointCoordinateDisjoint R m a b delta o M := by
  intro j hj l hl
  have hfullRange := hcoord.fullRange j hj l hl
  have hpartialDeltaBefore : partialStart < fullStart := by
    exact lt_of_le_of_lt (Nat.le_add_right partialStart _) hcoord.partialZeroBefore
  have hzeroNe :
      partialStart + (R.length + 1 - delta) ≠
        fullStart + j * (R.length + 2) + l := by
    apply Nat.ne_of_lt
    exact lt_of_lt_of_le hcoord.partialZeroBefore
      (by simpa [Nat.add_assoc] using
        Nat.le_add_right fullStart (j * (R.length + 2) + l))
  have hdeltaNe : partialStart ≠
      fullStart + j * (R.length + 2) + l := by
    apply Nat.ne_of_lt
    exact lt_of_lt_of_le hpartialDeltaBefore
      (by simpa [Nat.add_assoc] using
        Nat.le_add_right fullStart (j * (R.length + 2) + l))
  have hzero := Hunter.ProofsChartEq.blockWord_distinct hk hp
    hcoord.partialZeroRange hfullRange hzeroNe
  have hdelta := Hunter.ProofsChartEq.blockWord_distinct hk hp
    hcoord.partialDeltaRange hfullRange hdeltaNe
  rw [hcoord.partialZeroClass, hcoord.fullClass j hj l hl] at hzero
  rw [hcoord.partialDeltaClass, hcoord.fullClass j hj l hl] at hdelta
  exact ⟨hzero, hdelta⟩

/--
一旦实际路径分片已产生上述坐标证书，一般端点满游程界由 `no_reentry` 与六行
碰撞表直接闭合。
-/
theorem endpointFullRun_length_le_of_pathCoordinates
    {k : ℕ} (hk : 1 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart fullStart : ℕ} {R : List ℕ} {m a b delta M : ℕ}
    {o : PortalOrientation}
    (hcoord : EndpointRunPathCoordinates p partialStart fullStart
      R m a b delta o M) :
    M ≤ R.length := by
  exact endpointFullRun_length_le_coordinates R m a b delta M o
    hcoord.deltaPos hcoord.deltaMax
    (endpointCoordinateDisjoint_of_path hk hp hcoord)

/-- 标准化端点配置的真实路径满游程界。 -/
theorem endpointFullRun_length_le_of_normalized_path
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart fullStart M : ℕ} {R : List ℕ} {m a b delta : ℕ}
    {o : PortalOrientation}
    (hR : R.length = k - 3)
    (hdelta : 1 ≤ delta) (hdeltaMax : delta ≤ R.length + 1)
    (hfullStart : fullStart = partialStart + (R.length + 2 - delta))
    (hM : 1 ≤ M) (hrun : WeightThreeFullRun p fullStart M)
    (hzero : Hunter.ProofsChartEq.blockWord p fullStart =
      orientedSuccessorStartWord R m a b o 0)
    (hpartialZero :
      rotClass (Hunter.ProofsChartEq.blockWord p
        (partialStart + (R.length + 1 - delta))) =
        rotClass (partialIncidenceWord R m a b 0))
    (hpartialDelta :
      rotClass (Hunter.ProofsChartEq.blockWord p partialStart) =
        rotClass (partialIncidenceWord R m a b (delta + 1))) :
    M ≤ k - 3 := by
  rw [← hR]
  apply endpointFullRun_length_le_of_pathCoordinates (by omega : 1 ≤ k) hp
  exact endpointRunPathCoordinates_of_normalized hk hp hR hdelta hdeltaMax
    hfullStart hM hrun hzero hpartialZero hpartialDelta

/--
正文门户局部结论 (iii) 的真实前向版本：任意实际部分片之后的正满游程长度至多
`k-3`。六方向、支持不交和坐标归一化均已由前述定理自动消去。
-/
theorem partialThenFullRun_length_le
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart delta M : ℕ} (hcfg : PartialThenFullRun p partialStart delta M) :
    M ≤ k - 3 := by
  obtain ⟨R, m, a, b, o, hR, _hpartialStartWord, hzero,
      hpartialZero, hpartialDelta⟩ :=
    partialThenFullRun_normalizes hk hp hcfg
  apply endpointFullRun_length_le_of_normalized_path hk hp
    (partialStart := partialStart)
    (fullStart := partialStart + (k - 1 - delta))
    (M := M) (R := R) (m := m) (a := a) (b := b) (delta := delta) (o := o) hR
  · exact hcfg.deltaPos
  · rw [hR]
    have := hcfg.deltaMax
    omega
  · rw [hR]
    omega
  · exact hcfg.runPos
  · exact hcfg.fullRun
  · exact hzero
  · exact hpartialZero
  · exact hpartialDelta

/--
实际单位缺口之后若有正满游程，则首个满片的词被唯一确定为 `R,b,a,m`；同时单位
缺口片本身从 `R,a,b,m` 开始。这是局部结论 (ii) 的路径级方向部分。
-/
theorem partialThenFullRun_unit_first_word
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {partialStart M : ℕ} (hcfg : PartialThenFullRun p partialStart 1 M) :
    ∃ (R : List ℕ) (m a b : ℕ),
      R.length = k - 3 ∧
      Hunter.ProofsChartEq.blockWord p partialStart = R ++ [a, b, m] ∧
      Hunter.ProofsChartEq.blockWord p (partialStart + (k - 2)) =
        R ++ [b, a, m] := by
  obtain ⟨R, m, a, b, o, hR, hpartialStart, hzero,
      hpartialZero, hpartialDelta⟩ :=
    partialThenFullRun_normalizes hk hp hcfg
  have hkSub : k - 1 - 1 = k - 2 := by omega
  have hrun := hcfg.fullRun
  rw [hkSub] at hrun hzero
  have hcoord : EndpointRunPathCoordinates p partialStart
      (partialStart + (k - 2)) R m a b 1 o M := by
    apply endpointRunPathCoordinates_of_normalized hk hp hR hcfg.deltaPos
    · rw [hR]
      omega
    · rw [hR]
      omega
    · exact hcfg.runPos
    · exact hrun
    · exact hzero
    · exact hpartialZero
    · exact hpartialDelta
  have ho : o = .bam := unitPositiveRun_orientation_bam_coordinates
    R m a b M o hcfg.runPos
      (endpointCoordinateDisjoint_of_path (by omega : 1 ≤ k) hp hcoord)
  subst o
  refine ⟨R, m, a, b, hR, ?_, ?_⟩
  · rw [rotate_abR_two] at hpartialStart
    simpa [List.append_assoc] using hpartialStart
  · simpa [orientedSuccessorStartWord, List.append_assoc] using hzero

/--
正文门户局部结论 (ii)：一个单位缺口片不可能左侧由权三接缝接一个满片，同时右侧
又由权三接缝接一段非空满片游程。两侧强制出的同一块词会在两个不同块号重入。
-/
theorem unitDeficit_not_between_full_runs
    {k : ℕ} (hk : 4 ≤ k) {p : HPath k} (hp : p.Exitless)
    {leftStart M : ℕ}
    (hleft : FullIntervalPiece p leftStart)
    (hincoming : Hunter.ProofsLedger.bw p (leftStart + (k - 1)) = 3)
    (hright : PartialThenFullRun p (leftStart + (k - 1)) 1 M) : False := by
  let unitStart := leftStart + (k - 1)
  have hkSub : k - 1 - 1 = k - 2 := by omega
  have hdoorSub : k - 2 - 1 = k - 3 := by omega
  have hrun := hright.fullRun
  change WeightThreeFullRun p (unitStart + (k - 1 - 1)) M at hrun
  rw [hkSub] at hrun
  have hrightStartRange : k * (unitStart + (k - 2)) < p.numVerts := by
    have hperiodPos : 1 ≤ k - 1 := by omega
    have hbefore : unitStart + (k - 2) <
        unitStart + (k - 2) + M * (k - 1) := by
      have : 1 ≤ M * (k - 1) := Nat.mul_pos hright.runPos hperiodPos
      omega
    have hmul := Nat.mul_lt_mul_of_pos_left hbefore (by omega : 0 < k)
    exact lt_of_lt_of_le hmul hrun.inRange
  have hunit : UnitDeficitDoorSegment p unitStart := by
    refine ⟨hrightStartRange, ?_⟩
    intro i hi1 hi2
    have hdoor := hright.partialDoors i hi1 (by rw [hdoorSub]; exact hi2)
    simpa [unitStart] using hdoor
  have hunitPos : 1 ≤ unitStart := by
    dsimp [unitStart]
    omega
  have hsourceComplete0 := fullIntervalPiece_complete (by omega : 3 ≤ k) hp hleft
  have hsourceIndex : leftStart + (k - 2) = unitStart - 1 := by
    dsimp [unitStart]
    omega
  have hsourceComplete : Hunter.ProofsLedger.IsComplete p (unitStart - 1) := by
    rwa [hsourceIndex] at hsourceComplete0
  have halpha : Hunter.ProofsLedger.IsAlpha p unitStart :=
    weightThree_complete_to_unitDeficit_isAlpha hk hp hunitPos hunit
      (by simpa [unitStart] using hincoming) hsourceComplete
  obtain ⟨R, m, a, b, hR, hunitWord, hrightWord⟩ :=
    partialThenFullRun_unit_first_word hk hp hright
  let root := Hunter.ProofsChartEq.blockWord p leftStart
  let t := root.getLastD 0
  let B := root.dropLast
  let q := B.getLastD 0
  let A := B.dropLast
  have hrootLen : root.length = k := by
    exact (Hunter.ProofsChartEq.blockWord_isPermWord p leftStart).length
  have hrootNe : root ≠ [] := by
    intro hnil
    rw [hnil] at hrootLen
    simp at hrootLen
    omega
  have hrootSplit : root = B ++ [t] := by
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD root hrootNe
  have hBLen : B.length = k - 1 := by
    dsimp [B]
    rw [List.length_dropLast, hrootLen]
  have hBNe : B ≠ [] := by
    intro hnil
    rw [hnil] at hBLen
    simp at hBLen
    omega
  have hBSplit : B = A ++ [q] := by
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD B hBNe
  have hAlen : A.length = k - 2 := by
    dsimp [A]
    rw [List.length_dropLast, hBLen]
    exact hkSub
  have hleftStartWord : Hunter.ProofsChartEq.blockWord p leftStart = A ++ [q, t] := by
    change root = A ++ [q, t]
    rw [hrootSplit, hBSplit]
    simp [List.append_assoc]
  have hseamRange : k * (leftStart + (k - 1)) < p.numVerts := by
    have hle : leftStart + (k - 1) ≤ unitStart + (k - 2) := by
      dsimp [unitStart]
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k hle) hrightStartRange
  have hnext := fullPiece_alpha_next_start (by omega : 3 ≤ k) hp hAlen
    hseamRange hleft.doors hleftStartWord (by simpa [unitStart] using halpha)
  have htarget : A.rotate 1 ++ [q, t] = R ++ [a, b, m] := by
    exact hnext.symm.trans (by simpa [unitStart] using hunitWord)
  have hAR : A.length = R.length + 1 := by
    rw [hAlen, hR]
    omega
  have hsecondCoordinate : (A ++ [q]).rotate 1 ++ [t] = R ++ [b, a, m] :=
    fullPiece_second_word_of_alpha_target hAR htarget
  have hsecond := fullPiece_block_word (by omega : 3 ≤ k) hp hAlen
    (l := 1) (by omega) hleft.inRange hleft.doors hleftStartWord
  have hleftWord : Hunter.ProofsChartEq.blockWord p (leftStart + 1) =
      R ++ [b, a, m] := hsecond.trans hsecondCoordinate
  have hrightWord' : Hunter.ProofsChartEq.blockWord p (unitStart + (k - 2)) =
      R ++ [b, a, m] := by
    simpa [unitStart] using hrightWord
  have hleftRange : k * (leftStart + 1) < p.numVerts := by
    have hle : leftStart + 1 ≤ leftStart + (k - 2) := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k hle) hleft.inRange
  have hindexNe : leftStart + 1 ≠ unitStart + (k - 2) := by
    apply Nat.ne_of_lt
    dsimp [unitStart]
    omega
  have hdistinct := Hunter.ProofsChartEq.blockWord_distinct (by omega : 1 ≤ k) hp
    hleftRange hrightStartRange hindexNe
  apply hdistinct
  exact congrArg rotClass (hleftWord.trans hrightWord'.symm)

/-! ## 内部长满游程阈值的真实路径版本 -/

/-- 长满游程之后右部分片的起始块号。 -/
def internalLongRightStart (k leftStart leftDeficit : ℕ) : ℕ :=
  leftStart + (k - 1 - leftDeficit) + (k - 3) * (k - 1)

/-- 左部分片、`k-3` 个满片、右部分片组成的实际内部链配置。 -/
structure InternalLongFullRun
    {k : ℕ} (p : HPath k) (leftStart leftDeficit rightDeficit : ℕ) : Prop where
  left : PartialThenFullRun p leftStart leftDeficit (k - 3)
  rightDeficitPos : 1 ≤ rightDeficit
  rightDeficitMax : rightDeficit ≤ k - 2
  rightSeamWeight : Hunter.ProofsLedger.bw p
    (internalLongRightStart k leftStart leftDeficit) = 3
  rightDoors : ∀ r, 1 ≤ r → r ≤ k - 2 - rightDeficit →
    Hunter.ProofsLedger.IsDoor p
      (internalLongRightStart k leftStart leftDeficit + r)
  rightRange : k * (internalLongRightStart k leftStart leftDeficit +
    (k - 2 - rightDeficit)) < p.numVerts

/--
正文门户局部结论 (iv) 的真实必要方向：实际内部 `k-3` 满游程两侧的部分片缺口
之和至少为 `k-1`。
-/
theorem internalLongFullRun_deficit_threshold
    {k : ℕ} (hk : 5 ≤ k) {p : HPath k} (hp : p.Exitless)
    {leftStart leftDeficit rightDeficit : ℕ}
    (hcfg : InternalLongFullRun p leftStart leftDeficit rightDeficit) :
    k - 1 ≤ leftDeficit + rightDeficit := by
  by_contra hsum
  push Not at hsum
  obtain ⟨R, m, a, b, o, hR, _hleftStartWord, hzero,
      hpartialZero, hpartialDelta⟩ :=
    partialThenFullRun_normalizes (by omega : 4 ≤ k) hp hcfg.left
  let fullStart := leftStart + (k - 1 - leftDeficit)
  have hdeltaMaxR : leftDeficit ≤ R.length := by
    rw [hR]
    have := hcfg.rightDeficitPos
    omega
  have hfullStartEq : fullStart = leftStart + (R.length + 2 - leftDeficit) := by
    dsimp [fullStart]
    rw [hR]
    omega
  have hcoord : EndpointRunPathCoordinates p leftStart fullStart
      R m a b leftDeficit o (k - 3) := by
    apply endpointRunPathCoordinates_of_normalized (by omega : 4 ≤ k) hp hR
      hcfg.left.deltaPos
    · rw [hR]
      omega
    · exact hfullStartEq
    · exact hcfg.left.runPos
    · simpa [fullStart] using hcfg.left.fullRun
    · simpa [fullStart] using hzero
    · exact hpartialZero
    · exact hpartialDelta
  have ho : o = .bam := maximalRun_orientation_bam_coordinates
    R m a b leftDeficit (k - 3) o hcfg.left.deltaPos hdeltaMaxR
      (by rw [hR])
      (endpointCoordinateDisjoint_of_path (by omega : 1 ≤ k) hp hcoord)
  subst o
  let U := R.dropLast
  let c := R.getLastD 0
  have hRNe : R ≠ [] := by
    intro hnil
    rw [hnil] at hR
    simp at hR
    omega
  have hRsplit : R = U ++ [c] := by
    exact Hunter.ProofsSynthesis.list_dropLast_getLastD R hRNe
  have hU : U.length = k - 4 := by
    dsimp [U]
    rw [List.length_dropLast, hR]
    omega
  have hcount : U.length + 1 = k - 3 := by rw [hU]; omega
  have hperiod : U.length + 3 = k - 1 := by rw [hU]; omega
  let rightStart := internalLongRightStart k leftStart leftDeficit
  have hrightStartEq : rightStart = fullStart + (k - 3) * (k - 1) := by
    rfl
  have hrun : WeightThreeFullRun p fullStart (k - 3) := by
    simpa [fullStart] using hcfg.left.fullRun
  have hrightRange : k * (rightStart + (k - 2 - rightDeficit)) < p.numVerts := by
    simpa [rightStart] using hcfg.rightRange
  have hrightStartRange : k * rightStart < p.numVerts := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left k (Nat.le_add_right rightStart _)) hrightRange
  have hjLast : U.length < k - 3 := by rw [hU]; omega
  have hlastPiece := weightThreeFullRun_piece (by omega : 3 ≤ k) hrun hjLast
  have hstarts := weightThreeFullRun_start_words (by omega : 4 ≤ k) hp hR hrun
    (by simpa [fullStart] using hzero)
  have hlastStart0 := hstarts U.length hjLast
  have hRperiod : R.length + 2 = k - 1 := by rw [hR]; omega
  rw [hRperiod] at hlastStart0
  have hlastStart : Hunter.ProofsChartEq.blockWord p
      (fullStart + U.length * (k - 1)) =
        (R ++ [b]).rotate U.length ++ [a, m] := by
    simpa [orientedSuccessorStartWord] using hlastStart0
  have hAlast : ((R ++ [b]).rotate U.length).length = k - 2 := by
    rw [List.length_rotate, List.length_append, hR]
    simp
    omega
  have hlastWord0 := fullPiece_block_word (by omega : 3 ≤ k) hp hAlast
    (l := k - 2) (by omega) hlastPiece.inRange hlastPiece.doors hlastStart
  have hprevIndex : rightStart - 1 =
      fullStart + U.length * (k - 1) + (k - 2) := by
    rw [hrightStartEq, hU,
      show k - 3 = (k - 4) + 1 by omega, Nat.add_mul]
    omega
  have hlastWord : Hunter.ProofsChartEq.blockWord p (rightStart - 1) =
      longRunBlockWord U m a b c U.length (U.length + 2) := by
    rw [hprevIndex]
    rw [hRsplit] at hlastWord0
    simpa [longRunBlockWord, show U.length + 2 = k - 2 by rw [hU]; omega,
      List.append_assoc] using hlastWord0
  have hrightPos : 1 ≤ rightStart := by
    rw [hrightStartEq]
    have : 1 ≤ (k - 3) * (k - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hsource := blockBoundarySource_eq_bexit (by omega : 1 ≤ k) hp
    hrightPos hrightStartRange
  rw [hlastWord, bexit_longRunBlockWord_last (by omega : 4 ≤ k) U m a b c hU]
    at hsource
  have hV : (b :: U).length = k - 3 := by simp [hU]; omega
  obtain ⟨rightOrientation, hrightZero⟩ :=
    weightThreeTarget_normalizes_from_head (by omega : 4 ≤ k) hV hsource
      (by simpa [rightStart] using hcfg.rightSeamWeight)
  have hrightBlocks : ∀ r, r < U.length + 3 - rightDeficit →
      Hunter.ProofsChartEq.blockWord p (rightStart + r) =
        orientedRightPartialBlockWord U b m a c rightOrientation r := by
    intro r hr
    have hrle : r ≤ k - 2 - rightDeficit := by rw [hperiod] at hr; omega
    cases rightOrientation with
    | mab =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
    | mba =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
    | abm =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
    | amb =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
    | bma =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
    | bam =>
        exact doorSegment_block_word (by omega : 2 ≤ k) hp hrle hrightRange
          (by simpa [rightStart] using hcfg.rightDoors)
          (by simpa [orientedSuccessorStartWord] using hrightZero)
  have hfullClasses : ∀ j, j < U.length + 1 → ∀ l, l < U.length + 3 →
      rotClass (Hunter.ProofsChartEq.blockWord p
        (fullStart + j * (U.length + 3) + l)) =
        rotClass (longRunBlockWord U m a b c j l) := by
    intro j hj l hl
    have hj' : j < k - 3 := by rw [hU] at hj; omega
    have hl' : l < R.length + 2 := by
      rw [hRperiod, ← hperiod]
      exact hl
    have hclasses := weightThreeFullRun_block_classes (by omega : 4 ≤ k) hp
      hR hrun (by simpa [fullStart] using hzero) j hj' l hl'
    rw [hRperiod] at hclasses
    calc
      rotClass (Hunter.ProofsChartEq.blockWord p
          (fullStart + j * (U.length + 3) + l)) =
          rotClass (Hunter.ProofsChartEq.blockWord p
            (fullStart + j * (k - 1) + l)) := by rw [hperiod]
      _ = rotClass (orientedSuccessorIncidenceWord R m a b .bam j l) := hclasses
      _ = rotClass (longRunBlockWord U m a b c j l) := by
        rw [hRsplit]
        simpa [longRunBlockWord, orientedSuccessorIncidenceWord] using
          (orientedSuccessor_block_incidence_class
            (U ++ [c]) m a b .bam j l).symm
  have hcoordinateDisjoint : InternalLongCoordinateDisjoint U m a b c
      leftDeficit rightDeficit rightOrientation := by
    constructor
    · intro j hj l hl r hr
      have hfullBefore : fullStart + j * (U.length + 3) + l < rightStart := by
        rw [hrightStartEq, ← hperiod, ← hcount]
        have hjSucc : j + 1 ≤ U.length + 1 := by omega
        have hmul := Nat.mul_le_mul_right (U.length + 3) hjSucc
        rw [Nat.add_mul] at hmul
        omega
      have hfullRange : k * (fullStart + j * (U.length + 3) + l) <
          p.numVerts := by
        exact lt_of_le_of_lt
          (Nat.mul_le_mul_left k (Nat.le_of_lt hfullBefore)) hrightStartRange
      have hrightBlockRange : k * (rightStart + r) < p.numVerts := by
        have hrle : r ≤ k - 2 - rightDeficit := by rw [hperiod] at hr; omega
        exact lt_of_le_of_lt
          (Nat.mul_le_mul_left k (Nat.add_le_add_left hrle rightStart)) hrightRange
      have hne : fullStart + j * (U.length + 3) + l ≠ rightStart + r := by
        apply Nat.ne_of_lt
        exact lt_of_lt_of_le hfullBefore (Nat.le_add_right rightStart r)
      have hdistinct := Hunter.ProofsChartEq.blockWord_distinct
        (by omega : 1 ≤ k) hp hfullRange hrightBlockRange hne
      rw [hfullClasses j hj l hl,
        congrArg rotClass (hrightBlocks r hr)] at hdistinct
      exact hdistinct
    · intro r hr
      have hrightBlockRange : k * (rightStart + r) < p.numVerts := by
        have hrle : r ≤ k - 2 - rightDeficit := by rw [hperiod] at hr; omega
        exact lt_of_le_of_lt
          (Nat.mul_le_mul_left k (Nat.add_le_add_left hrle rightStart)) hrightRange
      have hleftBefore : leftStart < rightStart := by
        rw [hrightStartEq]
        dsimp [fullStart]
        omega
      have hne : leftStart ≠ rightStart + r := by
        apply Nat.ne_of_lt
        exact lt_of_lt_of_le hleftBefore (Nat.le_add_right rightStart r)
      have hdistinct := Hunter.ProofsChartEq.blockWord_distinct
        (by omega : 1 ≤ k) hp hcoord.partialDeltaRange hrightBlockRange hne
      rw [hpartialDelta, hRsplit,
        congrArg rotClass (hrightBlocks r hr)] at hdistinct
      exact hdistinct
  have hthreshold := internalLongRun_threshold_coordinates U m a b c
    leftDeficit rightDeficit rightOrientation hcfg.left.deltaPos
      hcfg.rightDeficitPos hcoordinateDisjoint
  rw [hperiod] at hthreshold
  omega

end PreimageChain

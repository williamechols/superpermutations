import LowerBounds.PLevels
import LowerBounds.PModel
import LowerBounds.SModel

/-!
# From search equations to the finite statements (the written proof, section 8)

The objects of `PModel.lean` (chains, families, paths and rings of vertices) are read as
sequences of rows on words (`PS.IsSeq`, `PSeq.lean`): `PS.seqOf kd F` writes the chains of `F` one
after the other and marks the first row of every chain with the kind `kd` of link.

For any number of symbols `4 ≤ k ≤ 15`:

* `chainCapK_of_search`, `pathCapK_of_search`: the searches `PS.seqSearch` (compiled, with tables)
  or `PS.seqSearchA` (arithmetic, for the kernel) for the levels up to `hi` give the caps;
* `ringCapK_of_search`: the search `PS.ringSearch` gives the ring cap, given the chain cap;
* `noProfileK_of_search`: the search `PS.profSearch` shows that no family has the profile, given
  the chain cap.

The statements about sequences on words (`PS.SeqCapLt`, `PS.RingCapT`) are kept as the interface
between the levels: `seqCap_of_search`, `seqCap_of_searchA`, `ringCapT_of_search`, ….
-/

namespace SuperpermLowerBounds
namespace PS

open S (PermW WLink IsWChain wdef)
open Hunter

variable {k : ℕ}

/-! ### Chains of words as rows with kinds -/

/-- The rows of a chain; the first row gets the kind `kd`, the others the kind 0. -/
def tagC (kd : ℕ) : List (List (List ℕ)) → List TRow
  | [] => []
  | P :: R => (kd, P) :: R.map fun Q => (0, Q)

/-- The rows of a list of chains, one chain after the other. -/
def tagF (kd : ℕ) (F : List (List (List (List ℕ)))) : List TRow := (F.map (tagC kd)).flatten

theorem tagC_snd (kd : ℕ) : ∀ C : List (List (List ℕ)), (tagC kd C).map Prod.snd = C
  | [] => rfl
  | P :: R => by
    show P :: (R.map fun Q => ((0 : ℕ), Q)).map Prod.snd = P :: R
    rw [List.map_map]
    congr 1
    exact List.map_id R

theorem tagF_snd (kd : ℕ) (F : List (List (List (List ℕ)))) :
    (tagF kd F).map Prod.snd = F.flatten := by
  unfold tagF
  rw [List.map_flatten, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id F]
  exact List.map_congr_left (fun C _ => tagC_snd kd C)

theorem tagC_ne (kd : ℕ) {C : List (List (List ℕ))} (h : C ≠ []) : tagC kd C ≠ [] := by
  cases C with
  | nil => exact absurd rfl h
  | cons P R => exact List.cons_ne_nil _ _

theorem length_tagC (kd : ℕ) (C : List (List (List ℕ))) : (tagC kd C).length = C.length := by
  rw [← List.length_map (f := Prod.snd), tagC_snd]

theorem holesT_eq_snd (L : List TRow) : holesT k L = (wdef k (L.map Prod.snd)).sum := by
  simp [holesT, wdef, List.map_map, Function.comp_def]

theorem holesT_tagC (kd : ℕ) (C : List (List (List ℕ))) :
    holesT k (tagC kd C) = (wdef k C).sum := by
  rw [holesT_eq_snd, tagC_snd]

theorem tagF_cons (kd : ℕ) (C : List (List (List ℕ))) (F : List (List (List (List ℕ)))) :
    tagF kd (C :: F) = tagC kd C ++ tagF kd F := rfl

theorem length_tagF (kd : ℕ) : ∀ F : List (List (List (List ℕ))),
    (tagF kd F).length = (F.map List.length).sum
  | [] => rfl
  | C :: F => by
    rw [tagF_cons, List.length_append, length_tagC, length_tagF kd F, List.map_cons,
      List.sum_cons]

theorem holesT_tagF (kd : ℕ) : ∀ F : List (List (List (List ℕ))),
    holesT k (tagF kd F) = (F.map fun C => (wdef k C).sum).sum
  | [] => rfl
  | C :: F => by
    rw [tagF_cons, holesT_append, holesT_tagC, holesT_tagF kd F, List.map_cons, List.sum_cons]

theorem tagC_tag (kd : ℕ) (C : List (List (List ℕ))) : ∀ x ∈ tagC kd C, x.1 = kd ∨ x.1 = 0 := by
  cases C with
  | nil =>
    intro x hx
    cases hx
  | cons P R =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    · obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hx
      exact Or.inr rfl

theorem mem_tagF {kd : ℕ} {F : List (List (List (List ℕ)))} {x : TRow} (hx : x ∈ tagF kd F) :
    ∃ C ∈ F, x ∈ tagC kd C := by
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hl
  exact ⟨C, hC, hxl⟩

theorem mem_tagC_snd {kd : ℕ} {C : List (List (List ℕ))} {x : TRow} (hx : x ∈ tagC kd C) :
    x.2 ∈ C := by
  have := List.mem_map_of_mem (f := Prod.snd) hx
  rwa [tagC_snd] at this

theorem countP_tagC {kd : ℕ} (hkd : kd ≠ 0) {C : List (List (List ℕ))} (hC : C ≠ []) :
    (tagC kd C).countP (fun x => x.1 != 0) = 1 := by
  cases C with
  | nil => exact absurd rfl hC
  | cons P R =>
    show ((kd, P) :: R.map fun Q => ((0 : ℕ), Q)).countP (fun x => x.1 != 0) = 1
    rw [List.countP_cons, List.countP_eq_zero.mpr]
    · simp [hkd]
    · intro x hx
      obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hx
      simp

theorem countP_tagF {kd : ℕ} (hkd : kd ≠ 0) : ∀ F : List (List (List (List ℕ))),
    (∀ C ∈ F, C ≠ []) → (tagF kd F).countP (fun x => x.1 != 0) = F.length
  | [], _ => rfl
  | C :: F, hne => by
    rw [tagF_cons, List.countP_append, countP_tagC hkd (hne C List.mem_cons_self),
      countP_tagF hkd F (fun D hD => hne D (List.mem_cons_of_mem _ hD)), List.length_cons]
    omega

theorem linksT_tagF {kd : ℕ} (hkd : kd ≠ 0) (F : List (List (List (List ℕ))))
    (hne : ∀ C ∈ F, C ≠ []) : linksT (tagF kd F) = F.length - 1 := by
  have h := countP_tagF hkd F hne
  cases F with
  | nil => rfl
  | cons C F' =>
    obtain ⟨P, R, rfl⟩ := List.exists_cons_of_ne_nil (hne C List.mem_cons_self)
    have e : tagF kd ((P :: R) :: F') = (kd, P) :: ((R.map fun Q => ((0 : ℕ), Q)) ++ tagF kd F') :=
      rfl
    rw [e] at h ⊢
    rw [List.countP_cons] at h
    have hk1 : (if ((kd, P) : TRow).1 != 0 then 1 else 0) = 1 := by simp [hkd]
    rw [hk1] at h
    show List.countP _ ((R.map fun Q => ((0 : ℕ), Q)) ++ tagF kd F') = _
    simp only [List.length_cons] at h ⊢
    omega

/-- The rows of a chain are joined by links of weight 3. -/
theorem isChain_tagC (kd : ℕ) {C : List (List (List ℕ))} (h : IsWChain k C) :
    List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
      LinkK k y.1 (x.2.getLast hx) (y.2.head hy)) (tagC kd C) := by
  cases C with
  | nil => exact List.IsChain.nil
  | cons P R =>
    have h1 : List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
        LinkK k y.1 (x.2.getLast hx) (y.2.head hy)) ((P :: R).map fun Q => ((0 : ℕ), Q)) := by
      rw [List.isChain_map]
      exact h.seams.imp (fun A B hAB hA hB => linkK_zero (hAB hA hB))
    exact List.IsChain.imp_head (fun hc hx hy => hc hx hy) h1

/-- A list of chains of words with pairwise different classes, joined by links of kind `kd`, is
a sequence. -/
theorem isSeq_tagF {kd : ℕ} {F : List (List (List (List ℕ)))} (hch : ∀ C ∈ F, IsWChain k C)
    (hne : ∀ C ∈ F, C ≠ [])
    (hcl : List.Pairwise (fun u v : List ℕ => ¬ u ~r v) F.flatten.flatten)
    (hlk : F.IsChain (fun C₁ C₂ => ∀ u ∈ C₁.getLast?.bind List.getLast?,
      ∀ v ∈ C₂.head?.bind List.head?, LinkK k kd u v)) :
    IsSeq k (tagF kd F) := by
  have hrow : ∀ x ∈ tagF kd F, ∃ C ∈ F, x.2 ∈ C := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := mem_tagF hx
    exact ⟨C, hC, mem_tagC_snd hxC⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    obtain ⟨C, hC, hxC⟩ := hrow x hx
    exact (hch C hC).words x.2 hxC w hw
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := hrow x hx
    exact (hch C hC).pieces_ne x.2 hxC
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := hrow x hx
    exact (hch C hC).size_le x.2 hxC
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := hrow x hx
    exact (hch C hC).doors x.2 hxC
  · have hnil : [] ∉ F.map (tagC kd) := by
      intro h
      obtain ⟨C, hC, e⟩ := List.mem_map.mp h
      exact tagC_ne kd (hne C hC) e
    unfold tagF
    rw [List.isChain_flatten hnil]
    refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hl
      exact isChain_tagC kd (hch C hC)
    · rw [List.isChain_map]
      refine hlk.imp ?_
      intro C₁ C₂ h12 x hx y hy hx' hy'
      have hy1 : y.1 = kd ∧ y.2.head hy' ∈ C₂.head?.bind List.head? := by
        cases C₂ with
        | nil => cases hy
        | cons P R =>
          have e : y = (kd, P) := (Option.some.inj hy).symm
          subst e
          refine ⟨rfl, ?_⟩
          show P.head hy' ∈ P.head?
          rw [List.head?_eq_some_head hy']
          rfl
      have hx1 : x.2.getLast hx' ∈ C₁.getLast?.bind List.getLast? := by
        have h1 : ((tagC kd C₁).map Prod.snd).getLast? = some x.2 := by
          rw [List.getLast?_map, Option.mem_def.mp hx]
          rfl
        rw [tagC_snd] at h1
        rw [h1]
        show x.2.getLast hx' ∈ x.2.getLast?
        rw [List.getLast?_eq_some_getLast hx']
        rfl
      rw [hy1.1]
      exact h12 _ hx1 _ hy1.2
  · rw [tagF_snd]
    exact hcl

theorem isChain_trivial {α : Type} {R : α → α → Prop} (h : ∀ a b, R a b) :
    ∀ l : List α, l.IsChain R
  | [] => List.IsChain.nil
  | [_] => List.isChain_singleton _
  | a :: b :: l => List.isChain_cons_cons.mpr ⟨h a b, isChain_trivial h (b :: l)⟩

/-! ### Caps for chains of words -/

/-- The chain cap, for chains of words. -/
def WCap (k : ℕ) (M : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ C : List (List (List ℕ)), IsWChain k C → (wdef k C).sum ≤ G → C.length ≤ M (wdef k C).sum

theorem tag_le_one {kd : ℕ} (hkd : kd ≤ 1) {F : List (List (List (List ℕ)))} :
    ∀ x ∈ tagF kd F, x.1 ≤ 1 := by
  intro x hx
  obtain ⟨C, _, hxC⟩ := mem_tagF hx
  rcases tagC_tag kd C x hxC with h | h <;> omega

theorem wcap_of_seqCap {M : ℕ → ℕ} {G : ℕ} (h : SeqCapLt k 0 M (G + 1)) : WCap k M G := by
  intro C hC hG
  by_cases hne : C = []
  · subst hne
    exact Nat.zero_le _
  have hseq : IsSeq k (tagF 1 [C]) := isSeq_tagF (fun D hD => by
      rw [List.mem_singleton.mp hD]
      exact hC)
    (fun D hD => by
      rw [List.mem_singleton.mp hD]
      exact hne)
    (by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact hC.classes)
    (List.isChain_singleton _)
  have hl : linksT (tagF 1 [C]) = 0 :=
    linksT_tagF (by decide) [C] (fun D hD => by
      rw [List.mem_singleton.mp hD]
      exact hne)
  have hh : holesT k (tagF 1 [C]) = (wdef k C).sum := by
    rw [holesT_tagF]
    simp
  have hlen : (tagF 1 [C]).length = C.length := by
    rw [length_tagF]
    simp
  have := h (tagF 1 [C]) hseq (tag_le_one (le_refl 1)) hl (by omega)
  rw [hh, hlen] at this
  exact this

/-! ### Vertices -/

/-- A chain of vertices as a chain of words. -/
def toW (C : List (List (Vtx k))) : List (List (List ℕ)) := C.map (List.map Subtype.val)

/-- The rows of a list of chains of vertices. -/
def seqOf (kd : ℕ) (F : List (List (List (Vtx k)))) : List TRow := tagF kd (F.map toW)

theorem toW_last (A : List (List (Vtx k))) :
    (toW A).getLast?.bind List.getLast? = (chainLast A).map Subtype.val := by
  unfold toW chainLast
  rw [List.getLast?_map]
  cases A.getLast? with
  | none => rfl
  | some P =>
    show (P.map Subtype.val).getLast? = P.getLast?.map Subtype.val
    exact List.getLast?_map

theorem toW_first (A : List (List (Vtx k))) :
    (toW A).head?.bind List.head? = (chainFirst A).map Subtype.val := by
  unfold toW chainFirst
  rw [List.head?_map]
  cases A.head? with
  | none => rfl
  | some P =>
    show (P.map Subtype.val).head? = P.head?.map Subtype.val
    exact List.head?_map

theorem holesL_toW (C : List (List (Vtx k))) : holesL k C = (wdef k (toW C)).sum := by
  unfold holesL
  rw [modelDeficits_eq]
  rfl

theorem toW_length (C : List (List (Vtx k))) : (toW C).length = C.length := List.length_map _

theorem fam_classes {F : List (List (List (Vtx k)))}
    (h : F.flatten.flatten.Pairwise (NotRot (k := k))) :
    List.Pairwise (fun u v : List ℕ => ¬ u ~r v) (F.map toW).flatten.flatten := by
  have e : (F.map toW).flatten.flatten = F.flatten.flatten.map Subtype.val := by
    symm
    rw [List.map_flatten, List.map_flatten]
    rfl
  rw [e, List.pairwise_map]
  exact h

/-- A link between two chains of vertices, read on words. -/
theorem chainLink_words {d kd : ℕ} (hkd : kd = 0 → d = 3) (hkd1 : kd = 1 → d = 4)
    {A B : List (List (Vtx k))} (h : ChainLink k d A B) :
    ∀ u ∈ (toW A).getLast?.bind List.getLast?, ∀ v ∈ (toW B).head?.bind List.head?,
      LinkK k kd u v := by
  intro u hu v hv
  rw [toW_last] at hu
  rw [toW_first] at hv
  obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨v0, hv0, rfl⟩ := Option.map_eq_some_iff.mp hv
  have hl : WLink k d u0.val v0.val := h u0 hu0 v0 hv0
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [← hkd h0]
    exact hl
  · rw [← hkd1 h1]
    exact hl

theorem famRows_seqOf (kd : ℕ) (F : List (List (List (Vtx k)))) :
    (seqOf kd F).length = famRows F := by
  unfold seqOf famRows
  rw [length_tagF, List.map_map]
  congr 1
  exact List.map_congr_left (fun C _ => toW_length C)

theorem famHoles_seqOf (kd : ℕ) (F : List (List (List (Vtx k)))) :
    holesT k (seqOf kd F) = famHoles k F := by
  unfold seqOf famHoles
  rw [holesT_tagF, List.map_map]
  congr 1
  exact List.map_congr_left (fun C _ => (holesL_toW C).symm)

/-- A family whose consecutive chains are joined by links of kind `kd` is a sequence. -/
theorem isSeq_seqOf {kd : ℕ} {F : List (List (List (Vtx k)))} (h : IsFamily k F)
    (hlk : (F.map toW).IsChain (fun C₁ C₂ => ∀ u ∈ C₁.getLast?.bind List.getLast?,
      ∀ v ∈ C₂.head?.bind List.head?, LinkK k kd u v)) : IsSeq k (seqOf kd F) :=
  isSeq_tagF
    (fun C hC => by
      obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
      exact isWChain_of_modelChain (h.chains C0 hC0))
    (fun C hC => by
      obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
      exact fun e => h.ne C0 hC0 (List.map_eq_nil_iff.mp e))
    (fam_classes h.classes) hlk

/-! ### The finite statements for `k` symbols -/

/-- `ChainCap` for `k` symbols. -/
def ChainCapK (k : ℕ) (M : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ C : List (List (Vtx k)), IsModelChain k C → holesL k C ≤ G → C.length ≤ M (holesL k C)

/-- `PathCap` for `k` symbols. -/
def PathCapK (k s : ℕ) (P : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ F : List (List (List (Vtx k))), IsPath k F → F.length = s + 1 → famHoles k F ≤ G →
    famRows F ≤ P (famHoles k F)

/-- `RingCap` for `k` symbols. -/
def RingCapK (k : ℕ) (PR : ℕ → ℕ) (G : ℕ) : Prop :=
  ∀ C : List (List (Vtx k)), IsRing k C → holesL k C ≤ G → C.length ≤ PR (holesL k C)

/-- `NoProfile` for `k` symbols. -/
def NoProfileK (k : ℕ) (ts : List (ℕ × ℕ)) : Prop :=
  ¬ ∃ F : List (List (List (Vtx k))), IsFamily k F ∧
    List.Forall₂ (fun C t => t.1 ≤ C.length ∧ holesL k C ≤ t.2) F ts

theorem chainCapK_of_wcap {M : ℕ → ℕ} {G : ℕ} (h : WCap k M G) : ChainCapK k M G := by
  intro C hC hG
  have := h (toW C) (isWChain_of_modelChain hC) (by rw [← holesL_toW]; exact hG)
  rwa [toW_length, ← holesL_toW] at this

theorem pathCapK_of_seqCap {s : ℕ} {P : ℕ → ℕ} {G : ℕ} (h : SeqCapLt k s P (G + 1)) :
    PathCapK k s P G := by
  intro F hF hlen hG
  have hseq : IsSeq k (seqOf 1 F) := isSeq_seqOf hF.toIsFamily (by
    rw [List.isChain_map]
    exact hF.links.imp (fun A B hAB =>
      chainLink_words (kd := 1) (fun h0 => absurd h0 (by decide)) (fun _ => rfl) hAB))
  have hne : ∀ C ∈ F.map toW, C ≠ [] := by
    intro C hC
    obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
    exact fun e => hF.ne C0 hC0 (List.map_eq_nil_iff.mp e)
  have hl : linksT (seqOf 1 F) = s := by
    unfold seqOf
    rw [linksT_tagF (by decide) _ hne, List.length_map, hlen]
    rfl
  have := h (seqOf 1 F) hseq (tag_le_one (le_refl 1)) hl (by rw [famHoles_seqOf]; omega)
  rwa [famRows_seqOf, famHoles_seqOf] at this

theorem ringCapK_of_ringCapT {PR : ℕ → ℕ} {G : ℕ} (h : RingCapT k PR G) : RingCapK k PR G := by
  intro C hC hG
  have hne : C ≠ [] := by
    intro e
    have := hC.two
    rw [e] at this
    simp at this
  have hfam : IsFamily k [C] :=
    ⟨fun D hD => by rw [List.mem_singleton.mp hD]; exact hC.chain,
      fun D hD => by rw [List.mem_singleton.mp hD]; exact hne,
      by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        exact hC.chain.classes⟩
  have hseq : IsSeq k (seqOf 0 [C]) := isSeq_seqOf hfam (List.isChain_singleton _)
  have h0 : ∀ x ∈ seqOf 0 [C], x.1 = 0 := by
    intro x hx
    obtain ⟨D, _, hxD⟩ := mem_tagF hx
    rcases tagC_tag 0 D x hxD with h | h <;> exact h
  have hlen : (seqOf 0 [C]).length = C.length := by
    rw [famRows_seqOf]
    simp [famRows]
  have hh : holesT k (seqOf 0 [C]) = holesL k C := by
    rw [famHoles_seqOf]
    simp [famHoles]
  have hsnd : (seqOf 0 [C]).map Prod.snd = toW C := by
    unfold seqOf
    rw [tagF_snd]
    simp
  have hcl : Closes k (seqOf 0 [C]) := by
    intro u hu v hv
    have hu' : u ∈ ((seqOf 0 [C]).map Prod.snd).getLast?.bind List.getLast? := by
      rw [List.getLast?_map]
      cases hq : (seqOf 0 [C]).getLast? with
      | none => rw [hq] at hu; cases hu
      | some x => rw [hq] at hu; exact hu
    have hv' : v ∈ ((seqOf 0 [C]).map Prod.snd).head?.bind List.head? := by
      rw [List.head?_map]
      cases hq : (seqOf 0 [C]).head? with
      | none => rw [hq] at hv; cases hv
      | some x => rw [hq] at hv; exact hv
    rw [hsnd] at hu' hv'
    exact (chainLink_words (kd := 0) (fun _ => rfl) (fun h1 => absurd h1 (by decide)) hC.closes
      u hu' v hv').1 rfl
  have := h (seqOf 0 [C]) hseq h0 (by rw [hlen]; exact hC.two) hcl (by rw [hh]; exact hG)
  rwa [hlen, hh] at this

/-! ### Profiles -/

theorem forall₂_and_right {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {l : List α} {ts : List β}, List.Forall₂ R l ts → (∀ t ∈ ts, P t) →
      List.Forall₂ (fun a t => R a t ∧ P t) l ts
  | _, _, List.Forall₂.nil, _ => List.Forall₂.nil
  | _, _, List.Forall₂.cons h hr, hP =>
    List.Forall₂.cons ⟨h, hP _ List.mem_cons_self⟩
      (forall₂_and_right hr (fun t ht => hP t (List.mem_cons_of_mem _ ht)))

theorem forall₂_left_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ts : List β}, List.Forall₂ R l ts → ∀ a ∈ l, ∃ t, R a t
  | _, _, List.Forall₂.nil, _, ha => by cases ha
  | _, _, List.Forall₂.cons h hr, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, h⟩
    · exact forall₂_left_mem hr a ha'

/-- Chains of words cut to the rows of their targets. -/
theorem cut_chains {G : ℕ} : ∀ {Fw : List (List (List (List ℕ)))} {ts : List (ℕ × ℕ)},
    List.Forall₂ (fun C t => (t.1 ≤ C.length ∧ (wdef k C).sum ≤ t.2) ∧ 1 ≤ t.1 ∧ t.2 ≤ G) Fw ts →
    (∀ C ∈ Fw, IsWChain k C) →
    ∃ Fc : List (List (List (List ℕ))),
      List.Forall₂ (fun C t => C.length = t.1 ∧ (wdef k C).sum ≤ t.2 ∧ IsWChain k C ∧ 1 ≤ t.1 ∧
        t.2 ≤ G) Fc ts ∧ Fc.flatten.flatten.Sublist Fw.flatten.flatten
  | _, _, List.Forall₂.nil, _ => ⟨[], List.Forall₂.nil, List.Sublist.refl _⟩
  | C :: Fw, t :: ts, List.Forall₂.cons hCt hrest, hch => by
    obtain ⟨Fc, hFc, hsub⟩ := cut_chains hrest (fun D hD => hch D (List.mem_cons_of_mem _ hD))
    refine ⟨C.take t.1 :: Fc, List.Forall₂.cons ⟨?_, ?_, ?_, hCt.2⟩ hFc, ?_⟩
    · rw [List.length_take]
      omega
    · have h1 : (wdef k C).sum = (wdef k (C.take t.1)).sum + (wdef k (C.drop t.1)).sum := by
        conv_lhs => rw [← List.take_append_drop t.1 C]
        simp [wdef]
      omega
    · exact (hch C List.mem_cons_self).infix (List.take_prefix _ _).isInfix
    · simp only [List.flatten_cons, List.flatten_append]
      exact List.Sublist.append ((List.take_sublist _ _).flatten) hsub

theorem holesT_zero_map (z : List (List (List ℕ))) :
    holesT k (z.map fun Q => ((0 : ℕ), Q)) = (wdef k z).sum := by
  rw [holesT_eq_snd, List.map_map]
  congr 2
  exact List.map_id z

/-- **No family has the profile `ts`**, if the statement for the profile rule holds and chains
obey the cap `M` up to `G` holes. -/
theorem noProfileK_of_stmt {M : List ℕ} {ts : List (ℕ × ℕ)} {G : ℕ}
    (hM : WCap k (fun x => M.getD x 0) G) (hts : ∀ t ∈ ts, 1 ≤ t.1 ∧ t.2 ≤ G) (hne : ts ≠ [])
    (hst : PStmt k true (profBad ts) noRule (profKeepN M ts) noRule (profKeepJ ts)) :
    NoProfileK k ts := by
  rintro ⟨F, hF, hFt⟩
  -- words, cut to the targets
  have hFw : List.Forall₂ (fun C t => (t.1 ≤ C.length ∧ (wdef k C).sum ≤ t.2) ∧ 1 ≤ t.1 ∧
      t.2 ≤ G) (F.map toW) ts := by
    refine forall₂_and_right ?_ hts
    rw [List.forall₂_map_left_iff]
    refine hFt.imp ?_
    intro C t hCt
    rw [toW_length, ← holesL_toW]
    exact hCt
  have hchW : ∀ C ∈ F.map toW, IsWChain k C := by
    intro C hC
    obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
    exact isWChain_of_modelChain (hF.chains C0 hC0)
  obtain ⟨Fc, hFc, hsub⟩ := cut_chains hFw hchW
  have hcl : List.Pairwise (fun u v : List ℕ => ¬ u ~r v) Fc.flatten.flatten :=
    (fam_classes hF.classes).sublist hsub
  -- every chain is a chain with at least one row
  have hFc2 : ∀ C ∈ Fc, IsWChain k C ∧ C ≠ [] := by
    intro C hC
    obtain ⟨t, hCt⟩ := forall₂_left_mem hFc C hC
    refine ⟨hCt.2.2.1, ?_⟩
    intro e
    have h1 := hCt.1
    rw [e] at h1
    simp only [List.length_nil] at h1
    omega
  have hseq : IsSeq k (tagF 2 Fc) := isSeq_tagF (fun C hC => (hFc2 C hC).1)
    (fun C hC => (hFc2 C hC).2) hcl
    (isChain_trivial (fun C₁ C₂ u _ v _ =>
      ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 (by decide)⟩) Fc)
  -- the rest of a chain obeys the cap
  have hsuf : ∀ (z : List (List (List ℕ))) (g : ℕ), IsWChain k z → (wdef k z).sum ≤ g → g ≤ G →
      ∀ a b : List TRow, (z.map fun Q => ((0 : ℕ), Q)) = a ++ b →
        b.length ≤ M.getD (holesT k b) 0 := by
    intro z g hz hzg hgG a b hab
    obtain ⟨a', b', rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hab
    have hb : IsWChain k b' := hz.infix (List.suffix_append a' b').isInfix
    have hbs : (wdef k b').sum ≤ (wdef k (a' ++ b')).sum := by
      simp [wdef]
    have := hM b' hb (by omega)
    rw [holesT_zero_map, List.length_map]
    exact this
  -- the shape of the rows
  cases hFc with
  | nil => exact hne rfl
  | @cons C0 t0 Fc' ts' hC0 hFc' =>
    obtain ⟨hC0len, hC0hol, hC0ch, ht0⟩ := hC0
    obtain ⟨P0, z0, rfl⟩ : ∃ P0 z0, C0 = P0 :: z0 := by
      cases C0 with
      | nil =>
        simp only [List.length_nil] at hC0len
        omega
      | cons P0 z0 => exact ⟨P0, z0, rfl⟩
    have hL : tagF 2 ((P0 :: z0) :: Fc') =
        (2, P0) :: ((z0.map fun Q => ((0 : ℕ), Q)) ++ (Fc'.map (tagC 2)).flatten) := rfl
    have hz0 : IsWChain k z0 := hC0ch.infix (List.suffix_cons P0 z0).isInfix
    have hwd : ∀ (P : List (List ℕ)) (z : List (List (List ℕ))),
        (wdef k (P :: z)).sum = (k - 1 - P.length) + (wdef k z).sum := by
      intro P z
      simp [wdef]
    have hinv : ProfInv k M (t0 :: ts') (0, 1, k - 1 - P0.length)
        ((z0.map fun Q => ((0 : ℕ), Q)) ++ (Fc'.map (tagC 2)).flatten) := by
      refine ⟨z0.map fun Q => ((0 : ℕ), Q), Fc'.map (tagC 2), rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hy
        rfl
      · show 0 + 1 + (Fc'.map (tagC 2)).length = (t0 :: ts').length
        rw [List.length_map, hFc'.length_eq, List.length_cons]
        omega
      · show 1 + (z0.map fun Q => ((0 : ℕ), Q)).length = t0.1
        rw [List.length_map]
        simp only [List.length_cons] at hC0len
        omega
      · show k - 1 - P0.length + holesT k (z0.map fun Q => ((0 : ℕ), Q)) ≤ t0.2
        rw [holesT_zero_map]
        rw [hwd] at hC0hol
        exact hC0hol
      · rw [hwd] at hC0hol
        exact hsuf z0 t0.2 hz0 (by omega) ht0.2
      · show List.Forall₂ _ (Fc'.map (tagC 2)) ts'
        rw [List.forall₂_map_left_iff]
        refine hFc'.imp ?_
        intro C t hCt
        obtain ⟨hlen, hhol, hch, ht⟩ := hCt
        obtain ⟨P, z, rfl⟩ : ∃ P z, C = P :: z := by
          cases C with
          | nil =>
            simp only [List.length_nil] at hlen
            omega
          | cons P z => exact ⟨P, z, rfl⟩
        refine ⟨P, z.map fun Q => ((0 : ℕ), Q), rfl, ?_, ?_, ?_, ?_⟩
        · intro y hy
          obtain ⟨Q, _, rfl⟩ := List.mem_map.mp hy
          rfl
        · rw [length_tagC]
          exact hlen
        · rw [holesT_tagC]
          exact hhol
        · rw [hwd] at hhol
          exact hsuf z t.2 (hch.infix (List.suffix_cons P z).isInfix) (by omega) ht.2
    have hrule := prof_rule _ _ hinv
    have hres := hst (tagF 2 ((P0 :: z0) :: Fc')) hseq (by rw [hL]; exact List.cons_ne_nil _ _)
      (by
        intro u x w huw hu
        rw [hL] at huw
        obtain ⟨y, u', rfl⟩ := List.exists_cons_of_ne_nil hu
        obtain ⟨rfl, hr⟩ := List.cons.inj huw
        exact hrule.1 u' x w hr)
    have hb : ap (profBad (t0 :: ts')) (cnt k true (tagF 2 ((P0 :: z0) :: Fc'))) = true := by
      rw [hL]
      exact hrule.2
    rw [hres.1] at hb
    cases hb

/-! ### From search equations -/

section Search

variable {caps : List (List ℕ)} {M PR : List ℕ} {ts : List (ℕ × ℕ)} {s lo hi G fuel ds nt : ℕ}

theorem seqSearch_direct {pa pb : ℕ} (h : seqSearch k caps s lo hi fuel ds nt pa pb = false) :
    searchB k false (seqBad caps s lo hi) noRule (seqKeepN caps s lo hi) (seqKeepS caps s lo hi)
      noRule fuel ds nt pa pb = false := by
  unfold seqSearch at h
  simp only [look3_tab3] at h
  exact h

theorem ringSearch_direct {pa pb : ℕ} (h : ringSearch k M PR G fuel ds nt pa pb = false) :
    searchB k false noRule (ringBad PR G) (ringKeep M PR G) noRule noRule fuel ds nt pa pb
      = false := by
  unfold ringSearch at h
  simp only [look3_tab3] at h
  exact h

theorem profSearch_direct {pa pb : ℕ} (h : profSearch k M ts fuel ds nt pa pb = false) :
    searchB k true (profBad ts) noRule (profKeepN M ts) noRule (profKeepJ ts) fuel ds nt pa pb
      = false := by
  unfold profSearch at h
  simp only [look3_tab3] at h
  exact h

/-- F_s on the levels `lo … hi`, from the compiled search. -/
theorem seqCap_of_search (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch k caps s lo hi fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_level hlow hprev (stmt_of_searchB hk hk15 hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    exact ⟨pa, pb, h1, h2, seqSearch_direct h⟩))

/-- F_s on the levels `lo … hi`, from the arithmetic search. -/
theorem seqCap_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hlow : ∀ j, j < s → SeqCapLt k j (capF caps j) (hi + 1))
    (hprev : SeqCapLt k s (capF caps s) lo)
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearchA k caps s lo hi fuel ds nt pa pb = false) :
    SeqCapLt k s (capF caps s) (hi + 1) :=
  seqCap_level hlow hprev (stmt_of_searchA hk hk15 hnt hs)

/-- FR, from the compiled search. -/
theorem ringCapT_of_search (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hM : SeqCapLt k 0 (fun x => M.getD x 0) (G + 1))
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      ringSearch k M PR G fuel ds nt pa pb = false) :
    RingCapT k (fun x => PR.getD x 0) G :=
  ringCap_of_stmt hM (stmt_of_searchB hk hk15 hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    exact ⟨pa, pb, h1, h2, ringSearch_direct h⟩))

/-- FR, from the arithmetic search. -/
theorem ringCapT_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hM : SeqCapLt k 0 (fun x => M.getD x 0) (G + 1))
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      ringSearchA k M PR G fuel ds nt pa pb = false) :
    RingCapT k (fun x => PR.getD x 0) G :=
  ringCap_of_stmt hM (stmt_of_searchA hk hk15 hnt hs)

/-- FF, from the compiled search. -/
theorem noProfileK_of_search (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hM : WCap k (fun x => M.getD x 0) G) (hts : ∀ t ∈ ts, 1 ≤ t.1 ∧ t.2 ≤ G) (hne : ts ≠ [])
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      profSearch k M ts fuel ds nt pa pb = false) :
    NoProfileK k ts :=
  noProfileK_of_stmt hM hts hne (stmt_of_searchB hk hk15 hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    exact ⟨pa, pb, h1, h2, profSearch_direct h⟩))

/-- FF, from the arithmetic search. -/
theorem noProfileK_of_searchA (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hM : WCap k (fun x => M.getD x 0) G) (hts : ∀ t ∈ ts, 1 ≤ t.1 ∧ t.2 ≤ G) (hne : ts ≠ [])
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      profSearchA k M ts fuel ds nt pa pb = false) :
    NoProfileK k ts :=
  noProfileK_of_stmt hM hts hne (stmt_of_searchA hk hk15 hnt hs)

end Search

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.seqCap_of_search
#print axioms SuperpermLowerBounds.PS.ringCapT_of_search
#print axioms SuperpermLowerBounds.PS.noProfileK_of_search
#print axioms SuperpermLowerBounds.PS.chainCapK_of_wcap
#print axioms SuperpermLowerBounds.PS.pathCapK_of_seqCap
#print axioms SuperpermLowerBounds.PS.ringCapK_of_ringCapT

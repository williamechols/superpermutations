import PreimageChain.PortalAssignment

/-!
# 余维一源映射的门户覆盖

实际非终端预像链源通过单射映入组件集合，并覆盖除至多一个组件之外的全部组件。
本模块证明任意组件谓词（特别是非特选终端门户）也至多损失一个元素。
-/

namespace PreimageChain

open scoped Classical

/-- 单射在有限子集上的像保持基数。 -/
theorem card_image_eq_of_injective_on_univ
    {Source Target : Type*} [DecidableEq Target]
    (f : Source → Target) (hf : Function.Injective f)
    (sources : Finset Source) :
    (sources.image f).card = sources.card :=
  Finset.card_image_of_injective sources hf

/-- 过滤后再取单射像，等于在像中按目标谓词过滤。 -/
theorem image_filter_eq_filter_image
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (f : Source → Target) (sources : Finset Source)
    (predicate : Target → Prop) [DecidablePred predicate] :
    (sources.filter fun source => predicate (f source)).image f =
      (sources.image f).filter predicate := by
  ext target
  constructor
  · intro htarget
    rw [Finset.mem_image] at htarget
    obtain ⟨source, hsource, rfl⟩ := htarget
    have hfiltered := Finset.mem_filter.mp hsource
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨source, hfiltered.1, rfl⟩, hfiltered.2⟩
  · intro htarget
    have hfiltered := Finset.mem_filter.mp htarget
    rw [Finset.mem_image] at hfiltered
    obtain ⟨source, hsource, rfl⟩ := hfiltered.1
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr ⟨hsource, hfiltered.2⟩, rfl⟩

/--
若单射源映射的实际像至多漏掉一个目标，则满足任意目标谓词的源也至多比目标少一个。
-/
theorem filtered_source_card_codimension_one
    {Source Target : Type*}
    [Fintype Target] [DecidableEq Source] [DecidableEq Target]
    (f : Source → Target) (hf : Function.Injective f)
    (sources : Finset Source)
    (predicate : Target → Prop) [DecidablePred predicate]
    (hcodim : Fintype.card Target ≤ sources.card + 1) :
    ((Finset.univ : Finset Target).filter predicate).card - 1 ≤
      (sources.filter fun source => predicate (f source)).card := by
  let represented : Finset Target := sources.image f
  let selected : Finset Target := (Finset.univ : Finset Target).filter predicate
  let selectedRepresented : Finset Target := selected.filter fun target => target ∈ represented
  let selectedMissing : Finset Target := selected.filter fun target => target ∉ represented

  have hrepresentedCard : represented.card = sources.card := by
    dsimp [represented]
    exact Finset.card_image_of_injective sources hf

  have hselectedPartition :
      selectedRepresented.card + selectedMissing.card = selected.card := by
    dsimp [selectedRepresented, selectedMissing]
    simpa using Finset.card_filter_add_card_filter_not
      (s := selected) (fun target => target ∈ represented)

  have hselectedRepresentedEq :
      selectedRepresented = represented.filter predicate := by
    ext target
    simp [selectedRepresented, selected, and_comm]

  have hsourceImage :
      (sources.filter fun source => predicate (f source)).image f =
        represented.filter predicate := by
    simpa [represented] using image_filter_eq_filter_image f sources predicate

  have hselectedRepresentedCard : selectedRepresented.card =
      (sources.filter fun source => predicate (f source)).card := by
    rw [hselectedRepresentedEq, ← hsourceImage]
    exact Finset.card_image_of_injective _ hf

  have hmissingSubset : selectedMissing ⊆
      (Finset.univ : Finset Target) \ represented := by
    intro target htarget
    have hmem := Finset.mem_filter.mp htarget
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmem.2⟩

  have hmissingCard : selectedMissing.card ≤ 1 := by
    have hsub := Finset.card_le_card hmissingSubset
    have hdiffCard :
        ((Finset.univ : Finset Target) \ represented).card =
          Fintype.card Target - represented.card := by
      simp [Finset.card_sdiff]
    rw [hdiffCard, hrepresentedCard] at hsub
    omega

  rw [hselectedRepresentedCard] at hselectedPartition
  change selected.card - 1 ≤
    (sources.filter fun source => predicate (f source)).card
  omega

/-- 全部源构成有限类型时的直接版本。 -/
theorem filtered_univ_source_card_codimension_one
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (f : Source → Target) (hf : Function.Injective f)
    (predicate : Target → Prop) [DecidablePred predicate]
    (hcodim : Fintype.card Target ≤ Fintype.card Source + 1) :
    ((Finset.univ : Finset Target).filter predicate).card - 1 ≤
      ((Finset.univ : Finset Source).filter fun source => predicate (f source)).card := by
  simpa using filtered_source_card_codimension_one
    f hf (Finset.univ : Finset Source) predicate (by simpa using hcodim)

end PreimageChain

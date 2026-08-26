import FiniteDefects.D4RoundTrip

/-! # Active-owner and good-edge cardinalities -/

namespace FiniteDefects

def IsD4InPhaseStone {m : ℕ} (placement : D4LiteralPlacement m) : Prop :=
  placement.tile = .stone ∧
    placementBaseResidue (m + 2) placement.base = .r0

noncomputable instance isD4InPhaseStoneDecidable {m : ℕ}
    (placement : D4LiteralPlacement m) :
    Decidable (IsD4InPhaseStone placement) := Classical.propDecidable _

abbrev D4InPhaseStonePlacement {m : ℕ} (tiling : D4LiteralTiling m) :=
  {placement : D4LiteralPlacement m //
    placement ∈ tiling.1 ∧ IsD4InPhaseStone placement}

noncomputable instance d4InPhaseStonePlacementFintype {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Fintype (D4InPhaseStonePlacement tiling) :=
  Fintype.ofFinite (D4InPhaseStonePlacement tiling)

noncomputable instance d4GoodBonePlacementFintype {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Fintype (D4GoodBonePlacement tiling) :=
  Fintype.ofFinite (D4GoodBonePlacement tiling)

noncomputable def D4InPhaseStonePlacement.owner {m : ℕ}
    {tiling : D4LiteralTiling m} (stone : D4InPhaseStonePlacement tiling) :
    SimplexPoint (m + 2) := d4StoneOwner stone.1 stone.2.2.1

theorem D4InPhaseStonePlacement.owner_full {m : ℕ}
    {tiling : D4LiteralTiling m} (stone : D4InPhaseStonePlacement tiling) :
    IsD4FullOwner stone.owner :=
  d4StoneOwner_full stone.1 stone.2.2.1 stone.2.2.2

theorem d4InPhaseStone_owner_injective {m : ℕ}
    {tiling : D4LiteralTiling m} :
    Function.Injective (D4InPhaseStonePlacement.owner
      (tiling := tiling)) := by
  intro left right howner
  have hpresent := left.owner_full .zero
  have hleftCover := d4Stone_covers_owner_label left.1 left.2.2.1
    left.2.2.2 .zero hpresent
  have hrightPresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell right.owner .zero) := right.owner_full .zero
  have hrightCover := d4Stone_covers_owner_label right.1 right.2.2.1
    right.2.2.2 .zero hrightPresent
  have hleftEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.owner .zero, hpresent⟩ left.1 left.2.1 hleftCover
  have hrightEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.owner .zero, hpresent⟩ right.1 right.2.1 (by
      simpa [howner] using hrightCover)
  apply Subtype.ext
  exact hleftEq.trans hrightEq.symm

noncomputable def d4StoneOwnerSet {m : ℕ} (tiling : D4LiteralTiling m) :
    Finset (SimplexPoint (m + 2)) :=
  Finset.univ.image (fun stone : D4InPhaseStonePlacement tiling => stone.owner)

def IsD4ActiveOwner {m : ℕ} (tiling : D4LiteralTiling m)
    (p : SimplexPoint (m + 2)) : Prop := p ∉ d4StoneOwnerSet tiling

abbrev D4ActiveOwner {m : ℕ} (tiling : D4LiteralTiling m) :=
  {p : SimplexPoint (m + 2) // IsD4ActiveOwner tiling p}

noncomputable instance d4ActiveOwnerFintype {m : ℕ}
    (tiling : D4LiteralTiling m) : Fintype (D4ActiveOwner tiling) :=
  Fintype.ofFinite (D4ActiveOwner tiling)

theorem card_d4StoneOwnerSet {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4StoneOwnerSet tiling).card =
      Fintype.card (D4InPhaseStonePlacement tiling) := by
  rw [d4StoneOwnerSet, Finset.card_image_of_injective]
  · simp
  · exact d4InPhaseStone_owner_injective

theorem card_d4ActiveOwner {m : ℕ} (tiling : D4LiteralTiling m) :
    Fintype.card (D4ActiveOwner tiling) =
      Fintype.card (SimplexPoint (m + 2)) -
        Fintype.card (D4InPhaseStonePlacement tiling) := by
  classical
  let activeFilter : Finset (SimplexPoint (m + 2)) :=
    Finset.univ.filter fun p => p ∉ d4StoneOwnerSet tiling
  let equiv : D4ActiveOwner tiling ≃ ↥activeFilter :=
    { toFun := fun p => ⟨p.1, Finset.mem_filter.mpr
        ⟨Finset.mem_univ p.1, p.2⟩⟩
      invFun := fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr equiv, Fintype.card_coe]
  have hactive : activeFilter =
      (Finset.univ : Finset (SimplexPoint (m + 2))) \ d4StoneOwnerSet tiling := by
    ext p
    simp [activeFilter]
  rw [hactive, Finset.card_sdiff (Finset.subset_univ _),
    Finset.card_univ, card_d4StoneOwnerSet]

theorem card_d4InPhaseStonePlacement {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Fintype.card (D4InPhaseStonePlacement tiling) =
      d4RightStoneCount tiling - d4WrongPhaseStoneCount tiling := by
  classical
  let equiv : D4InPhaseStonePlacement tiling ≃
      ↥(tiling.1.filter IsD4InPhaseStone) :=
    { toFun := fun placement => ⟨placement.1,
        Finset.mem_filter.mpr placement.2⟩
      invFun := fun placement => ⟨placement.1,
        Finset.mem_filter.mp placement.2⟩
      left_inv := by intro placement; rfl
      right_inv := by intro placement; rfl }
  rw [Fintype.card_congr equiv, Fintype.card_coe]
  have hpartition :
      tiling.1.filter (fun placement => placement.tile = .stone) =
        tiling.1.filter IsD4InPhaseStone ∪
          tiling.1.filter IsD4WrongPhaseStone := by
    ext placement
    simp only [Finset.mem_filter, Finset.mem_union, IsD4InPhaseStone,
      IsD4WrongPhaseStone]
    constructor
    · intro hstone
      by_cases hphase : placementBaseResidue (m + 2) placement.base = .r0
      · exact Or.inl ⟨hstone.1, hstone.2, hphase⟩
      · exact Or.inr ⟨hstone.1, hstone.2, hphase⟩
    · rintro (⟨hmem, hstone, _⟩ | ⟨hmem, hstone, _⟩)
      · exact ⟨hmem, hstone⟩
      · exact ⟨hmem, hstone⟩
  have hdisjoint : Disjoint (tiling.1.filter IsD4InPhaseStone)
      (tiling.1.filter IsD4WrongPhaseStone) := by
    rw [Finset.disjoint_left]
    intro placement hin hwrong
    simp only [Finset.mem_filter, IsD4InPhaseStone,
      IsD4WrongPhaseStone] at hin hwrong
    exact hwrong.2.2 hin.2.2
  have hcard := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  change d4RightStoneCount tiling =
    (tiling.1.filter IsD4InPhaseStone).card +
      d4WrongPhaseStoneCount tiling at hcard
  omega

theorem card_d4GoodBonePlacement {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Fintype.card (D4GoodBonePlacement tiling) =
      d4BoneCount tiling - d4ThreeOwnerBoneCount tiling := by
  classical
  let goodPredicate := fun placement : D4LiteralPlacement m =>
    placement.tile ≠ .stone ∧ ¬IsD4ThreeOwnerBone placement
  let equiv : D4GoodBonePlacement tiling ≃
      ↥(tiling.1.filter goodPredicate) :=
    { toFun := fun placement => ⟨placement.1,
        Finset.mem_filter.mpr ⟨placement.2.1,
          placement.2.2.1, placement.2.2.2⟩⟩
      invFun := fun placement => ⟨placement.1,
        (Finset.mem_filter.mp placement.2).1,
        (Finset.mem_filter.mp placement.2).2.1,
        (Finset.mem_filter.mp placement.2).2.2⟩
      left_inv := by intro placement; rfl
      right_inv := by intro placement; rfl }
  rw [Fintype.card_congr equiv, Fintype.card_coe]
  change (tiling.1.filter fun placement =>
    placement.tile ≠ .stone ∧ ¬IsD4ThreeOwnerBone placement).card = _
  have hpartition :
      tiling.1.filter (fun placement => placement.tile ≠ .stone) =
        tiling.1.filter (fun placement =>
          placement.tile ≠ .stone ∧ ¬IsD4ThreeOwnerBone placement) ∪
        tiling.1.filter IsD4ThreeOwnerBone := by
    ext placement
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hbone
      by_cases hthree : IsD4ThreeOwnerBone placement
      · exact Or.inr ⟨hbone.1, hthree⟩
      · exact Or.inl ⟨hbone.1, hbone.2, hthree⟩
    · rintro (⟨hmem, hbone, _⟩ | ⟨hmem, hthree⟩)
      · exact ⟨hmem, hbone⟩
      · refine ⟨hmem, ?_⟩
        intro hstone
        rcases htile : placement.tile with _ | _ | _ | _
        · simp [htile, IsD4ThreeOwnerBone] at hthree
        all_goals simp [hstone] at htile
  have hdisjoint : Disjoint
      (tiling.1.filter fun placement =>
        placement.tile ≠ .stone ∧ ¬IsD4ThreeOwnerBone placement)
      (tiling.1.filter IsD4ThreeOwnerBone) := by
    rw [Finset.disjoint_left]
    intro placement hgood hthree
    simp only [Finset.mem_filter] at hgood hthree
    exact hgood.2.2 hthree.2
  have hcard := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  unfold d4BoneCount d4ThreeOwnerBoneCount
  omega

theorem card_active_eq_goodEdges_add_three {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Fintype.card (D4ActiveOwner tiling) =
      Fintype.card (D4GoodBonePlacement tiling) + 3 := by
  rw [card_d4ActiveOwner, card_d4InPhaseStonePlacement,
    card_d4GoodBonePlacement, card_simplexPoint]
  rw [show m + 2 + 2 = m + 4 by omega]
  have hpartition := d4RightStoneCount_add_boneCount tiling
  rw [d4_literal_tiling_card] at hpartition
  have hdefect := d4_exactly_one_defect_reference tiling
  have hchoose : 2 ≤ (m + 4).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ m + 4 by omega)
    norm_num at hmono ⊢
    omega
  have hstoneLe : d4WrongPhaseStoneCount tiling ≤
      d4RightStoneCount tiling := by
    unfold d4WrongPhaseStoneCount d4RightStoneCount
    apply Finset.card_le_card
    intro placement hmem
    simp only [Finset.mem_filter, IsD4WrongPhaseStone] at hmem ⊢
    exact ⟨hmem.1, hmem.2.1⟩
  have hboneLe : d4ThreeOwnerBoneCount tiling ≤ d4BoneCount tiling := by
    unfold d4ThreeOwnerBoneCount d4BoneCount
    apply Finset.card_le_card
    intro placement hmem
    simp only [Finset.mem_filter] at hmem ⊢
    refine ⟨hmem.1, ?_⟩
    intro hstone
    rcases htile : placement.tile with _ | _ | _ | _
    · simp [htile, IsD4ThreeOwnerBone] at hmem
    all_goals simp [hstone] at htile
  have htotal : (m + 4).choose 2 =
      d4RightStoneCount tiling + d4BoneCount tiling + 2 := by
    omega
  omega

end FiniteDefects

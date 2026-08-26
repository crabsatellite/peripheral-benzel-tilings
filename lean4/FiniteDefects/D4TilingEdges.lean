import FiniteDefects.D4OwnerTypes

/-! # The good-bone edge carrier of one literal d=4 tiling -/

namespace FiniteDefects

abbrev D4GoodBonePlacement {m : ℕ} (tiling : D4LiteralTiling m) :=
  {placement : D4LiteralPlacement m //
    placement ∈ tiling.1 ∧ placement.tile ≠ .stone ∧
      ¬IsD4ThreeOwnerBone placement}

noncomputable def D4GoodBonePlacement.edge {m : ℕ}
    {tiling : D4LiteralTiling m} (placement : D4GoodBonePlacement tiling) :
    D4LiteralDirectedEdge m :=
  d4LiteralDirectedEdgeOfPlacement placement.1
    placement.2.2.1 placement.2.2.2

noncomputable def D4GoodBonePlacement.source {m : ℕ}
    {tiling : D4LiteralTiling m} (placement : D4GoodBonePlacement tiling) :
    SimplexPoint (m + 2) := placement.edge.source

noncomputable def D4GoodBonePlacement.target {m : ℕ}
    {tiling : D4LiteralTiling m} (placement : D4GoodBonePlacement tiling) :
    SimplexPoint (m + 2) := placement.edge.target

noncomputable def D4GoodBonePlacement.label {m : ℕ}
    {tiling : D4LiteralTiling m} (placement : D4GoodBonePlacement tiling) :
    MicroLabel := placement.edge.boneClass.label

noncomputable def D4GoodBonePlacement.step {m : ℕ}
    {tiling : D4LiteralTiling m} (placement : D4GoodBonePlacement tiling) :
    Cell := placement.edge.boneClass.step

theorem d4TilingEdge_mem {m : ℕ} {tiling : D4LiteralTiling m}
    (edge : D4GoodBonePlacement tiling) : edge.1 ∈ tiling.1 := edge.2.1

theorem d4TilingEdge_cover_role {m : ℕ} {tiling : D4LiteralTiling m}
    (edge : D4GoodBonePlacement tiling)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers edge.1 ⟨ownerCell p label, hpresent⟩) :
    (p = edge.source ∧ label ≠ edge.label) ∨
      (p = edge.target ∧ label = edge.label) :=
  d4_good_edge_cover_role edge.edge p label hpresent hcover

theorem d4TilingEdge_covers_target {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.target edge.label)) :
    D4PlacementCovers edge.1
      ⟨ownerCell edge.target edge.label, hpresent⟩ :=
  d4GoodEdge_covers_target_label edge.edge hpresent

theorem d4TilingEdge_covers_source_other {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (label : MicroLabel) (hne : label ≠ edge.label)
    (hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.source label)) :
    D4PlacementCovers edge.1
      ⟨ownerCell edge.source label, hpresent⟩ :=
  d4GoodEdge_covers_source_other edge.edge label hne hpresent

theorem d4TilingEdge_simplex_step {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    (edge.step = stepA ∧ edge.target.u + 1 = edge.source.u ∧
      edge.target.v = edge.source.v ∧ edge.target.w = edge.source.w + 1) ∨
    (edge.step = stepB ∧ edge.target.u = edge.source.u ∧
      edge.target.v = edge.source.v + 1 ∧ edge.target.w + 1 = edge.source.w) ∨
    (edge.step = stepC ∧ edge.target.u = edge.source.u + 1 ∧
      edge.target.v + 1 = edge.source.v ∧ edge.target.w = edge.source.w) :=
  d4LiteralDirectedEdge_simplex_step edge.edge

theorem d4TilingEdge_label_allowed {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    allowedStep edge.label edge.step := d4GoodEdge_label_allowed edge.edge

theorem microLabel_exists_ne_two (left right : MicroLabel) :
    ∃ label, label ≠ left ∧ label ≠ right := by
  rcases left <;> rcases right
  all_goals first
    | exact ⟨.zero, by decide, by decide⟩
    | exact ⟨.one, by decide, by decide⟩
    | exact ⟨.two, by decide, by decide⟩

theorem microLabel_two_others (label : MicroLabel) :
    ∃ left right, left ≠ label ∧ right ≠ label ∧ left ≠ right := by
  rcases label
  · exact ⟨.one, .two, by decide, by decide, by decide⟩
  · exact ⟨.zero, .two, by decide, by decide, by decide⟩
  · exact ⟨.zero, .one, by decide, by decide, by decide⟩

theorem d4TilingEdge_source_full {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    IsD4FullOwner edge.source := by
  rcases d4_owner_full_or_boundary edge.source with hfull | hboundary
  · exact hfull
  · obtain ⟨endpointLabel, hendpoint⟩ := hboundary
    obtain ⟨left, right, hleft, hright, hne⟩ :=
      microLabel_two_others edge.label
    have hleftPresent := d4GoodEdge_source_other_present edge.edge left hleft
    have hrightPresent := d4GoodEdge_source_other_present edge.edge right hright
    have hleftEq := d4_boundary_owner_label_unique edge.source endpointLabel
      left hendpoint hleftPresent
    have hrightEq := d4_boundary_owner_label_unique edge.source endpointLabel
      right hendpoint hrightPresent
    exact (hne (hleftEq.trans hrightEq.symm)).elim

theorem d4TilingEdge_source_unique {m : ℕ}
    {tiling : D4LiteralTiling m}
    (left right : D4GoodBonePlacement tiling)
    (hsource : left.source = right.source) : left = right := by
  obtain ⟨label, hleft, hright⟩ :=
    microLabel_exists_ne_two left.label right.label
  have hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell left.source label) := d4TilingEdge_source_full left label
  have hleftCover := d4TilingEdge_covers_source_other left label hleft hpresent
  have hrightPresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell right.source label) := by simpa [hsource] using hpresent
  have hrightCover :=
    d4TilingEdge_covers_source_other right label hright hrightPresent
  have heq := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.source label, hpresent⟩ left.1 left.2.1 hleftCover
  have heq' := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.source label, hpresent⟩ right.1 right.2.1 (by
      simpa [hsource] using hrightCover)
  apply Subtype.ext
  exact heq.trans heq'.symm

theorem d4TilingEdge_target_label_unique {m : ℕ}
    {tiling : D4LiteralTiling m}
    (left right : D4GoodBonePlacement tiling)
    (htarget : left.target = right.target)
    (hlabel : left.label = right.label) : left = right := by
  have hpresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell left.target left.label) :=
    d4GoodEdge_target_present left.edge
  have hleftCover := d4TilingEdge_covers_target left hpresent
  have hrightPresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell right.target right.label) := by simpa [htarget, hlabel] using hpresent
  have hrightCover := d4TilingEdge_covers_target right hrightPresent
  have heq := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.target left.label, hpresent⟩ left.1 left.2.1 hleftCover
  have heq' := d4CoveringPlacement_unique tiling
    ⟨ownerCell left.target left.label, hpresent⟩ right.1 right.2.1 (by
      simpa [htarget, hlabel] using hrightCover)
  apply Subtype.ext
  exact heq.trans heq'.symm

theorem d4CoveringPlacement_classification {m : ℕ}
    (tiling : D4LiteralTiling m) (cell : D4Cell m) :
    d4CoveringPlacement tiling cell = d4BadPlacement tiling ∨
    (d4CoveringPlacement tiling cell).tile = .stone ∧
      placementBaseResidue (m + 2)
        (d4CoveringPlacement tiling cell).base = .r0 ∨
    ∃ edge : D4GoodBonePlacement tiling,
      edge.1 = d4CoveringPlacement tiling cell := by
  let placement := d4CoveringPlacement tiling cell
  have hmem := d4CoveringPlacement_mem tiling cell
  by_cases hbad : IsD4BadPlacement placement
  · left
    exact d4BadPlacement_unique tiling placement hmem hbad
  · rcases d4_nonbad_is_good_bone_or_stone placement hbad with hstone | hbone
    · exact Or.inr (Or.inl hstone)
    · right; right
      exact ⟨⟨placement, hmem, hbone.1, hbone.2⟩, rfl⟩

end FiniteDefects

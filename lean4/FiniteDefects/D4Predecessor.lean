import FiniteDefects.D4TilingEdges

/-! # Unique backward continuation from every path edge and endpoint -/

namespace FiniteDefects

theorem d4_edge_source_predecessor {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    ∃! previous : D4GoodBonePlacement tiling,
      previous.target = edge.source ∧ previous.label = edge.label := by
  have hsourceFull := d4TilingEdge_source_full edge
  let cell : D4Cell m :=
    ⟨ownerCell edge.source edge.label, hsourceFull edge.label⟩
  let covering := d4CoveringPlacement tiling cell
  have hcoveringMem := d4CoveringPlacement_mem tiling cell
  have hcoveringCovers := d4CoveringPlacement_covers tiling cell
  rcases d4CoveringPlacement_classification tiling cell with hbad | hstone | hbone
  · have hbadCover : D4PlacementCovers (d4BadPlacement tiling) cell := by
      rw [← hbad]
      exact hcoveringCovers
    have hcore := d4_bad_cover_is_core tiling edge.source edge.label
      (hsourceFull edge.label) hbadCover
    exact (hnotcore hcore).elim
  · have hstoneOwner := d4_good_stone_cover_owner covering hstone.1 hstone.2
      edge.source edge.label (hsourceFull edge.label) hcoveringCovers
    obtain ⟨other, hother, _⟩ := microLabel_exists_ne_two edge.label edge.label
    have hotherPresent := hsourceFull other
    have hstoneCover : D4PlacementCovers covering
        ⟨ownerCell edge.source other, hotherPresent⟩ := by
      have hpresentStone : inBenzel (m + 4) (2 * m + 4)
          (ownerCell (d4StoneOwner covering hstone.1) other) := by
        simpa [← hstoneOwner] using hotherPresent
      have hcoverStone := d4Stone_covers_owner_label covering hstone.1
        hstone.2 other hpresentStone
      simpa [← hstoneOwner] using hcoverStone
    have hedgeCover :=
      d4TilingEdge_covers_source_other edge other hother hotherPresent
    have hcoverEq := d4CoveringPlacement_unique tiling
      ⟨ownerCell edge.source other, hotherPresent⟩ covering hcoveringMem
      hstoneCover
    have hedgeEq := d4CoveringPlacement_unique tiling
      ⟨ownerCell edge.source other, hotherPresent⟩ edge.1 edge.2.1 hedgeCover
    have heq : covering = edge.1 := hcoverEq.trans hedgeEq.symm
    have : covering.tile ≠ .stone := by simpa [heq] using edge.2.2.1
    exact (this hstone.1).elim
  · obtain ⟨previous, hprevious⟩ := hbone
    have hpreviousCover : D4PlacementCovers previous.1 cell := by
      rw [hprevious]
      exact hcoveringCovers
    rcases d4TilingEdge_cover_role previous edge.source edge.label
      (hsourceFull edge.label) hpreviousCover with hsource | htarget
    · obtain ⟨other, hcurrentOther, hpreviousOther⟩ :=
        microLabel_exists_ne_two edge.label previous.label
      have hotherPresent := hsourceFull other
      have hcurrentCover := d4TilingEdge_covers_source_other edge other
        hcurrentOther hotherPresent
      have hpreviousPresent : inBenzel (m + 4) (2 * m + 4)
          (ownerCell previous.source other) := by
        simpa [hsource.1] using hotherPresent
      have hpreviousOtherCover := d4TilingEdge_covers_source_other previous other
        hpreviousOther hpreviousPresent
      have hcurrentEq := d4CoveringPlacement_unique tiling
        ⟨ownerCell edge.source other, hotherPresent⟩ edge.1 edge.2.1
        hcurrentCover
      have hpreviousEq := d4CoveringPlacement_unique tiling
        ⟨ownerCell edge.source other, hotherPresent⟩ previous.1 previous.2.1 (by
          simpa [hsource.1] using hpreviousOtherCover)
      have hedgeEq : edge = previous := by
        apply Subtype.ext
        exact hcurrentEq.trans hpreviousEq.symm
      have : edge.label ≠ previous.label := by
        exact hsource.2
      exact (this (congrArg D4GoodBonePlacement.label hedgeEq)).elim
    · refine ⟨previous, ⟨htarget.1.symm, htarget.2.symm⟩, ?_⟩
      intro candidate hcandidate
      exact d4TilingEdge_target_label_unique candidate previous
        (hcandidate.1.trans htarget.1)
        (hcandidate.2.trans htarget.2)

theorem d4_boundary_predecessor_or_core (m : ℕ)
    (tiling : D4LiteralTiling m) (label : MicroLabel) :
    d4BoundaryOwner m label = d4DefectCore tiling label ∨
    ∃! previous : D4GoodBonePlacement tiling,
      previous.target = d4BoundaryOwner m label ∧ previous.label = label := by
  by_cases hcore : d4BoundaryOwner m label = d4DefectCore tiling label
  · exact Or.inl hcore
  · right
    let cell : D4Cell m :=
      ⟨ownerCell (d4BoundaryOwner m label) label,
        d4BoundaryOwner_present m label⟩
    let covering := d4CoveringPlacement tiling cell
    have hcoveringMem := d4CoveringPlacement_mem tiling cell
    have hcoveringCovers := d4CoveringPlacement_covers tiling cell
    rcases d4CoveringPlacement_classification tiling cell with hbad | hstone | hbone
    · have hbadCover : D4PlacementCovers (d4BadPlacement tiling) cell := by
        rw [← hbad]
        exact hcoveringCovers
      have hbadCore := d4_bad_cover_is_core tiling
        (d4BoundaryOwner m label) label (d4BoundaryOwner_present m label)
        hbadCover
      exact (hcore hbadCore).elim
    · have hstoneOwner := d4_good_stone_cover_owner covering hstone.1 hstone.2
        (d4BoundaryOwner m label) label (d4BoundaryOwner_present m label)
        hcoveringCovers
      have hfull := d4StoneOwner_full covering hstone.1 hstone.2
      obtain ⟨other, hne, _⟩ := microLabel_exists_ne_two label label
      have hotherPresent : inBenzel (m + 4) (2 * m + 4)
          (ownerCell (d4BoundaryOwner m label) other) := by
        rw [hstoneOwner]
        exact hfull other
      exact (hne ((d4BoundaryOwner_present_iff m label other).1
        hotherPresent)).elim
    · obtain ⟨previous, hprevious⟩ := hbone
      have hpreviousCover : D4PlacementCovers previous.1 cell := by
        rw [hprevious]
        exact hcoveringCovers
      rcases d4TilingEdge_cover_role previous (d4BoundaryOwner m label) label
        (d4BoundaryOwner_present m label) hpreviousCover with hsource | htarget
      · have hfull := d4TilingEdge_source_full previous
        obtain ⟨other, hne, _⟩ := microLabel_exists_ne_two label label
        have hotherPresent := hfull other
        exact (hne ((d4BoundaryOwner_present_iff m label other).1 (by
          simpa [hsource.1] using hotherPresent))).elim
      · refine ⟨previous, ⟨htarget.1.symm, htarget.2.symm⟩, ?_⟩
        intro candidate hcandidate
        exact d4TilingEdge_target_label_unique candidate previous
          (hcandidate.1.trans htarget.1)
          (hcandidate.2.trans htarget.2)

end FiniteDefects

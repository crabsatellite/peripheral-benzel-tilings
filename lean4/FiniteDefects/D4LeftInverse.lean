import FiniteDefects.D4Successor

/-! # Reconstructing extracted data returns the original literal tiling -/

namespace FiniteDefects

theorem extracted_pathPlacement_mem_original {m : ℕ}
    (tiling : D4LiteralTiling m)
    (placement : D4LiteralPlacement m)
    (hmem : placement ∈
      (d4ExtractedPathData tiling).pathPlacements) :
    placement ∈ tiling.1 := by
  obtain ⟨label, edge, hedge, hedgePlacement⟩ :=
    (d4ExtractedPathData tiling).pathPlacement_witness placement hmem
  change edge ∈ (d4ReverseBoundaryPath tiling label).map
    D4GoodBonePlacement.edge at hedge
  obtain ⟨goodEdge, hgoodMem, hedgeEq⟩ := List.mem_map.mp hedge
  rw [← hedgePlacement, ← hedgeEq]
  exact goodEdge.2.1

theorem extracted_unusedStone_mem_original {m : ℕ}
    (tiling : D4LiteralTiling m)
    (owner : D4UnusedFullOwner (d4ExtractedPathData tiling)) :
    d4ReverseStonePlacement owner.1 owner.2.1 ∈ tiling.1 := by
  let cell : D4Cell m :=
    ⟨ownerCell owner.1 .zero, owner.2.1 .zero⟩
  let covering := d4CoveringPlacement tiling cell
  have hcoveringMem := d4CoveringPlacement_mem tiling cell
  have hcoveringCovers := d4CoveringPlacement_covers tiling cell
  rcases d4CoveringPlacement_classification tiling cell with hbad | hstone | hbone
  · have hbadCover : D4PlacementCovers (d4BadPlacement tiling) cell := by
      rw [← hbad]
      exact hcoveringCovers
    have hcore := d4_bad_cover_is_core tiling owner.1 .zero
      (owner.2.1 .zero) hbadCover
    apply False.elim
    apply owner.2.2
    refine ⟨.zero, ?_⟩
    change D4AbstractPathVisits (d4BoundaryOwner m .zero)
      ((d4TilingDefect tiling).core .zero)
      ((d4ExtractedPathData tiling).paths .zero) owner.1
    rw [d4TilingDefect_core tiling .zero]
    exact Or.inr (Or.inl hcore)
  · have howner := d4_good_stone_cover_owner covering hstone.1 hstone.2
      owner.1 .zero (owner.2.1 .zero) hcoveringCovers
    have heq : d4ReverseStonePlacement owner.1 owner.2.1 = covering := by
      apply Subtype.ext
      apply Prod.ext
      · exact hstone.1.symm
      · apply Subtype.ext
        have hbase := d4InPhaseStone_base_eq_owner covering hstone.1 hstone.2
        change (d4ReverseStonePlacement owner.1 owner.2.1).base = covering.base
        rw [d4ReverseStonePlacement_base, hbase, howner]
    rw [heq]
    exact hcoveringMem
  · obtain ⟨goodEdge, hgoodEq⟩ := hbone
    have hgoodCover : D4PlacementCovers goodEdge.1 cell := by
      rw [hgoodEq]
      exact hcoveringCovers
    rcases d4TilingEdge_cover_role goodEdge owner.1 .zero
      (owner.2.1 .zero) hgoodCover with hsource | htarget
    · let endpoint := d4EdgeCanonicalEndpoint goodEdge
      apply False.elim
      apply owner.2.2
      refine ⟨endpoint.1, ?_⟩
      change D4AbstractPathVisits (d4BoundaryOwner m endpoint.1)
        ((d4TilingDefect tiling).core endpoint.1)
        ((d4ReverseBoundaryPath tiling endpoint.1).map
          D4GoodBonePlacement.edge) owner.1
      rw [d4TilingDefect_core tiling endpoint.1]
      exact Or.inr (Or.inr ⟨goodEdge.edge,
        List.mem_map.mpr ⟨goodEdge, endpoint.2.2, rfl⟩,
        Or.inl hsource.1⟩)
    · let endpoint := d4EdgeCanonicalEndpoint goodEdge
      apply False.elim
      apply owner.2.2
      refine ⟨endpoint.1, ?_⟩
      change D4AbstractPathVisits (d4BoundaryOwner m endpoint.1)
        ((d4TilingDefect tiling).core endpoint.1)
        ((d4ReverseBoundaryPath tiling endpoint.1).map
          D4GoodBonePlacement.edge) owner.1
      rw [d4TilingDefect_core tiling endpoint.1]
      exact Or.inr (Or.inr ⟨goodEdge.edge,
        List.mem_map.mpr ⟨goodEdge, endpoint.2.2, rfl⟩,
        Or.inr htarget.1⟩)

theorem extracted_selected_subset_original {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ExtractedPathData tiling).selectedPlacements ⊆ tiling.1 := by
  intro placement hmem
  simp only [D4DefectPathData.selectedPlacements, Finset.mem_insert,
    Finset.mem_union] at hmem
  rcases hmem with hdefect | hpath | hstone
  · rw [hdefect]
    change d4BadPlacement tiling ∈ tiling.1
    exact d4BadPlacement_mem tiling
  · exact extracted_pathPlacement_mem_original tiling placement hpath
  · obtain ⟨owner, howner⟩ :=
      (d4ExtractedPathData tiling).stonePlacement_witness placement hstone
    rw [← howner]
    exact extracted_unusedStone_mem_original tiling owner

theorem reconstructed_extracted_tiling {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4ReconstructedTiling (d4ExtractedPathData tiling) = tiling := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · exact extracted_selected_subset_original tiling
  · have hleft := d4_literal_tiling_card
      (d4ReconstructedTiling (d4ExtractedPathData tiling))
    have hright := d4_literal_tiling_card tiling
    have hselected :
        (d4ExtractedPathData tiling).selectedPlacements.card =
          (m + 4).choose 2 - 2 := by
      exact hleft
    change tiling.1.card ≤
      (d4ExtractedPathData tiling).selectedPlacements.card
    omega

noncomputable def d4LiteralTilingEquivPathData (m : ℕ) :
    D4LiteralTiling m ≃ D4DefectPathData m where
  toFun := d4ExtractedPathData
  invFun := d4ReconstructedTiling
  left_inv := reconstructed_extracted_tiling
  right_inv := reconstructed_extraction

end FiniteDefects

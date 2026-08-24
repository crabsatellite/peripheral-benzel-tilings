import BenzelProblem6Kernel.RootedAlternatingBoundary

/-! # Construct one literal geometric splice from a shared edge occurrence -/

namespace BenzelProblem6Kernel

theorem exists_geometricTileBoundarySplice_of_shared_edge
    {m : ℕ} (region : RootedAlternatingBoundary)
    (placement : LiteralPlacement m) (sharedEdge : LabeledHexEdge)
    (hregion : sharedEdge ∈ region.edges)
    (htile : sharedEdge ∈ literalPlacementBoundary placement) :
    ∃ splice : GeometricTileBoundarySplice m,
      splice.boundary = region.edges ∧
      splice.placement = placement ∧
      splice.sharedEdge = sharedEdge := by
  obtain ⟨boundaryPrefix, boundarySuffix, hboundary⟩ :=
    List.mem_iff_append.mp hregion
  obtain ⟨tilePrefix, tileSuffix, htileBoundary⟩ :=
    List.mem_iff_append.mp htile
  have heven := region.factorPathEven_of_decompositions
    (literalPlacementRootedBoundary placement)
    boundaryPrefix boundarySuffix tilePrefix tileSuffix sharedEdge
    hboundary htileBoundary
  let splice : GeometricTileBoundarySplice m :=
    { boundary := region.edges
      placement := placement
      boundaryPrefix := boundaryPrefix
      boundarySuffix := boundarySuffix
      tilePrefix := tilePrefix
      tileSuffix := tileSuffix
      sharedEdge := sharedEdge
      boundary_eq := hboundary
      tile_eq := htileBoundary
      factor_path_even := heven }
  exact ⟨splice, rfl, rfl, rfl⟩

structure AvailableGeometricTileSplice {m : ℕ}
    (region : RootedAlternatingBoundary)
    (placement : LiteralPlacement m) (sharedEdge : LabeledHexEdge) where
  splice : GeometricTileBoundarySplice m
  boundary_exact : splice.boundary = region.edges
  placement_exact : splice.placement = placement
  edge_exact : splice.sharedEdge = sharedEdge

theorem availableGeometricTileSplice_nonempty
    {m : ℕ} (region : RootedAlternatingBoundary)
    (placement : LiteralPlacement m) (sharedEdge : LabeledHexEdge)
    (hregion : sharedEdge ∈ region.edges)
    (htile : sharedEdge ∈ literalPlacementBoundary placement) :
    Nonempty (AvailableGeometricTileSplice region placement sharedEdge) := by
  obtain ⟨splice, hboundary, hplacement, hedge⟩ :=
    exists_geometricTileBoundarySplice_of_shared_edge
      region placement sharedEdge hregion htile
  exact ⟨⟨splice, hboundary, hplacement, hedge⟩⟩

end BenzelProblem6Kernel

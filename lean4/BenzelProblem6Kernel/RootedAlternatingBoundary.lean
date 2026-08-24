import BenzelProblem6Kernel.HoneycombEdgePathParity

/-! # Rooted alternating closed boundary walks -/

namespace BenzelProblem6Kernel

theorem literalPrototypeBoundary_walkEnd
    (tile : ProtoTile) (base : Cell) :
    labeledHexWalkEnd (prototypeBoundaryStart tile base)
        (prototypeBoundarySteps tile) =
      prototypeBoundaryStart tile base := by
  rcases base with ⟨i, j⟩
  cases tile <;>
    simp [labeledHexWalkEnd, prototypeBoundaryStart,
      prototypeBoundarySteps, addHexStep, hexCellCenter,
      ShadowStep.neg, shadowA, shadowB, shadowC] <;> ring <;> simp

theorem literalPrototypeBoundary_continuous
    (tile : ProtoTile) (base : Cell) :
    ContinuousLabeledEdgePath (prototypeBoundaryStart tile base)
      (literalPrototypeBoundary tile base)
      (prototypeBoundaryStart tile base) := by
  rw [literalPrototypeBoundary]
  simpa [literalPrototypeBoundary_walkEnd] using
    walkLabeledHexEdges_continuous
      (prototypeBoundaryStart tile base) (prototypeBoundarySteps tile)

theorem prototypeBoundaryStart_classZero
    (tile : ProtoTile) (base : Cell) :
    hexVertexClassZero (prototypeBoundaryStart tile base) = true := by
  rcases base with ⟨i, j⟩
  cases tile <;>
    simp [hexVertexClassZero, prototypeBoundaryStart,
      hexCellCenter] <;> omega

theorem edge_mem_labeledCellBoundary_alternates
    (cell : Cell) {edge : LabeledHexEdge}
    (hedge : edge ∈ labeledCellBoundary cell) :
    AlternatesHexVertexClass edge := by
  rw [labeledCellBoundary_eq_allEdges] at hedge
  simp [allCellBoundaryEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact cellBoundaryEdgeAt_alternates cell _

theorem literalPrototypeBoundary_subset_cellBoundaries
    (tile : ProtoTile) (base : Cell) :
    literalPrototypeBoundary tile base ⊆
      orientedPrototypeCellBoundaryList tile base := by
  intro edge hedge
  have hcanonicalSubset :
      literalPrototypeBoundary tile (0, 0) ⊆
        orientedPrototypeCellBoundaryList tile (0, 0) := by
    intro canonicalEdge hcanonicalEdge
    exact (canonical_oriented_perm tile).symm.subset
      (List.mem_append_left _ hcanonicalEdge)
  have hbase : base = translateCell base (0, 0) := by
    rcases base with ⟨i, j⟩
    simp [translateCell]
  rw [hbase, literalPrototypeBoundary_translate] at hedge
  obtain ⟨canonicalEdge, hcanonicalEdge, hedgeEq⟩ := List.mem_map.mp hedge
  rw [orientedPrototypeCellBoundaryList_translate]
  exact List.mem_map.mpr
    ⟨canonicalEdge, hcanonicalSubset hcanonicalEdge, hedgeEq⟩

theorem literalPrototypeBoundary_edges_alternate
    (tile : ProtoTile) (base : Cell) :
    ∀ edge ∈ literalPrototypeBoundary tile base,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  have hcellList := literalPrototypeBoundary_subset_cellBoundaries
    tile base hedge
  simp only [orientedPrototypeCellBoundaryList,
    orientedCellBoundaryList, List.mem_flatMap] at hcellList
  obtain ⟨cell, hcell, hedgeCell⟩ := hcellList
  exact edge_mem_labeledCellBoundary_alternates cell hedgeCell

structure RootedAlternatingBoundary where
  edges : List LabeledHexEdge
  root : HexVertex
  continuous : ContinuousLabeledEdgePath root edges root
  root_classZero : hexVertexClassZero root = true
  alternates : ∀ edge ∈ edges, AlternatesHexVertexClass edge

def literalPlacementRootedBoundary {m : ℕ}
    (placement : LiteralPlacement m) :
    RootedAlternatingBoundary where
  edges := literalPlacementBoundary placement
  root := prototypeBoundaryStart placement.tile placement.base
  continuous := literalPrototypeBoundary_continuous
    placement.tile placement.base
  root_classZero := prototypeBoundaryStart_classZero
    placement.tile placement.base
  alternates := literalPrototypeBoundary_edges_alternate
    placement.tile placement.base

theorem RootedAlternatingBoundary.factorPathEven_of_decompositions
    (region tile : RootedAlternatingBoundary)
    (boundaryPrefix boundarySuffix tilePrefix tileSuffix :
      List LabeledHexEdge)
    (sharedEdge : LabeledHexEdge)
    (hboundary : region.edges =
      boundaryPrefix ++ sharedEdge :: boundarySuffix)
    (htile : tile.edges = tilePrefix ++ sharedEdge :: tileSuffix) :
    EvenShadowLabelWord
      (labeledEdgeWord boundaryPrefix ++
        (labeledEdgeWord tilePrefix).reverse) := by
  have hregionPath : ContinuousLabeledEdgePath region.root
      boundaryPrefix sharedEdge.source := by
    have path := region.continuous
    rw [hboundary] at path
    exact path.prefix_before_edge
  have htilePath : ContinuousLabeledEdgePath tile.root
      tilePrefix sharedEdge.source := by
    have path := tile.continuous
    rw [htile] at path
    exact path.prefix_before_edge
  have hregionAlt : ∀ edge ∈ boundaryPrefix,
      AlternatesHexVertexClass edge := by
    intro edge hedge
    exact region.alternates edge (by
      rw [hboundary]
      simp [hedge])
  have htileAlt : ∀ edge ∈ tilePrefix,
      AlternatesHexVertexClass edge := by
    intro edge hedge
    exact tile.alternates edge (by
      rw [htile]
      simp [hedge])
  apply evenShadowWord_of_even_edgePrefixSum boundaryPrefix tilePrefix
  exact even_prefix_sum_of_common_endpoint hregionPath htilePath
    (region.root_classZero.trans tile.root_classZero.symm)
    hregionAlt htileAlt

def RootedAlternatingBoundary.spliceRemaining
    {m : ℕ} (region : RootedAlternatingBoundary)
    (splice : GeometricTileBoundarySplice m)
    (hboundary : splice.boundary = region.edges) :
    RootedAlternatingBoundary where
  edges := splice.remainingBoundary
  root := region.root
  continuous := by
    let tile := literalPlacementRootedBoundary splice.placement
    have regionPath := region.continuous
    rw [← hboundary, splice.boundary_eq] at regionPath
    have regionPrefix := regionPath.prefix_before_edge
    have regionSuffix := regionPath.suffix_after_edge
    have tilePath := tile.continuous
    change ContinuousLabeledEdgePath tile.root
      (literalPlacementBoundary splice.placement) tile.root at tilePath
    rw [splice.tile_eq] at tilePath
    have tilePrefix := tilePath.prefix_before_edge
    have tileSuffix := tilePath.suffix_after_edge
    have rotatedRest : ContinuousLabeledEdgePath splice.sharedEdge.target
        splice.rotatedTileRest splice.sharedEdge.source := by
      exact tileSuffix.append tilePrefix
    have reversedRest := rotatedRest.reverse
    have combined := (regionPrefix.append reversedRest).append regionSuffix
    simpa [GeometricTileBoundarySplice.remainingBoundary,
      GeometricTileBoundarySplice.rotatedTileRest,
      List.reverse_append, List.map_append, List.append_assoc] using combined
  root_classZero := region.root_classZero
  alternates := by
    intro edge hedge
    rw [GeometricTileBoundarySplice.remainingBoundary] at hedge
    rcases List.mem_append.mp hedge with hedge | hedge
    · rcases List.mem_append.mp hedge with hedge | hedge
      · exact region.alternates edge (by
          rw [← hboundary, splice.boundary_eq]
          simp [hedge])
      · obtain ⟨original, horiginal, hedgeEq⟩ := List.mem_map.mp hedge
        have horiginal' : original ∈ splice.rotatedTileRest :=
          List.mem_reverse.mp horiginal
        rw [← hedgeEq]
        apply reverseLabeledHexEdge_alternates
        let tile := literalPlacementRootedBoundary splice.placement
        apply tile.alternates original
        change original ∈ literalPlacementBoundary splice.placement
        rw [splice.tile_eq]
        change original ∈ splice.tileSuffix ++ splice.tilePrefix at horiginal'
        rw [List.mem_append] at horiginal'
        rcases horiginal' with hsuffix | hprefix
        · exact List.mem_append_right _ (by simp [hsuffix])
        · exact List.mem_append_left _ hprefix
    · exact region.alternates edge (by
        rw [← hboundary, splice.boundary_eq]
        simp [hedge])

end BenzelProblem6Kernel

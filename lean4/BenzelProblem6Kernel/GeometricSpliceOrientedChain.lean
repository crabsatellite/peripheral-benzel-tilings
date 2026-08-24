import BenzelProblem6Kernel.GeometricBacktrackOrientedChain

/-! # A geometric splice subtracts exactly one placement boundary chain -/

namespace BenzelProblem6Kernel

theorem geometricTileBoundarySplice_rotated_perm
    {m : ℕ} (splice : GeometricTileBoundarySplice m) :
    List.Perm (literalPlacementBoundary splice.placement)
      (splice.sharedEdge :: splice.rotatedTileRest) := by
  rw [splice.tile_eq]
  simpa [GeometricTileBoundarySplice.rotatedTileRest,
    List.append_assoc] using
      (List.perm_append_comm : List.Perm
        (splice.tilePrefix ++ splice.sharedEdge :: splice.tileSuffix)
        ((splice.sharedEdge :: splice.tileSuffix) ++ splice.tilePrefix))

theorem geometricTileBoundarySplice_remaining_coefficient
    {m : ℕ} (splice : GeometricTileBoundarySplice m)
    (edge : LabeledHexEdge) :
    directedEdgeCoefficient splice.remainingBoundary edge =
      directedEdgeCoefficient splice.boundary edge -
        directedEdgeCoefficient
          (literalPlacementBoundary splice.placement) edge := by
  have htile := SameOrientedBoundaryChain.perm
    (geometricTileBoundarySplice_rotated_perm splice)
  have htileCoeff := htile edge
  rw [GeometricTileBoundarySplice.remainingBoundary,
    directedEdgeCoefficient_append,
    directedEdgeCoefficient_append,
    directedEdgeCoefficient_reverse]
  rw [splice.boundary_eq,
    directedEdgeCoefficient_append]
  have hshared :
      directedEdgeCoefficient
          (splice.sharedEdge :: splice.boundarySuffix) edge =
        directedEdgeCoefficient [splice.sharedEdge] edge +
          directedEdgeCoefficient splice.boundarySuffix edge := by
    simpa using directedEdgeCoefficient_append
      [splice.sharedEdge] splice.boundarySuffix edge
  have hrotated :
      directedEdgeCoefficient
          (splice.sharedEdge :: splice.rotatedTileRest) edge =
        directedEdgeCoefficient [splice.sharedEdge] edge +
          directedEdgeCoefficient splice.rotatedTileRest edge := by
    simpa using directedEdgeCoefficient_append
      [splice.sharedEdge] splice.rotatedTileRest edge
  rw [hrotated] at htileCoeff
  rw [hshared, htileCoeff]
  ring

theorem geometricTileBoundarySplice_reduced_coefficient
    {m : ℕ} (splice : GeometricTileBoundarySplice m)
    (edge : LabeledHexEdge) :
    directedEdgeCoefficient
        (reduceGeometricBacktracks splice.remainingBoundary) edge =
      directedEdgeCoefficient splice.boundary edge -
        directedEdgeCoefficient
          (literalPlacementBoundary splice.placement) edge := by
  rw [← geometricTileBoundarySplice_remaining_coefficient splice edge]
  exact (reduceGeometricBacktracks_same_chain
    splice.remainingBoundary edge).symm

end BenzelProblem6Kernel

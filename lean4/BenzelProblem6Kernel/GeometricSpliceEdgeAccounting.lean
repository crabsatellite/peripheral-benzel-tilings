import BenzelProblem6Kernel.RightmostPeelingTrace
import Mathlib.Data.List.Count

/-! # Exact physical-edge accounting through geometric splices -/

namespace BenzelProblem6Kernel

def reverseReorientedEdges (edges : List LabeledHexEdge) :
    List LabeledHexEdge :=
  edges.reverse.map reverseLabeledHexEdge

def selectedEdgePair (edge : LabeledHexEdge) :
    List LabeledHexEdge :=
  [edge, reverseLabeledHexEdge edge]

theorem geometricTileBoundarySplice_edge_perm {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    List.Perm
      (splice.boundary ++
        reverseReorientedEdges
          (literalPlacementBoundary splice.placement))
      (splice.remainingBoundary ++ selectedEdgePair splice.sharedEdge) := by
  classical
  rw [splice.boundary_eq, splice.tile_eq]
  simp only [reverseReorientedEdges,
    GeometricTileBoundarySplice.remainingBoundary,
    GeometricTileBoundarySplice.rotatedTileRest,
    List.reverse_append, List.reverse_cons, List.map_append,
    List.map_cons, List.map_nil]
  apply List.perm_iff_count.mpr
  intro edge
  simp only [selectedEdgePair, List.count_append,
    List.count_cons, List.count_nil]
  omega

def RightmostPeelingSkeleton.reverseTileBoundaries {m : ℕ} :
    {region : RootedAlternatingBoundary} →
    {placements : Finset (LiteralPlacement m)} →
      RightmostPeelingSkeleton m region placements →
        List LabeledHexEdge
  | _, _, .done _ => []
  | _, _, .peel _ _ splice _ _ _ _ _ _ _ rest =>
      reverseReorientedEdges
        (literalPlacementBoundary splice.placement) ++
          rest.reverseTileBoundaries

def RightmostPeelingSkeleton.selectedEdgePairs {m : ℕ} :
    {region : RootedAlternatingBoundary} →
    {placements : Finset (LiteralPlacement m)} →
      RightmostPeelingSkeleton m region placements →
        List LabeledHexEdge
  | _, _, .done _ => []
  | _, _, .peel _ _ splice _ _ _ _ _ _ _ rest =>
      rest.selectedEdgePairs ++ selectedEdgePair splice.sharedEdge

theorem RightmostPeelingSkeleton.edge_accounting_perm {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    List.Perm
      (region.edges ++ skeleton.reverseTileBoundaries)
      (skeleton.terminalRegion.edges ++ skeleton.selectedEdgePairs) := by
  induction skeleton with
  | done => rfl
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.reverseTileBoundaries,
        RightmostPeelingSkeleton.selectedEdgePairs,
        RightmostPeelingSkeleton.terminalRegion]
      rw [← List.append_assoc]
      have hlocal := geometricTileBoundarySplice_edge_perm splice
      rw [boundary_exact] at hlocal
      have hlocalRest := hlocal.append_right rest.reverseTileBoundaries
      have hswap : List.Perm
          (splice.remainingBoundary ++
            selectedEdgePair splice.sharedEdge ++
              rest.reverseTileBoundaries)
          (splice.remainingBoundary ++
            rest.reverseTileBoundaries ++
              selectedEdgePair splice.sharedEdge) := by
        simpa [List.append_assoc] using
          ((List.perm_append_comm : List.Perm
            (selectedEdgePair splice.sharedEdge ++
              rest.reverseTileBoundaries)
            (rest.reverseTileBoundaries ++
              selectedEdgePair splice.sharedEdge)).append_left
                splice.remainingBoundary)
      have ihPair := ih.append_right
        (selectedEdgePair splice.sharedEdge)
      simpa [RootedAlternatingBoundary.spliceRemaining,
        List.append_assoc] using hlocalRest.trans hswap |>.trans ihPair

end BenzelProblem6Kernel

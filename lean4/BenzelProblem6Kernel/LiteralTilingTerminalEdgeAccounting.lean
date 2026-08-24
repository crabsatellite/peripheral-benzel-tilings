import BenzelProblem6Kernel.TilingComplexEdgePairs
import BenzelProblem6Kernel.LiteralTilingPeelingSkeleton

/-! # Exact terminal edge accounting for the literal rightmost skeleton -/

namespace BenzelProblem6Kernel

theorem RightmostPeelingSkeleton.reverseTileBoundaries_eq {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    skeleton.reverseTileBoundaries =
      reverseLiteralPlacementBoundaryList skeleton.removedPlacements := by
  induction skeleton with
  | done => rfl
  | peel region placements splice boundary_exact placement_mem
      selectedCell selectedCell_mem sharedEdge_exact neighbor_outside
      selectedCell_not_remaining rest ih =>
      simp only [RightmostPeelingSkeleton.reverseTileBoundaries,
        RightmostPeelingSkeleton.removedPlacements,
        reverseLiteralPlacementBoundaryList, List.flatMap_cons]
      exact congrArg
        (fun tail => reverseReorientedEdges
          (literalPlacementBoundary splice.placement) ++ tail) ih

theorem RightmostPeelingSkeleton.reverseTileBoundaries_perm_initial {m : ℕ}
    {region : RootedAlternatingBoundary}
    {placements : Finset (LiteralPlacement m)}
    (skeleton : RightmostPeelingSkeleton m region placements) :
    List.Perm skeleton.reverseTileBoundaries
      (reverseLiteralPlacementBoundaryList placements.toList) := by
  rw [skeleton.reverseTileBoundaries_eq]
  exact (skeleton.removedPlacements_perm.map
    (fun placement => reverseReorientedEdges
      (literalPlacementBoundary placement))).flatten

theorem literalTilingTerminal_edgeAccounting_perm {m : ℕ}
    (tiling : LiteralTiling m) :
    List.Perm (literalTilingComplexDirectedEdges tiling)
      ((literalTilingRightmostTerminal tiling).edges ++
        (literalTilingRightmostSkeleton tiling).selectedEdgePairs) := by
  let skeleton := literalTilingRightmostSkeleton tiling
  have hreverse : List.Perm
      (reverseLiteralPlacementBoundaryList tiling.1.toList)
      skeleton.reverseTileBoundaries :=
    skeleton.reverseTileBoundaries_perm_initial.symm
  have hinitial : List.Perm
      (literalReducedPeripheralBoundary m ++
        reverseLiteralPlacementBoundaryList tiling.1.toList)
      (literalReducedPeripheralBoundary m ++
        skeleton.reverseTileBoundaries) :=
    hreverse.append_left _
  have haccount := skeleton.edge_accounting_perm
  exact hinitial.trans haccount

theorem literalTilingTerminal_append_selected_nodup {m : ℕ}
    (tiling : LiteralTiling m) :
    ((literalTilingRightmostTerminal tiling).edges ++
      (literalTilingRightmostSkeleton tiling).selectedEdgePairs).Nodup := by
  exact (literalTilingComplexDirectedEdges_nodup tiling).perm
    (literalTilingTerminal_edgeAccounting_perm tiling)

theorem literalTilingRightmostTerminal_nodup {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingRightmostTerminal tiling).edges.Nodup :=
  (List.nodup_append.mp
    (literalTilingTerminal_append_selected_nodup tiling)).1

theorem literalTilingRightmostTerminal_disjoint_selected {m : ℕ}
    (tiling : LiteralTiling m) :
    List.Disjoint (literalTilingRightmostTerminal tiling).edges
      (literalTilingRightmostSkeleton tiling).selectedEdgePairs :=
  (List.nodup_append.mp
    (literalTilingTerminal_append_selected_nodup tiling)).2.2

end BenzelProblem6Kernel

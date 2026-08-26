import D4KernelOnly.D4TilingCellPermutation
import BenzelProblem6Kernel.OrientedTilingCellBoundary

/-! # Exact cancellation of all internal d=4 placement edges -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4ShadowPlacementBoundaries_eq_d4CellBoundaries {m : ℕ}
    (tiling : D4LiteralTiling m) :
    SameOrientedBoundaryChain
      (literalPlacementBoundaryList (d4ShadowPlacementList tiling))
      (orientedCellBoundaryList (d4CellValueList m)) := by
  have hgrouped :=
    (orientedCellBoundaryList_flatMap_placements
      (d4ShadowPlacementList tiling)).symm
  have hflatten :
      (d4ShadowPlacementList tiling).flatMap
          BenzelProblem6Kernel.LiteralPlacement.cells =
        d4TilingCellList tiling :=
    d4ShadowPlacementList_cells tiling
  have hcells : SameOrientedBoundaryChain
      (orientedCellBoundaryList
        ((d4ShadowPlacementList tiling).flatMap
          BenzelProblem6Kernel.LiteralPlacement.cells))
      (orientedCellBoundaryList (d4CellValueList m)) := by
    rw [hflatten]
    exact orientedCellBoundaryList_perm
      (d4TilingCellList_perm_d4Cells tiling)
  exact hgrouped.trans hcells

end FiniteDefects

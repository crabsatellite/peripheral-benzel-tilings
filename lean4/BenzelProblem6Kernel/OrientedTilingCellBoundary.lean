import BenzelProblem6Kernel.OrientedPlacementBoundaryCancellation

/-! # The oriented sum of placement boundaries equals the benzel cell sum -/

namespace BenzelProblem6Kernel

def literalPlacementBoundaryList {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    List LabeledHexEdge :=
  placements.flatMap literalPlacementBoundary

theorem orientedCellBoundaryList_append
    (left right : List Cell) :
    orientedCellBoundaryList (left ++ right) =
      orientedCellBoundaryList left ++ orientedCellBoundaryList right := by
  simp [orientedCellBoundaryList, List.flatMap_append]

theorem orientedCellBoundaryList_flatMap_placements {m : ℕ}
    (placements : List (LiteralPlacement m)) :
    SameOrientedBoundaryChain
      (orientedCellBoundaryList
        (placements.flatMap LiteralPlacement.cells))
      (literalPlacementBoundaryList placements) := by
  induction placements with
  | nil => exact SameOrientedBoundaryChain.refl []
  | cons placement rest ih =>
      simp only [List.flatMap_cons, literalPlacementBoundaryList,
        orientedCellBoundaryList_append]
      exact (oriented_literalPlacement_boundary_cancel placement).append ih

theorem orientedCellBoundaryList_perm
    {left right : List Cell} (hperm : List.Perm left right) :
    SameOrientedBoundaryChain
      (orientedCellBoundaryList left)
      (orientedCellBoundaryList right) := by
  have hedgePerm : List.Perm
      (left.flatMap labeledCellBoundary)
      (right.flatMap labeledCellBoundary) := by
    simpa [List.flatMap] using (hperm.map labeledCellBoundary).flatten
  exact SameOrientedBoundaryChain.perm hedgePerm

theorem literalTilingPlacementBoundaries_eq_benzelCellBoundaries
    {m : ℕ} (tiling : LiteralTiling m) :
    SameOrientedBoundaryChain
      (literalPlacementBoundaryList tiling.1.toList)
      (orientedCellBoundaryList (benzelCellValueList m)) := by
  have hgrouped :=
    (orientedCellBoundaryList_flatMap_placements tiling.1.toList).symm
  have hcells : SameOrientedBoundaryChain
      (orientedCellBoundaryList
        (tiling.1.toList.flatMap LiteralPlacement.cells))
      (orientedCellBoundaryList (benzelCellValueList m)) :=
    orientedCellBoundaryList_perm (tilingCellList_perm_benzelCells tiling)
  exact hgrouped.trans hcells

end BenzelProblem6Kernel

import BenzelProblem6Kernel.CanonicalOrientedBoundaryCancellation

/-! # Translation of oriented boundary cancellation to every placement -/

namespace BenzelProblem6Kernel

theorem orientedCellBoundaryList_translate
    (offset : Cell) (cells : List Cell) :
    orientedCellBoundaryList (cells.map (translateCell offset)) =
      (orientedCellBoundaryList cells).map
        (translateLabeledHexEdge (hexVertexTranslation offset)) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      change (rest.map (translateCell offset)).flatMap labeledCellBoundary =
        (rest.flatMap labeledCellBoundary).map
          (translateLabeledHexEdge (hexVertexTranslation offset)) at ih
      simp only [List.map_cons, orientedCellBoundaryList,
        List.flatMap_cons, List.map_append]
      rw [labeledCellBoundary_translate, ih]

theorem orientedPrototypeCellBoundaryList_translate
    (tile : ProtoTile) (base : Cell) :
    orientedPrototypeCellBoundaryList tile base =
      (orientedPrototypeCellBoundaryList tile (0, 0)).map
        (translateLabeledHexEdge (hexVertexTranslation base)) := by
  rw [orientedPrototypeCellBoundaryList,
    orientedPrototypeCellBoundaryList,
    prototypeCells_translate,
    orientedCellBoundaryList_translate]

theorem oriented_prototype_boundary_cancel
    (tile : ProtoTile) (base : Cell) :
    SameOrientedBoundaryChain
      (orientedPrototypeCellBoundaryList tile base)
      (literalPrototypeBoundary tile base) := by
  have htranslated :=
    (canonical_oriented_boundary_cancel tile).translate
      (hexVertexTranslation base)
  rw [← orientedPrototypeCellBoundaryList_translate,
    ← literalPrototypeBoundary_translate] at htranslated
  simpa [translateCell] using htranslated

theorem oriented_literalPlacement_boundary_cancel
    {m : ℕ} (placement : LiteralPlacement m) :
    SameOrientedBoundaryChain
      (orientedCellBoundaryList placement.cells)
      (literalPlacementBoundary placement) := by
  exact oriented_prototype_boundary_cancel
    placement.tile placement.base

end BenzelProblem6Kernel

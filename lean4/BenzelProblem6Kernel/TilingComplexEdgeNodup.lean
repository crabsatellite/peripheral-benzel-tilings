import BenzelProblem6Kernel.ExposedPlacementEdgeAllSides
import BenzelProblem6Kernel.TilingBoundaryNodup

/-! # Directed uniqueness of the complete tiling-complex edge list -/

namespace BenzelProblem6Kernel

theorem mem_reverseReorientedEdges_iff
    (edge : LabeledHexEdge) (edges : List LabeledHexEdge) :
    edge ∈ reverseReorientedEdges edges ↔
      reverseLabeledHexEdge edge ∈ edges := by
  simp only [reverseReorientedEdges, List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨original, horiginal, hedge⟩
    have horiginalEq : original = reverseLabeledHexEdge edge := by
      simpa [reverseLabeledHexEdge_involutive] using
        congrArg reverseLabeledHexEdge hedge
    rwa [← horiginalEq]
  · intro hedge
    exact ⟨reverseLabeledHexEdge edge, hedge,
      reverseLabeledHexEdge_involutive edge⟩

theorem mem_literalReducedPeripheralBoundary_exists_datum
    {m : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ literalReducedPeripheralBoundary m) :
    ∃ datum ∈ literalPeripheralIncidences m,
      cellSideBoundaryEdge datum = edge := by
  simp only [literalReducedPeripheralBoundary, List.mem_map,
    List.mem_reverse] at hedge
  exact hedge

theorem literalReducedBoundary_disjoint_reversePlacement {m : ℕ}
    (placement : LiteralPlacement m) :
    List.Disjoint (literalReducedPeripheralBoundary m)
      (reverseReorientedEdges
        (literalPlacementBoundary placement)) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTile
  obtain ⟨datum, hdatum, hedgeDatum⟩ :=
    mem_literalReducedPeripheralBoundary_exists_datum hedgeOuter
  have hreverseTile : reverseLabeledHexEdge edge ∈
      literalPlacementBoundary placement :=
    (mem_reverseReorientedEdges_iff edge _).mp hedgeTile
  obtain ⟨owner, howner, hownerEdge⟩ :=
    literalPlacementBoundary_edge_has_cell placement hreverseTile
  have hedgeAt : cellBoundaryEdgeAt datum.1 datum.2 = edge :=
    hedgeDatum
  have hownerEdge' : reverseLabeledHexEdge
      (cellBoundaryEdgeAt datum.1 datum.2) ∈
        labeledCellBoundary owner := by
    rwa [hedgeAt]
  have hownerEq : owner = neighboringCell datum.1 datum.2 :=
    (reverse_edge_mem_labeledCellBoundary_iff
      datum.1 owner datum.2).mp hownerEdge'
  have hinside := (isInsidePeripheralEdge_iff_mem
    m datum.1 datum.2).mpr hdatum
  exact hinside.2 (by
    rw [← hownerEq]
    exact placement.2 owner howner)

theorem literalReducedBoundary_disjoint_reverseTiling {m : ℕ}
    (tiling : LiteralTiling m) :
    List.Disjoint (literalReducedPeripheralBoundary m)
      (reverseLiteralPlacementBoundaryList tiling.1.toList) := by
  rw [List.disjoint_left]
  intro edge hedgeOuter hedgeTiles
  rw [reverseLiteralPlacementBoundaryList,
    List.mem_flatMap] at hedgeTiles
  obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
  exact (List.disjoint_left.mp
    (literalReducedBoundary_disjoint_reversePlacement placement))
      hedgeOuter hedgePlacement

noncomputable def literalTilingComplexDirectedEdges {m : ℕ}
    (tiling : LiteralTiling m) : List LabeledHexEdge :=
  literalReducedPeripheralBoundary m ++
    reverseLiteralPlacementBoundaryList tiling.1.toList

theorem literalTilingComplexDirectedEdges_nodup {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingComplexDirectedEdges tiling).Nodup := by
  rw [literalTilingComplexDirectedEdges, List.nodup_append]
  exact ⟨literalReducedPeripheralBoundary_nodup m,
    reverseLiteralPlacementBoundaryList_nodup tiling,
    literalReducedBoundary_disjoint_reverseTiling tiling⟩

end BenzelProblem6Kernel

import BenzelProblem6Kernel.GeometricSpliceEdgeAccounting
import BenzelProblem6Kernel.PeripheralIncidenceNodup

/-! # Duplicate-free literal placement boundaries -/

namespace BenzelProblem6Kernel

theorem literalPrototypeBoundary_nodup
    (tile : ProtoTile) (base : Cell) :
    (literalPrototypeBoundary tile base).Nodup := by
  have hcanonical :
      (literalPrototypeBoundary tile (0, 0)).Nodup := by
    cases tile <;> decide
  have hbase : base = translateCell base (0, 0) := by
    rcases base with ⟨i, j⟩
    simp [translateCell]
  rw [hbase, literalPrototypeBoundary_translate]
  exact hcanonical.map
    (translateLabeledHexEdge_injective (hexVertexTranslation base))

theorem literalPlacementBoundary_nodup {m : ℕ}
    (placement : LiteralPlacement m) :
    (literalPlacementBoundary placement).Nodup :=
  literalPrototypeBoundary_nodup placement.tile placement.base

theorem reverseReorientedEdges_nodup
    {edges : List LabeledHexEdge} (hnodup : edges.Nodup) :
    (reverseReorientedEdges edges).Nodup := by
  rw [reverseReorientedEdges]
  exact (List.nodup_reverse.mpr hnodup).map
    reverseLabeledHexEdge_injective

theorem reverseLiteralPlacementBoundary_nodup {m : ℕ}
    (placement : LiteralPlacement m) :
    (reverseReorientedEdges
      (literalPlacementBoundary placement)).Nodup :=
  reverseReorientedEdges_nodup (literalPlacementBoundary_nodup placement)

end BenzelProblem6Kernel

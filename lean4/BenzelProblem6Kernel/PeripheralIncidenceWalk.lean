import BenzelProblem6Kernel.HoneycombEdgePathParity

/-! # Clockwise walks carried by peripheral cell-side incidences -/

namespace BenzelProblem6Kernel

def clockwiseCellSideEdge (datum : CellSide) : LabeledHexEdge :=
  reverseLabeledHexEdge (cellSideBoundaryEdge datum)

def clockwiseIncidenceEdges (incidences : List CellSide) :
    List LabeledHexEdge :=
  incidences.map clockwiseCellSideEdge

theorem clockwiseIncidenceEdges_append
    (left right : List CellSide) :
    clockwiseIncidenceEdges (left ++ right) =
      clockwiseIncidenceEdges left ++ clockwiseIncidenceEdges right := by
  simp [clockwiseIncidenceEdges]

theorem clockwiseCellSideEdge_alternates (datum : CellSide) :
    AlternatesHexVertexClass (clockwiseCellSideEdge datum) := by
  apply reverseLabeledHexEdge_alternates
  exact cellBoundaryEdgeAt_alternates datum.1 datum.2

theorem clockwiseIncidenceEdges_alternate
    (incidences : List CellSide) :
    ∀ edge ∈ clockwiseIncidenceEdges incidences,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  obtain ⟨datum, hdatum, rfl⟩ := List.mem_map.mp hedge
  exact clockwiseCellSideEdge_alternates datum

end BenzelProblem6Kernel

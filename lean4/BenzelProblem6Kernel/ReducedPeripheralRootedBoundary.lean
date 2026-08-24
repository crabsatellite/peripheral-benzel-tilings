import BenzelProblem6Kernel.PeripheralFixedWalks
import BenzelProblem6Kernel.RootedAlternatingBoundary

/-! # The explicit reduced peripheral edge list is a rooted closed walk -/

namespace BenzelProblem6Kernel

theorem peripheralIncidences_clockwise_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 5, -((m : ℤ)) - 2)
      (clockwiseIncidenceEdges (literalPeripheralIncidences m))
      ((m : ℤ) + 5, -((m : ℤ)) - 2) := by
  rw [literalPeripheralIncidences,
    clockwiseIncidenceEdges_append,
    clockwiseIncidenceEdges_append,
    clockwiseIncidenceEdges_append,
    clockwiseIncidenceEdges_append,
    clockwiseIncidenceEdges_append]
  exact (((((peripheralFixed₀_continuous m).append
    (peripheralLong₁_continuous m)).append
    (peripheralFixed₂_continuous m)).append
    (peripheralLong₃_continuous m)).append
    (peripheralFixed₄_continuous m)).append
    (peripheralLong₅_continuous m)

theorem reverse_clockwiseIncidenceEdges
    (incidences : List CellSide) :
    (clockwiseIncidenceEdges incidences).reverse.map
        reverseLabeledHexEdge =
      incidences.reverse.map cellSideBoundaryEdge := by
  rw [clockwiseIncidenceEdges, List.map_reverse, List.map_map]
  rw [← List.map_reverse]
  apply List.map_congr_left
  intro datum hdatum
  simp [clockwiseCellSideEdge, reverseLabeledHexEdge_involutive]

theorem literalReducedPeripheralBoundary_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 5, -((m : ℤ)) - 2)
      (literalReducedPeripheralBoundary m)
      ((m : ℤ) + 5, -((m : ℤ)) - 2) := by
  have hreverse := (peripheralIncidences_clockwise_continuous m).reverse
  rw [reverse_clockwiseIncidenceEdges] at hreverse
  exact hreverse

theorem literalReducedPeripheralBoundary_edges_alternate (m : ℕ) :
    ∀ edge ∈ literalReducedPeripheralBoundary m,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp only [literalReducedPeripheralBoundary, List.mem_map,
    List.mem_reverse] at hedge
  obtain ⟨datum, hdatum, rfl⟩ := hedge
  exact cellBoundaryEdgeAt_alternates datum.1 datum.2

def literalReducedPeripheralRootedBoundary (m : ℕ) :
    RootedAlternatingBoundary where
  edges := literalReducedPeripheralBoundary m
  root := ((m : ℤ) + 5, -((m : ℤ)) - 2)
  continuous := literalReducedPeripheralBoundary_continuous m
  root_classZero := by
    simp [hexVertexClassZero]
    omega
  alternates := literalReducedPeripheralBoundary_edges_alternate m

end BenzelProblem6Kernel

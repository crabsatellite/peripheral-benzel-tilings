import BenzelProblem6Kernel.PeripheralLong1Walk
import BenzelProblem6Kernel.PeripheralLong3Walk
import BenzelProblem6Kernel.PeripheralLong5Walk

/-! # The three fixed clockwise corner stretches of the peripheral boundary -/

namespace BenzelProblem6Kernel

theorem peripheralFixed₀_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 5, -((m : ℤ)) - 2)
      (clockwiseIncidenceEdges (peripheralFixed₀ m))
      ((m : ℤ) + 2, -((m : ℤ)) - 4) := by
  convert walkLabeledHexEdges_continuous
      ((m : ℤ) + 5, -((m : ℤ)) - 2)
      [(shadowC, .c), (shadowA.neg, .a), (shadowC, .c)] using 1 <;>
    simp [peripheralFixed₀, clockwiseIncidenceEdges,
      clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
      reverseLabeledHexEdge, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp

theorem peripheralFixed₂_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      (-2 * (m : ℤ) - 7, -((m : ℤ)) - 5)
      (clockwiseIncidenceEdges (peripheralFixed₂ m))
      (-2 * (m : ℤ) - 6, -((m : ℤ)) - 2) := by
  convert walkLabeledHexEdges_continuous
      (-2 * (m : ℤ) - 7, -((m : ℤ)) - 5)
      [(shadowB, .b), (shadowC.neg, .c), (shadowB, .b)] using 1 <;>
    simp [peripheralFixed₂, clockwiseIncidenceEdges,
      clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
      reverseLabeledHexEdge, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp

theorem peripheralFixed₄_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 2, 2 * (m : ℤ) + 7)
      (clockwiseIncidenceEdges (peripheralFixed₄ m))
      ((m : ℤ) + 4, 2 * (m : ℤ) + 6) := by
  convert walkLabeledHexEdges_continuous
      ((m : ℤ) + 2, 2 * (m : ℤ) + 7)
      [(shadowA, .a), (shadowB.neg, .b), (shadowA, .a)] using 1 <;>
    simp [peripheralFixed₄, clockwiseIncidenceEdges,
      clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
      reverseLabeledHexEdge, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp

end BenzelProblem6Kernel

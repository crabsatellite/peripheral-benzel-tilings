import BenzelProblem6Kernel.HexCellEdgeIncidenceSide0
import BenzelProblem6Kernel.HexCellEdgeIncidenceSide1
import BenzelProblem6Kernel.HexCellEdgeIncidenceSide2
import BenzelProblem6Kernel.HexCellEdgeIncidenceSide3
import BenzelProblem6Kernel.HexCellEdgeIncidenceSide4
import BenzelProblem6Kernel.HexCellEdgeIncidenceSide5

/-! # Complete unique-incidence theorem for labeled honeycomb edges -/

namespace BenzelProblem6Kernel

theorem cellBoundaryEdgeAt_key_eq_iff
    (leftCell rightCell : Cell) (leftSide rightSide : HexSide) :
    (cellBoundaryEdgeAt leftCell leftSide).key =
        (cellBoundaryEdgeAt rightCell rightSide).key ↔
      (rightCell = leftCell ∧ rightSide = leftSide) ∨
        (rightCell = neighboringCell leftCell leftSide ∧
          rightSide = oppositeHexSide leftSide) := by
  cases leftSide
  · exact cellBoundaryEdgeAt_side₀_key_eq_iff leftCell rightCell rightSide
  · exact cellBoundaryEdgeAt_side₁_key_eq_iff leftCell rightCell rightSide
  · exact cellBoundaryEdgeAt_side₂_key_eq_iff leftCell rightCell rightSide
  · exact cellBoundaryEdgeAt_side₃_key_eq_iff leftCell rightCell rightSide
  · exact cellBoundaryEdgeAt_side₄_key_eq_iff leftCell rightCell rightSide
  · exact cellBoundaryEdgeAt_side₅_key_eq_iff leftCell rightCell rightSide

end BenzelProblem6Kernel

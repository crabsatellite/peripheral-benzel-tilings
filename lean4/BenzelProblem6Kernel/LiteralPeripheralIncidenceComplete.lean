import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide0
import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide1
import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide2
import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide3
import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide4
import BenzelProblem6Kernel.LiteralPeripheralIncidenceSide5

/-! # Complete arithmetic classification of peripheral cell-sides -/

namespace BenzelProblem6Kernel

theorem isInsidePeripheralEdge_iff_mem
    (m : ℕ) (cell : Cell) (side : HexSide) :
    IsInsidePeripheralEdge m cell side ↔
      (cell, side) ∈ literalPeripheralIncidences m := by
  cases side
  · exact isInsidePeripheralEdge_side₀_iff_mem m cell
  · exact isInsidePeripheralEdge_side₁_iff_mem m cell
  · exact isInsidePeripheralEdge_side₂_iff_mem m cell
  · exact isInsidePeripheralEdge_side₃_iff_mem m cell
  · exact isInsidePeripheralEdge_side₄_iff_mem m cell
  · exact isInsidePeripheralEdge_side₅_iff_mem m cell

end BenzelProblem6Kernel

import BenzelProblem6Kernel.ExposedPlacementEdgeStone

/-! # Every exposed side of a literal stone is on its boundary -/

namespace BenzelProblem6Kernel

theorem cellSide_mem_stoneBoundary_iff
    (base cell : Cell) (side : HexSide)
    (hcell : cell ∈
      (protoCells .stone).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell side ∈
        literalPrototypeBoundary .stone base ↔
      neighboringCell cell side ∉
        (protoCells .stone).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c01] at hcell
  rcases hcell with hcell | hcell | hcell <;>
    rcases hcell with ⟨rfl, rfl⟩
  all_goals cases side
  all_goals
    simp [protoCells, translateLocalCell, c00, c10, c01,
      neighboringCell, literalPrototypeBoundary,
      prototypeBoundaryStart, prototypeBoundarySteps,
      walkLabeledHexEdges, cellBoundaryEdgeAt,
      advanceLabeledHexEdge, addHexStep, hexCellStartVertex,
      hexCellCenter, ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

end BenzelProblem6Kernel

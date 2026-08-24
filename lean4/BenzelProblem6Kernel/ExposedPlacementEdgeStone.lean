import BenzelProblem6Kernel.ExposedPlacementEdge

namespace BenzelProblem6Kernel

theorem exposed_side₅_mem_stoneBoundary
    (base cell : Cell)
    (hcell : cell ∈
      (protoCells .stone).map (translateLocalCell base))
    (hexposed : neighboringCell cell .side₅ ∉
      (protoCells .stone).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈
      literalPrototypeBoundary .stone base := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c01] at hcell hexposed
  rcases hcell with hcell | hcell | hcell <;>
    rcases hcell with ⟨rfl, rfl⟩
  all_goals
    simp [neighboringCell, literalPrototypeBoundary,
      prototypeBoundaryStart, prototypeBoundarySteps,
      walkLabeledHexEdges, cellBoundaryEdgeAt,
      advanceLabeledHexEdge, addHexStep, hexCellStartVertex,
      hexCellCenter, ShadowStep.neg, shadowA, shadowB, shadowC] at hexposed ⊢
  all_goals omega

end BenzelProblem6Kernel

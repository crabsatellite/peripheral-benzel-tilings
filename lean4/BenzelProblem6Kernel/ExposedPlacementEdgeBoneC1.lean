import BenzelProblem6Kernel.ExposedPlacementEdge

namespace BenzelProblem6Kernel

theorem exposed_side₅_mem_boneC_c1m1 (base : Cell) :
    cellBoundaryEdgeAt (translateLocalCell base c1m1) .side₅ ∈
      literalPrototypeBoundary .boneC base := by
  rcases base with ⟨baseI, baseJ⟩
  simp [translateLocalCell, c1m1, cellBoundaryEdgeAt,
    literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex,
    hexCellCenter, ShadowStep.neg, shadowA, shadowB, shadowC]
  omega

end BenzelProblem6Kernel

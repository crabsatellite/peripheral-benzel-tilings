import BenzelProblem6Kernel.ExposedPlacementEdgeBoneC

/-! # Every exposed side of a literal diagonal bone is on its boundary -/

namespace BenzelProblem6Kernel

theorem cellSide₀_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₀ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₀ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₁_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₁ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₁ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₂_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₂ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₂ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₃_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₃ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₃ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₄_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₄ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₄ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₅_mem_boneCBoundary_neighbor_not
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base))
    (hboundary : cellBoundaryEdgeAt cell .side₅ ∈
      literalPrototypeBoundary .boneC base) :
    neighboringCell cell .side₅ ∉
      (protoCells .boneC).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c1m1, c2m2] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c1m1, c2m2,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC] at hboundary ⊢

theorem cellSide₅_mem_boneCBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell .side₅ ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  constructor
  · exact cellSide₅_mem_boneCBoundary_neighbor_not base cell hcell
  · exact exposed_side₅_mem_boneCBoundary base cell hcell

theorem cellSide_mem_boneCBoundary_iff
    (base cell : Cell) (side : HexSide)
    (hcell : cell ∈ (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell side ∈ literalPrototypeBoundary .boneC base ↔
      neighboringCell cell side ∉
        (protoCells .boneC).map (translateLocalCell base) := by
  cases side
  · exact cellSide₀_mem_boneCBoundary_iff base cell hcell
  · exact cellSide₁_mem_boneCBoundary_iff base cell hcell
  · exact cellSide₂_mem_boneCBoundary_iff base cell hcell
  · exact cellSide₃_mem_boneCBoundary_iff base cell hcell
  · exact cellSide₄_mem_boneCBoundary_iff base cell hcell
  · exact cellSide₅_mem_boneCBoundary_iff base cell hcell

end BenzelProblem6Kernel

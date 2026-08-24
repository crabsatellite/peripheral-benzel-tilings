import BenzelProblem6Kernel.ExposedPlacementEdgeBoneB

/-! # Every exposed side of a literal vertical bone is on its boundary -/

namespace BenzelProblem6Kernel

theorem cellSide₀_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₀ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₀ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₁_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₁ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₁ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₂_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₂ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₂ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₃_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₃ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₃ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₄_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₄ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₄ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₅_mem_boneBBoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell .side₅ ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c01, c02] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c01, c02,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide_mem_boneBBoundary_iff
    (base cell : Cell) (side : HexSide)
    (hcell : cell ∈ (protoCells .boneB).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell side ∈ literalPrototypeBoundary .boneB base ↔
      neighboringCell cell side ∉
        (protoCells .boneB).map (translateLocalCell base) := by
  cases side
  · exact cellSide₀_mem_boneBBoundary_iff base cell hcell
  · exact cellSide₁_mem_boneBBoundary_iff base cell hcell
  · exact cellSide₂_mem_boneBBoundary_iff base cell hcell
  · exact cellSide₃_mem_boneBBoundary_iff base cell hcell
  · exact cellSide₄_mem_boneBBoundary_iff base cell hcell
  · exact cellSide₅_mem_boneBBoundary_iff base cell hcell

end BenzelProblem6Kernel

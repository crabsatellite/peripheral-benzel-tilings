import BenzelProblem6Kernel.ExposedPlacementEdgeBoneA

/-! # Every exposed side of a literal horizontal bone is on its boundary -/

namespace BenzelProblem6Kernel

theorem cellSide₀_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₀ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₀ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₁_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₁ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₁ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₂_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₂ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₂ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₃_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₃ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₃ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₄_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₄ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₄ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide₅_mem_boneABoundary_iff
    (base cell : Cell)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell .side₅ ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  rcases base with ⟨baseI, baseJ⟩
  rcases cell with ⟨cellI, cellJ⟩
  simp [protoCells, translateLocalCell, c00, c10, c20] at hcell
  rcases hcell with hcell | hcell | hcell <;> rcases hcell with ⟨rfl, rfl⟩
  all_goals simp [protoCells, translateLocalCell, c00, c10, c20,
    neighboringCell, literalPrototypeBoundary, prototypeBoundaryStart,
    prototypeBoundarySteps, walkLabeledHexEdges, cellBoundaryEdgeAt,
    advanceLabeledHexEdge, addHexStep, hexCellStartVertex, hexCellCenter,
    ShadowStep.neg, shadowA, shadowB, shadowC]
  all_goals omega

theorem cellSide_mem_boneABoundary_iff
    (base cell : Cell) (side : HexSide)
    (hcell : cell ∈ (protoCells .boneA).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell side ∈ literalPrototypeBoundary .boneA base ↔
      neighboringCell cell side ∉
        (protoCells .boneA).map (translateLocalCell base) := by
  cases side
  · exact cellSide₀_mem_boneABoundary_iff base cell hcell
  · exact cellSide₁_mem_boneABoundary_iff base cell hcell
  · exact cellSide₂_mem_boneABoundary_iff base cell hcell
  · exact cellSide₃_mem_boneABoundary_iff base cell hcell
  · exact cellSide₄_mem_boneABoundary_iff base cell hcell
  · exact cellSide₅_mem_boneABoundary_iff base cell hcell

end BenzelProblem6Kernel

import BenzelProblem6Kernel.SelectedSpliceEndpointSupport

/-! # A directed honeycomb edge is determined by its two endpoints -/

namespace BenzelProblem6Kernel

theorem side₀_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₀).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₀).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₀ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem side₁_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₁).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₁).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₁ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem side₂_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₂).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₂).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₂ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem side₃_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₃).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₃).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₃ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem side₄_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₄).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₄).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₄ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem side₅_endpoint_injective (left right : Cell)
    (rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left .side₅).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left .side₅).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left .side₅ =
      cellBoundaryEdgeAt right rightSide := by
  rcases left with ⟨li, lj⟩
  rcases right with ⟨ri, rj⟩
  cases rightSide
  all_goals apply labeledHexEdge_ext
  all_goals try exact hsource
  all_goals try exact htarget
  all_goals simp [cellBoundaryEdgeAt, advanceLabeledHexEdge, addHexStep,
    hexCellStartVertex, hexCellCenter, ShadowStep.neg,
    shadowA, shadowB, shadowC] at hsource htarget ⊢ <;> omega

theorem cellBoundaryEdgeAt_endpoint_injective
    (left right : Cell) (leftSide rightSide : HexSide)
    (hsource : (cellBoundaryEdgeAt left leftSide).source =
      (cellBoundaryEdgeAt right rightSide).source)
    (htarget : (cellBoundaryEdgeAt left leftSide).target =
      (cellBoundaryEdgeAt right rightSide).target) :
    cellBoundaryEdgeAt left leftSide =
      cellBoundaryEdgeAt right rightSide := by
  cases leftSide
  · exact side₀_endpoint_injective left right rightSide hsource htarget
  · exact side₁_endpoint_injective left right rightSide hsource htarget
  · exact side₂_endpoint_injective left right rightSide hsource htarget
  · exact side₃_endpoint_injective left right rightSide hsource htarget
  · exact side₄_endpoint_injective left right rightSide hsource htarget
  · exact side₅_endpoint_injective left right rightSide hsource htarget

end BenzelProblem6Kernel

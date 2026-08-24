import BenzelProblem6Kernel.HexCellEdgeIncidence

namespace BenzelProblem6Kernel

theorem cellBoundaryEdgeAt_side₁_key_eq_iff
    (leftCell rightCell : Cell) (rightSide : HexSide) :
    (cellBoundaryEdgeAt leftCell .side₁).key =
        (cellBoundaryEdgeAt rightCell rightSide).key ↔
      (rightCell = leftCell ∧ rightSide = .side₁) ∨
        (rightCell = neighboringCell leftCell .side₁ ∧
          rightSide = oppositeHexSide .side₁) := by
  rcases leftCell with ⟨leftI, leftJ⟩
  rcases rightCell with ⟨rightI, rightJ⟩
  cases rightSide <;>
    simp [cellBoundaryEdgeAt, neighboringCell, oppositeHexSide,
      LabeledHexEdge.key, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, Sym2.eq_iff, Prod.ext_iff] <;> omega

end BenzelProblem6Kernel

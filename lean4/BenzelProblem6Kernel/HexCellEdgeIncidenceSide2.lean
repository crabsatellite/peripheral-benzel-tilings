import BenzelProblem6Kernel.HexCellEdgeIncidence

namespace BenzelProblem6Kernel

theorem cellBoundaryEdgeAt_side₂_key_eq_iff
    (leftCell rightCell : Cell) (rightSide : HexSide) :
    (cellBoundaryEdgeAt leftCell .side₂).key =
        (cellBoundaryEdgeAt rightCell rightSide).key ↔
      (rightCell = leftCell ∧ rightSide = .side₂) ∨
        (rightCell = neighboringCell leftCell .side₂ ∧
          rightSide = oppositeHexSide .side₂) := by
  rcases leftCell with ⟨leftI, leftJ⟩
  rcases rightCell with ⟨rightI, rightJ⟩
  cases rightSide <;>
    simp [cellBoundaryEdgeAt, neighboringCell, oppositeHexSide,
      LabeledHexEdge.key, advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, Sym2.eq_iff, Prod.ext_iff] <;> omega

end BenzelProblem6Kernel

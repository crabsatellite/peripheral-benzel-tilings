import BenzelProblem6Kernel.TilingComplexVerticesLocal

/-! # Cellwise realization of the finite benzel vertex carrier -/

namespace BenzelProblem6Kernel

def cellVertexFinset (cell : Cell) : Finset HexVertex :=
  edgeSourceFinset (labeledCellBoundary cell)

theorem mem_cellVertexFinset_iff (cell : Cell) (vertex : HexVertex) :
    vertex ∈ cellVertexFinset cell ↔
      (∃ (anchor : Cell) (label : MicroLabel),
        cellForOwnerAnchor anchor label = cell ∧
          upHexVertex anchor = vertex) ∨
      (∃ (anchor : Cell) (label : MicroLabel),
        downAnchorCell anchor label = cell ∧
          downHexVertex anchor = vertex) := by
  rcases cell with ⟨i, j⟩
  rcases vertex with ⟨x, y⟩
  simp only [cellVertexFinset, edgeSourceFinset,
    labeledCellBoundary, walkLabeledHexEdges,
    cellBoundarySteps, List.map_cons, List.map_nil,
    List.mem_toFinset, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h | h | h)
    · left
      exact ⟨(i, j), .zero, rfl, by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [upHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge, shadowA] at hx hy ⊢
        omega⟩
    · right
      exact ⟨(i, j), .zero, rfl, by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [downHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge, shadowA, shadowB] at hx hy ⊢
        omega⟩
    · left
      exact ⟨(i - 1, j), .one, by
        simp [cellForOwnerAnchor], by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [upHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge,
          ShadowStep.neg, shadowA, shadowB] at hx hy ⊢
        omega⟩
    · right
      exact ⟨(i, j - 1), .one, by
        simp [downAnchorCell], by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [downHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge,
          ShadowStep.neg, shadowA, shadowB, shadowC] at hx hy ⊢
        omega⟩
    · left
      exact ⟨(i, j - 1), .two, by
        simp [cellForOwnerAnchor], by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [upHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge,
          ShadowStep.neg, shadowA, shadowB, shadowC] at hx hy ⊢
        omega⟩
    · right
      exact ⟨(i + 1, j - 1), .two, by
        simp [downAnchorCell], by
        have hx := congrArg Prod.fst h
        have hy := congrArg Prod.snd h
        simp [downHexVertex, hexCellStartVertex, hexCellCenter,
          addHexStep, advanceLabeledHexEdge,
          ShadowStep.neg, shadowA, shadowB, shadowC] at hx hy ⊢
        omega⟩
  · rintro (⟨anchor, label, hcell, hvertex⟩ |
      ⟨anchor, label, hcell, hvertex⟩)
    · rcases anchor with ⟨q, r⟩
      cases label <;> simp [cellForOwnerAnchor] at hcell
      all_goals simp [upHexVertex, hexCellStartVertex, hexCellCenter,
        addHexStep, advanceLabeledHexEdge,
        ShadowStep.neg, shadowA, shadowB, shadowC] at hvertex hcell ⊢
      all_goals omega
    · rcases anchor with ⟨q, r⟩
      cases label <;> simp [downAnchorCell] at hcell
      all_goals simp [downHexVertex, hexCellStartVertex, hexCellCenter,
        addHexStep, advanceLabeledHexEdge,
        ShadowStep.neg, shadowA, shadowB, shadowC] at hvertex hcell ⊢
      all_goals omega

end BenzelProblem6Kernel

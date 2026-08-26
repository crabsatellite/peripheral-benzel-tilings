import D4KernelOnly.D4BoundarySideFiveCoefficient

/-! # Alternation of the literal physical d=4 boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

private theorem d4Block5_edges_alternate (m r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (d4Stage0 m) (-3, -3) r)
        d4LiteralStepBlock5,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock5, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, d4Stage0, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Block4_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock4, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      d4Stage2, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Block3_edges_alternate (m r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (d4Stage4 m) (3, 0) r)
        d4LiteralStepBlock3,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock3, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, d4Stage4, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Block2_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock2, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      d4Stage6, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Block1_edges_alternate (m r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (d4Stage8 m) (0, 3) r)
        d4LiteralStepBlock1,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock1, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, d4Stage8, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Block0_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock0, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      d4Stage10, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem d4Single1_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage1 m) [(shadowC, .c)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage1, advanceLabeledHexEdge, addHexStep, shadowC]
  omega

private theorem d4Single3_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage3 m) [(shadowC.neg, .c)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage3, advanceLabeledHexEdge, addHexStep, shadowC,
    ShadowStep.neg]
  omega

private theorem d4Single5_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage5 m) [(shadowA, .a)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage5, advanceLabeledHexEdge, addHexStep, shadowA]
  omega

private theorem d4Single7_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage7 m) [(shadowA.neg, .a)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage7, advanceLabeledHexEdge, addHexStep, shadowA,
    ShadowStep.neg]
  omega

private theorem d4Single9_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage9 m) [(shadowB, .b)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage9, advanceLabeledHexEdge, addHexStep, shadowB]
  omega

private theorem d4Single11_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage11 m) [(shadowB.neg, .b)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    d4Stage11, advanceLabeledHexEdge, addHexStep, shadowB,
    ShadowStep.neg]
  omega

private theorem d4Block5_power_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage0 m)
        (labeledStepWordPower d4LiteralStepBlock5 (m + 1)),
      AlternatesHexVertexClass edge := by
  rw [walkLabeledHexEdges_power d4LiteralStepBlock5 (-3, -3)
    (d4Stage0 m) (fun source => by
      simpa using d4LiteralBlock5_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨r, hr, hedge⟩ := hedge
  exact d4Block5_edges_alternate m r edge hedge

private theorem d4Block3_power_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage4 m)
        (labeledStepWordPower d4LiteralStepBlock3 (m + 1)),
      AlternatesHexVertexClass edge := by
  rw [walkLabeledHexEdges_power d4LiteralStepBlock3 (3, 0)
    (d4Stage4 m) (fun source => by
      simpa using d4LiteralBlock3_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨r, hr, hedge⟩ := hedge
  exact d4Block3_edges_alternate m r edge hedge

private theorem d4Block1_power_edges_alternate (m : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (d4Stage8 m)
        (labeledStepWordPower d4LiteralStepBlock1 (m + 1)),
      AlternatesHexVertexClass edge := by
  rw [walkLabeledHexEdges_power d4LiteralStepBlock1 (0, 3)
    (d4Stage8 m) (fun source => by
      simpa using d4LiteralBlock1_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨r, hr, hedge⟩ := hedge
  exact d4Block1_edges_alternate m r edge hedge

theorem d4LiteralBoundaryWalk_edges_alternate (m : ℕ) :
    ∀ edge ∈ d4LiteralBoundaryWalk m,
      AlternatesHexVertexClass edge := by
  rw [d4LiteralBoundaryWalk_eq_segments]
  unfold d4LiteralBoundaryWalkBySegments
  intro edge hedge
  simp only [List.mem_append] at hedge
  rcases hedge with hedge | hedge | hedge | hedge | hedge | hedge |
      hedge | hedge | hedge | hedge | hedge | hedge
  · exact d4Block5_power_edges_alternate m edge hedge
  · exact d4Single1_edges_alternate m edge hedge
  · exact d4Block4_edges_alternate m edge hedge
  · exact d4Single3_edges_alternate m edge hedge
  · exact d4Block3_power_edges_alternate m edge hedge
  · exact d4Single5_edges_alternate m edge hedge
  · exact d4Block2_edges_alternate m edge hedge
  · exact d4Single7_edges_alternate m edge hedge
  · exact d4Block1_power_edges_alternate m edge hedge
  · exact d4Single9_edges_alternate m edge hedge
  · exact d4Block0_edges_alternate m edge hedge
  · exact d4Single11_edges_alternate m edge hedge

end FiniteDefects

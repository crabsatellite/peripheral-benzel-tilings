import D4KernelOnly.GeneralClassMinusOneAllCoefficients

/-! # Alternation of the general class-minus-one physical boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

theorem hexVertexClassZero_rotate (vertex : HexVertex) :
    hexVertexClassZero (d4RotateVertex vertex) =
      hexVertexClassZero vertex := by
  rcases vertex with ⟨x, y⟩
  simp [hexVertexClassZero, d4RotateVertex]
  omega

theorem alternates_d4RotateEdge_iff (edge : LabeledHexEdge) :
    AlternatesHexVertexClass (d4RotateEdge edge) ↔
      AlternatesHexVertexClass edge := by
  simp only [AlternatesHexVertexClass, d4RotateEdge,
    hexVertexClassZero_rotate]

private theorem cmoBlock5_edges_alternate (s r q : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (cmoStage0 s r) (-3, -3) q)
        d4LiteralStepBlock5,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock5, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, cmoStage0, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem cmoBlock4_edges_alternate (s r q : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (cmoStage2 s r) (0, -3) q)
        d4LiteralStepBlock4,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [d4LiteralStepBlock4, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, cmoStage2, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem cmoSingle1_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (cmoStage1 s r) [(shadowC, .c)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    cmoStage1, advanceLabeledHexEdge, addHexStep, shadowC]
  omega

private theorem cmoSingle3_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (cmoStage3 s r) [(shadowC.neg, .c)],
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [walkLabeledHexEdges] at hedge
  subst edge
  simp [AlternatesHexVertexClass, hexVertexClassZero,
    cmoStage3, advanceLabeledHexEdge, addHexStep, shadowC,
    ShadowStep.neg]
  omega

private theorem cmoBlock5_power_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (cmoStage0 s r)
        (labeledStepWordPower d4LiteralStepBlock5 r),
      AlternatesHexVertexClass edge := by
  rw [walkLabeledHexEdges_power d4LiteralStepBlock5 (-3, -3)
    (cmoStage0 s r) (fun source => by
      simpa using d4LiteralBlock5_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨q, hq, hedge⟩ := hedge
  exact cmoBlock5_edges_alternate s r q edge hedge

private theorem cmoBlock4_power_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (cmoStage2 s r)
        (labeledStepWordPower d4LiteralStepBlock4 s),
      AlternatesHexVertexClass edge := by
  rw [walkLabeledHexEdges_power d4LiteralStepBlock4 (0, -3)
    (cmoStage2 s r) (fun source => by
      simpa using d4LiteralBlock4_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨q, hq, hedge⟩ := hedge
  exact cmoBlock4_edges_alternate s r q edge hedge

theorem cmoBoundaryChunk0_edges_alternate (s r : ℕ) :
    ∀ edge ∈ cmoBoundaryChunk0 s r,
      AlternatesHexVertexClass edge := by
  unfold cmoBoundaryChunk0
  intro edge hedge
  simp only [List.mem_append] at hedge
  rcases hedge with ((hedge | hedge) | hedge) | hedge
  · exact cmoBlock5_power_edges_alternate s r edge hedge
  · exact cmoSingle1_edges_alternate s r edge hedge
  · exact cmoBlock4_power_edges_alternate s r edge hedge
  · exact cmoSingle3_edges_alternate s r edge hedge

theorem cmoBoundaryChunk1_edges_alternate (s r : ℕ) :
    ∀ edge ∈ cmoBoundaryChunk1 s r,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  have hrot : d4RotateEdge edge ∈ cmoBoundaryChunk0 s r := by
    rw [← cmoRotateChunk1 s r]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (alternates_d4RotateEdge_iff edge).mp
    (cmoBoundaryChunk0_edges_alternate s r _ hrot)

theorem cmoBoundaryChunk2_edges_alternate (s r : ℕ) :
    ∀ edge ∈ cmoBoundaryChunk2 s r,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  have hrot : d4RotateEdge edge ∈ cmoBoundaryChunk1 s r := by
    rw [← cmoRotateChunk2 s r]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (alternates_d4RotateEdge_iff edge).mp
    (cmoBoundaryChunk1_edges_alternate s r _ hrot)

theorem classMinusOneLiteralBoundaryWalk_edges_alternate (s r : ℕ) :
    ∀ edge ∈ classMinusOneLiteralBoundaryWalk s r,
      AlternatesHexVertexClass edge := by
  rw [classMinusOneBoundaryWalk_eq_chunks]
  intro edge hedge
  simp only [List.mem_append] at hedge
  rcases hedge with (hedge | hedge) | hedge
  · exact cmoBoundaryChunk0_edges_alternate s r edge hedge
  · exact cmoBoundaryChunk1_edges_alternate s r edge hedge
  · exact cmoBoundaryChunk2_edges_alternate s r edge hedge

theorem classMinusOneLiteralBoundaryRoot_classZero (s r : ℕ) :
    hexVertexClassZero (classMinusOneLiteralBoundaryRoot s r) = true := by
  simp [classMinusOneLiteralBoundaryRoot, hexVertexClassZero]
  omega

def classMinusOneLiteralRootedBoundary (s r : ℕ) :
    RootedAlternatingBoundary where
  edges := classMinusOneLiteralBoundaryWalk s r
  root := classMinusOneLiteralBoundaryRoot s r
  continuous := classMinusOneLiteralBoundary_continuous s r
  root_classZero := classMinusOneLiteralBoundaryRoot_classZero s r
  alternates := classMinusOneLiteralBoundaryWalk_edges_alternate s r

end FiniteDefects

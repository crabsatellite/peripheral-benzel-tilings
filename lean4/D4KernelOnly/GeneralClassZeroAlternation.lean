import D4KernelOnly.GeneralClassZeroNodup
import D4KernelOnly.GeneralClassMinusOneAlternation

/-! # Alternation of the general class-zero physical boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

private theorem czBlock5_edges_alternate (s r q : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (czStage0 s r) (0, 3) q) czLiteralBlock5,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [czLiteralBlock5, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₅, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, czStage0, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem czBlock4_edges_alternate (s r q : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges
        (walkPowerStart (czStage1 s r) (-3, 0) q) czLiteralBlock4,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  simp [czLiteralBlock4, reverseClassZeroWord, reverseClassZeroStep,
    literalPeripheralBlock₄, walkLabeledHexEdges] at hedge
  rcases hedge with rfl | rfl | rfl | rfl
  all_goals
    simp [AlternatesHexVertexClass, hexVertexClassZero,
      walkPowerStart, czStage1, advanceLabeledHexEdge, addHexStep,
      shadowA, shadowB, shadowC, ShadowStep.neg]
  all_goals omega

private theorem czBlock5_power_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (czStage0 s r)
        (labeledHexStepWordPower czLiteralBlock5 r),
      AlternatesHexVertexClass edge := by
  rw [labeledHexStepWordPower_eq_labeledStepWordPower,
    walkLabeledHexEdges_power czLiteralBlock5 (0, 3)
      (czStage0 s r) (fun source => by
        simpa using czLiteralBlock5_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨q, hq, hedge⟩ := hedge
  exact czBlock5_edges_alternate s r q edge hedge

private theorem czBlock4_power_edges_alternate (s r : ℕ) :
    ∀ edge ∈ walkLabeledHexEdges (czStage1 s r)
        (labeledHexStepWordPower czLiteralBlock4 s),
      AlternatesHexVertexClass edge := by
  rw [labeledHexStepWordPower_eq_labeledStepWordPower,
    walkLabeledHexEdges_power czLiteralBlock4 (-3, 0)
      (czStage1 s r) (fun source => by
        simpa using czLiteralBlock4_walkEnd source)]
  intro edge hedge
  rw [List.mem_flatMap] at hedge
  obtain ⟨q, hq, hedge⟩ := hedge
  exact czBlock4_edges_alternate s r q edge hedge

theorem czBoundaryChunk0_edges_alternate (s r : ℕ) :
    ∀ edge ∈ czBoundaryChunk0 s r, AlternatesHexVertexClass edge := by
  unfold czBoundaryChunk0
  intro edge hedge
  rw [List.mem_append] at hedge
  rcases hedge with hedge | hedge
  · exact czBlock5_power_edges_alternate s r edge hedge
  · exact czBlock4_power_edges_alternate s r edge hedge

theorem czBoundaryChunk1_edges_alternate (s r : ℕ) :
    ∀ edge ∈ czBoundaryChunk1 s r, AlternatesHexVertexClass edge := by
  intro edge hedge
  have hrot : d4RotateEdge edge ∈ czBoundaryChunk0 s r := by
    rw [← czRotateChunk1 s r]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (alternates_d4RotateEdge_iff edge).mp
    (czBoundaryChunk0_edges_alternate s r _ hrot)

theorem czBoundaryChunk2_edges_alternate (s r : ℕ) :
    ∀ edge ∈ czBoundaryChunk2 s r, AlternatesHexVertexClass edge := by
  intro edge hedge
  have hrot : d4RotateEdge edge ∈ czBoundaryChunk1 s r := by
    rw [← czRotateChunk2 s r]
    exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
  exact (alternates_d4RotateEdge_iff edge).mp
    (czBoundaryChunk1_edges_alternate s r _ hrot)

theorem classZeroLiteralBoundaryWalk_edges_alternate (s r : ℕ) :
    ∀ edge ∈ classZeroLiteralBoundaryWalk s r,
      AlternatesHexVertexClass edge := by
  rw [classZeroBoundaryWalk_eq_chunks]
  intro edge hedge
  simp only [List.mem_append] at hedge
  rcases hedge with (hedge | hedge) | hedge
  · exact czBoundaryChunk0_edges_alternate s r edge hedge
  · exact czBoundaryChunk1_edges_alternate s r edge hedge
  · exact czBoundaryChunk2_edges_alternate s r edge hedge

theorem classZeroLiteralBoundaryRoot_classZero (s r : ℕ) :
    hexVertexClassZero (classZeroClockwiseRoot s r) = true := by
  simp [classZeroClockwiseRoot, hexVertexClassZero]
  omega

def classZeroLiteralRootedBoundary (s r : ℕ) : RootedAlternatingBoundary where
  edges := classZeroLiteralBoundaryWalk s r
  root := classZeroClockwiseRoot s r
  continuous := classZeroLiteralBoundary_continuous s r
  root_classZero := classZeroLiteralBoundaryRoot_classZero s r
  alternates := classZeroLiteralBoundaryWalk_edges_alternate s r

end FiniteDefects

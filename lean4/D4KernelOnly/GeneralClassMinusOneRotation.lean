import D4KernelOnly.GeneralClassMinusOneCoefficient
import D4KernelOnly.D4AllBoundaryCoefficients

/-! # Threefold rotation of the general class-minus-one boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

theorem cmoRotateStage0 (s r : ℕ) :
    d4RotateVertex (cmoStage0 s r) = cmoStage8 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage0, cmoStage8] <;> ring
theorem cmoRotateStage1 (s r : ℕ) :
    d4RotateVertex (cmoStage1 s r) = cmoStage9 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage1, cmoStage9] <;> ring
theorem cmoRotateStage2 (s r : ℕ) :
    d4RotateVertex (cmoStage2 s r) = cmoStage10 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage2, cmoStage10] <;> ring
theorem cmoRotateStage3 (s r : ℕ) :
    d4RotateVertex (cmoStage3 s r) = cmoStage11 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage3, cmoStage11] <;> ring
theorem cmoRotateStage4 (s r : ℕ) :
    d4RotateVertex (cmoStage4 s r) = cmoStage0 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage4, cmoStage0] <;> ring
theorem cmoRotateStage5 (s r : ℕ) :
    d4RotateVertex (cmoStage5 s r) = cmoStage1 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage5, cmoStage1] <;> ring
theorem cmoRotateStage6 (s r : ℕ) :
    d4RotateVertex (cmoStage6 s r) = cmoStage2 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage6, cmoStage2] <;> ring
theorem cmoRotateStage7 (s r : ℕ) :
    d4RotateVertex (cmoStage7 s r) = cmoStage3 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage7, cmoStage3] <;> ring
theorem cmoRotateStage8 (s r : ℕ) :
    d4RotateVertex (cmoStage8 s r) = cmoStage4 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage8, cmoStage4] <;> ring
theorem cmoRotateStage9 (s r : ℕ) :
    d4RotateVertex (cmoStage9 s r) = cmoStage5 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage9, cmoStage5] <;> ring
theorem cmoRotateStage10 (s r : ℕ) :
    d4RotateVertex (cmoStage10 s r) = cmoStage6 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage10, cmoStage6] <;> ring
theorem cmoRotateStage11 (s r : ℕ) :
    d4RotateVertex (cmoStage11 s r) = cmoStage7 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, cmoStage11, cmoStage7] <;> ring

def cmoBoundaryChunk0 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage0 s r)
      (labeledStepWordPower d4LiteralStepBlock5 r) ++
    walkLabeledHexEdges (cmoStage1 s r) [(shadowC, .c)] ++
    walkLabeledHexEdges (cmoStage2 s r)
      (labeledStepWordPower d4LiteralStepBlock4 s) ++
    walkLabeledHexEdges (cmoStage3 s r) [(shadowC.neg, .c)]

def cmoBoundaryChunk1 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage4 s r)
      (labeledStepWordPower d4LiteralStepBlock3 r) ++
    walkLabeledHexEdges (cmoStage5 s r) [(shadowA, .a)] ++
    walkLabeledHexEdges (cmoStage6 s r)
      (labeledStepWordPower d4LiteralStepBlock2 s) ++
    walkLabeledHexEdges (cmoStage7 s r) [(shadowA.neg, .a)]

def cmoBoundaryChunk2 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (cmoStage8 s r)
      (labeledStepWordPower d4LiteralStepBlock1 r) ++
    walkLabeledHexEdges (cmoStage9 s r) [(shadowB, .b)] ++
    walkLabeledHexEdges (cmoStage10 s r)
      (labeledStepWordPower d4LiteralStepBlock0 s) ++
    walkLabeledHexEdges (cmoStage11 s r) [(shadowB.neg, .b)]

theorem classMinusOneBoundaryWalk_eq_chunks (s r : ℕ) :
    classMinusOneLiteralBoundaryWalk s r =
      cmoBoundaryChunk0 s r ++ cmoBoundaryChunk1 s r ++
        cmoBoundaryChunk2 s r := by
  rw [classMinusOneLiteralBoundaryWalk_eq_segments]
  simp [classMinusOneBoundaryWalkBySegments, cmoBoundaryChunk0,
    cmoBoundaryChunk1, cmoBoundaryChunk2, List.append_assoc]

theorem cmoRotateChunk0 (s r : ℕ) :
    (cmoBoundaryChunk0 s r).map d4RotateEdge =
      cmoBoundaryChunk2 s r := by
  simp [cmoBoundaryChunk0, cmoBoundaryChunk2,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    cmoRotateStage0, cmoRotateStage1, cmoRotateStage2, cmoRotateStage3,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem cmoRotateChunk1 (s r : ℕ) :
    (cmoBoundaryChunk1 s r).map d4RotateEdge =
      cmoBoundaryChunk0 s r := by
  simp [cmoBoundaryChunk1, cmoBoundaryChunk0,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    cmoRotateStage4, cmoRotateStage5, cmoRotateStage6, cmoRotateStage7,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem cmoRotateChunk2 (s r : ℕ) :
    (cmoBoundaryChunk2 s r).map d4RotateEdge =
      cmoBoundaryChunk1 s r := by
  simp [cmoBoundaryChunk2, cmoBoundaryChunk1,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    cmoRotateStage8, cmoRotateStage9, cmoRotateStage10, cmoRotateStage11,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem classMinusOneBoundaryWalk_rotate_perm (s r : ℕ) :
    List.Perm ((classMinusOneLiteralBoundaryWalk s r).map d4RotateEdge)
      (classMinusOneLiteralBoundaryWalk s r) := by
  rw [classMinusOneBoundaryWalk_eq_chunks, List.map_append, List.map_append,
    cmoRotateChunk0, cmoRotateChunk1, cmoRotateChunk2]
  have hperm : List.Perm
      (cmoBoundaryChunk2 s r ++
        (cmoBoundaryChunk0 s r ++ cmoBoundaryChunk1 s r))
      ((cmoBoundaryChunk0 s r ++ cmoBoundaryChunk1 s r) ++
        cmoBoundaryChunk2 s r) := List.perm_append_comm
  simpa [List.append_assoc] using hperm

end FiniteDefects

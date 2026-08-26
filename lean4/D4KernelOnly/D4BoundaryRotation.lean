import D4KernelOnly.D4RightmostPeelingSkeleton

/-! # Threefold rotation of the literal d=4 boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

def d4RotateVertex (vertex : HexVertex) : HexVertex :=
  (-vertex.1 + vertex.2, -vertex.1)

def d4RotateStep : ShadowStep → ShadowStep
  | ⟨x, y⟩ => ⟨-x + y, -x⟩

def d4RotateLabel : ShadowLabel → ShadowLabel
  | .a => .c
  | .b => .a
  | .c => .b

def d4RotateLabeledStep (step : D4LabeledStep) : D4LabeledStep :=
  (d4RotateStep step.1, d4RotateLabel step.2)

def d4RotateEdge (edge : LabeledHexEdge) : LabeledHexEdge where
  source := d4RotateVertex edge.source
  target := d4RotateVertex edge.target
  label := d4RotateLabel edge.label

theorem d4RotateVertex_addHexStep (vertex : HexVertex) (step : ShadowStep) :
    d4RotateVertex (addHexStep vertex step) =
      addHexStep (d4RotateVertex vertex) (d4RotateStep step) := by
  rcases vertex with ⟨x, y⟩
  rcases step with ⟨u, v⟩
  apply Prod.ext <;> simp [d4RotateVertex, d4RotateStep, addHexStep] <;> ring

theorem d4RotateEdge_advance (source : HexVertex)
    (step : ShadowStep) (label : ShadowLabel) :
    d4RotateEdge (advanceLabeledHexEdge source step label) =
      advanceLabeledHexEdge (d4RotateVertex source)
        (d4RotateStep step) (d4RotateLabel label) := by
  apply labeledHexEdge_ext
  · rfl
  · exact d4RotateVertex_addHexStep source step
  · rfl

theorem d4RotateEdge_walk (source : HexVertex)
    (steps : List D4LabeledStep) :
    (walkLabeledHexEdges source steps).map d4RotateEdge =
      walkLabeledHexEdges (d4RotateVertex source)
        (steps.map d4RotateLabeledStep) := by
  induction steps generalizing source with
  | nil => rfl
  | cons head tail ih =>
      simp only [walkLabeledHexEdges, List.map_cons]
      rw [d4RotateEdge_advance, ih]
      simp [d4RotateLabeledStep, advanceLabeledHexEdge,
        d4RotateVertex_addHexStep]

theorem d4RotateLabeledStep_power (word : List D4LabeledStep)
    (exponent : ℕ) :
    (labeledStepWordPower word exponent).map d4RotateLabeledStep =
      labeledStepWordPower (word.map d4RotateLabeledStep) exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [labeledStepWordPower_succ, List.map_append, ih,
        labeledStepWordPower_succ]

@[simp] theorem d4RotateBlock5 :
    d4LiteralStepBlock5.map d4RotateLabeledStep =
      d4LiteralStepBlock1 := by decide

@[simp] theorem d4RotateBlock4 :
    d4LiteralStepBlock4.map d4RotateLabeledStep =
      d4LiteralStepBlock0 := by decide

@[simp] theorem d4RotateBlock3 :
    d4LiteralStepBlock3.map d4RotateLabeledStep =
      d4LiteralStepBlock5 := by decide

@[simp] theorem d4RotateBlock2 :
    d4LiteralStepBlock2.map d4RotateLabeledStep =
      d4LiteralStepBlock4 := by decide

@[simp] theorem d4RotateBlock1 :
    d4LiteralStepBlock1.map d4RotateLabeledStep =
      d4LiteralStepBlock3 := by decide

@[simp] theorem d4RotateBlock0 :
    d4LiteralStepBlock0.map d4RotateLabeledStep =
      d4LiteralStepBlock2 := by decide

theorem d4RotateStage0 (m : ℕ) :
    d4RotateVertex (d4Stage0 m) = d4Stage8 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage0, d4Stage8] <;> ring

theorem d4RotateStage1 (m : ℕ) :
    d4RotateVertex (d4Stage1 m) = d4Stage9 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage1, d4Stage9] <;> ring

theorem d4RotateStage2 (m : ℕ) :
    d4RotateVertex (d4Stage2 m) = d4Stage10 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage2, d4Stage10] <;> ring

theorem d4RotateStage3 (m : ℕ) :
    d4RotateVertex (d4Stage3 m) = d4Stage11 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage3, d4Stage11] <;> ring

theorem d4RotateStage4 (m : ℕ) :
    d4RotateVertex (d4Stage4 m) = d4Stage0 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage4, d4Stage0] <;> ring

theorem d4RotateStage5 (m : ℕ) :
    d4RotateVertex (d4Stage5 m) = d4Stage1 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage5, d4Stage1] <;> ring

theorem d4RotateStage6 (m : ℕ) :
    d4RotateVertex (d4Stage6 m) = d4Stage2 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage6, d4Stage2] <;> ring

theorem d4RotateStage7 (m : ℕ) :
    d4RotateVertex (d4Stage7 m) = d4Stage3 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage7, d4Stage3] <;> ring

theorem d4RotateStage8 (m : ℕ) :
    d4RotateVertex (d4Stage8 m) = d4Stage4 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage8, d4Stage4] <;> ring

theorem d4RotateStage9 (m : ℕ) :
    d4RotateVertex (d4Stage9 m) = d4Stage5 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage9, d4Stage5] <;> ring

theorem d4RotateStage10 (m : ℕ) :
    d4RotateVertex (d4Stage10 m) = d4Stage6 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage10, d4Stage6] <;> ring

theorem d4RotateStage11 (m : ℕ) :
    d4RotateVertex (d4Stage11 m) = d4Stage7 m := by
  apply Prod.ext <;> simp [d4RotateVertex, d4Stage11, d4Stage7] <;> ring

def d4BoundarySegmentChunk0 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage0 m)
      (labeledStepWordPower d4LiteralStepBlock5 (m + 1)) ++
    walkLabeledHexEdges (d4Stage1 m) [(shadowC, .c)] ++
    walkLabeledHexEdges (d4Stage2 m) d4LiteralStepBlock4 ++
    walkLabeledHexEdges (d4Stage3 m) [(shadowC.neg, .c)]

def d4BoundarySegmentChunk1 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage4 m)
      (labeledStepWordPower d4LiteralStepBlock3 (m + 1)) ++
    walkLabeledHexEdges (d4Stage5 m) [(shadowA, .a)] ++
    walkLabeledHexEdges (d4Stage6 m) d4LiteralStepBlock2 ++
    walkLabeledHexEdges (d4Stage7 m) [(shadowA.neg, .a)]

def d4BoundarySegmentChunk2 (m : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (d4Stage8 m)
      (labeledStepWordPower d4LiteralStepBlock1 (m + 1)) ++
    walkLabeledHexEdges (d4Stage9 m) [(shadowB, .b)] ++
    walkLabeledHexEdges (d4Stage10 m) d4LiteralStepBlock0 ++
    walkLabeledHexEdges (d4Stage11 m) [(shadowB.neg, .b)]

theorem d4LiteralBoundaryWalk_eq_chunks (m : ℕ) :
    d4LiteralBoundaryWalk m =
      d4BoundarySegmentChunk0 m ++ d4BoundarySegmentChunk1 m ++
        d4BoundarySegmentChunk2 m := by
  rw [d4LiteralBoundaryWalk_eq_segments]
  simp [d4LiteralBoundaryWalkBySegments, d4BoundarySegmentChunk0,
    d4BoundarySegmentChunk1, d4BoundarySegmentChunk2,
    List.append_assoc]

theorem d4RotateChunk0 (m : ℕ) :
    (d4BoundarySegmentChunk0 m).map d4RotateEdge =
      d4BoundarySegmentChunk2 m := by
  simp [d4BoundarySegmentChunk0, d4BoundarySegmentChunk2,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    d4RotateStage0, d4RotateStage1, d4RotateStage2, d4RotateStage3,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem d4RotateChunk1 (m : ℕ) :
    (d4BoundarySegmentChunk1 m).map d4RotateEdge =
      d4BoundarySegmentChunk0 m := by
  simp [d4BoundarySegmentChunk1, d4BoundarySegmentChunk0,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    d4RotateStage4, d4RotateStage5, d4RotateStage6, d4RotateStage7,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem d4RotateChunk2 (m : ℕ) :
    (d4BoundarySegmentChunk2 m).map d4RotateEdge =
      d4BoundarySegmentChunk1 m := by
  simp [d4BoundarySegmentChunk2, d4BoundarySegmentChunk1,
    List.map_append, d4RotateEdge_walk, d4RotateLabeledStep_power,
    d4RotateStage8, d4RotateStage9, d4RotateStage10, d4RotateStage11,
    d4RotateLabeledStep, d4RotateStep, d4RotateLabel,
    shadowA, shadowB, shadowC, ShadowStep.neg]

theorem d4LiteralBoundaryWalk_rotate_perm (m : ℕ) :
    List.Perm ((d4LiteralBoundaryWalk m).map d4RotateEdge)
      (d4LiteralBoundaryWalk m) := by
  rw [d4LiteralBoundaryWalk_eq_chunks, List.map_append, List.map_append,
    d4RotateChunk0, d4RotateChunk1, d4RotateChunk2]
  have hperm : List.Perm
      (d4BoundarySegmentChunk2 m ++
        (d4BoundarySegmentChunk0 m ++ d4BoundarySegmentChunk1 m))
      ((d4BoundarySegmentChunk0 m ++ d4BoundarySegmentChunk1 m) ++
        d4BoundarySegmentChunk2 m) := List.perm_append_comm
  simpa [List.append_assoc] using hperm

end FiniteDefects

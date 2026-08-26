import D4KernelOnly.GeneralClassZeroCoefficient
import D4KernelOnly.D4AllBoundaryCoefficients

/-! # Threefold rotation of the general class-zero boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

set_option linter.unnecessarySeqFocus false

theorem czRotateStage0 (s r : ℕ) : d4RotateVertex (czStage0 s r) = czStage4 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage0, czStage4] <;> ring
theorem czRotateStage1 (s r : ℕ) : d4RotateVertex (czStage1 s r) = czStage5 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage1, czStage5] <;> ring
theorem czRotateStage2 (s r : ℕ) : d4RotateVertex (czStage2 s r) = czStage0 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage2, czStage0] <;> ring
theorem czRotateStage3 (s r : ℕ) : d4RotateVertex (czStage3 s r) = czStage1 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage3, czStage1] <;> ring
theorem czRotateStage4 (s r : ℕ) : d4RotateVertex (czStage4 s r) = czStage2 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage4, czStage2] <;> ring
theorem czRotateStage5 (s r : ℕ) : d4RotateVertex (czStage5 s r) = czStage3 s r := by
  apply Prod.ext <;> simp [d4RotateVertex, czStage5, czStage3] <;> ring

def czBoundaryChunk0 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czStage0 s r) (labeledHexStepWordPower czLiteralBlock5 r) ++
    walkLabeledHexEdges (czStage1 s r) (labeledHexStepWordPower czLiteralBlock4 s)

def czBoundaryChunk1 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czStage2 s r) (labeledHexStepWordPower czLiteralBlock3 r) ++
    walkLabeledHexEdges (czStage3 s r) (labeledHexStepWordPower czLiteralBlock2 s)

def czBoundaryChunk2 (s r : ℕ) : List LabeledHexEdge :=
  walkLabeledHexEdges (czStage4 s r) (labeledHexStepWordPower czLiteralBlock1 r) ++
    walkLabeledHexEdges (czStage5 s r) (labeledHexStepWordPower czLiteralBlock0 s)

theorem classZeroBoundaryWalk_eq_chunks (s r : ℕ) :
    classZeroLiteralBoundaryWalk s r =
      czBoundaryChunk0 s r ++ czBoundaryChunk1 s r ++ czBoundaryChunk2 s r := by
  rw [classZeroLiteralBoundaryWalk_eq_segments]
  simp [classZeroBoundaryWalkBySegments, czBoundaryChunk0,
    czBoundaryChunk1, czBoundaryChunk2, List.append_assoc]

theorem czRotateBlock5 :
    czLiteralBlock5.map d4RotateLabeledStep = czLiteralBlock1 := by decide
theorem czRotateBlock4 :
    czLiteralBlock4.map d4RotateLabeledStep = czLiteralBlock0 := by decide
theorem czRotateBlock3 :
    czLiteralBlock3.map d4RotateLabeledStep = czLiteralBlock5 := by decide
theorem czRotateBlock2 :
    czLiteralBlock2.map d4RotateLabeledStep = czLiteralBlock4 := by decide
theorem czRotateBlock1 :
    czLiteralBlock1.map d4RotateLabeledStep = czLiteralBlock3 := by decide
theorem czRotateBlock0 :
    czLiteralBlock0.map d4RotateLabeledStep = czLiteralBlock2 := by decide

theorem d4RotateLabeledHexStepPower
    (word : List LabeledHexStep) (n : ℕ) :
    (labeledHexStepWordPower word n).map d4RotateLabeledStep =
      labeledHexStepWordPower (word.map d4RotateLabeledStep) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [labeledHexStepWordPower_succ, List.map_append, ih,
        labeledHexStepWordPower_succ]

theorem czRotateChunk0 (s r : ℕ) :
    (czBoundaryChunk0 s r).map d4RotateEdge = czBoundaryChunk2 s r := by
  simp [czBoundaryChunk0, czBoundaryChunk2, List.map_append,
    d4RotateEdge_walk, d4RotateLabeledHexStepPower,
    czRotateStage0, czRotateStage1, czRotateBlock5, czRotateBlock4]

theorem czRotateChunk1 (s r : ℕ) :
    (czBoundaryChunk1 s r).map d4RotateEdge = czBoundaryChunk0 s r := by
  simp [czBoundaryChunk1, czBoundaryChunk0, List.map_append,
    d4RotateEdge_walk, d4RotateLabeledHexStepPower,
    czRotateStage2, czRotateStage3, czRotateBlock3, czRotateBlock2]

theorem czRotateChunk2 (s r : ℕ) :
    (czBoundaryChunk2 s r).map d4RotateEdge = czBoundaryChunk1 s r := by
  simp [czBoundaryChunk2, czBoundaryChunk1, List.map_append,
    d4RotateEdge_walk, d4RotateLabeledHexStepPower,
    czRotateStage4, czRotateStage5, czRotateBlock1, czRotateBlock0]

theorem classZeroBoundaryWalk_rotate_perm (s r : ℕ) :
    List.Perm ((classZeroLiteralBoundaryWalk s r).map d4RotateEdge)
      (classZeroLiteralBoundaryWalk s r) := by
  rw [classZeroBoundaryWalk_eq_chunks, List.map_append, List.map_append,
    czRotateChunk0, czRotateChunk1, czRotateChunk2]
  have hperm : List.Perm
      (czBoundaryChunk2 s r ++ (czBoundaryChunk0 s r ++ czBoundaryChunk1 s r))
      ((czBoundaryChunk0 s r ++ czBoundaryChunk1 s r) ++ czBoundaryChunk2 s r) :=
    List.perm_append_comm
  simpa [List.append_assoc] using hperm

end FiniteDefects

import D4KernelOnly.GeneralClassZeroAllCoefficients
import D4KernelOnly.D4BoundaryNodup

/-! # No repeated directed edge in the class-zero physical boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czStepPower_matches
    (word : List LabeledHexStep)
    (hword : ∀ step ∈ word, D4StepMatchesLabel step)
    (n : ℕ) : ∀ step ∈ labeledHexStepWordPower word n,
      D4StepMatchesLabel step := by
  intro step hstep
  rw [labeledHexStepWordPower_eq_labeledStepWordPower] at hstep
  exact d4StepWordPower_matches word hword n step hstep

theorem classZeroLiteralBoundarySteps_matches (s r : ℕ) :
    ∀ step ∈ classZeroLiteralBoundarySteps s r,
      D4StepMatchesLabel step := by
  rw [classZeroLiteralBoundarySteps_eq_explicit]
  intro step hstep
  simp only [classZeroLiteralBoundaryStepsExplicit, List.mem_append] at hstep
  rcases hstep with hstep | hstep | hstep | hstep | hstep | hstep
  · exact czStepPower_matches czLiteralBlock5
      (by simp [czLiteralBlock5, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₅, D4StepMatchesLabel])
      r step hstep
  · exact czStepPower_matches czLiteralBlock4
      (by simp [czLiteralBlock4, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₄, D4StepMatchesLabel])
      s step hstep
  · exact czStepPower_matches czLiteralBlock3
      (by simp [czLiteralBlock3, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₃, D4StepMatchesLabel])
      r step hstep
  · exact czStepPower_matches czLiteralBlock2
      (by simp [czLiteralBlock2, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₂, D4StepMatchesLabel])
      s step hstep
  · exact czStepPower_matches czLiteralBlock1
      (by simp [czLiteralBlock1, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₁, D4StepMatchesLabel])
      r step hstep
  · exact czStepPower_matches czLiteralBlock0
      (by simp [czLiteralBlock0, reverseClassZeroWord,
        reverseClassZeroStep, literalPeripheralBlock₀, D4StepMatchesLabel])
      s step hstep

theorem classZeroLiteralBoundaryWalk_matches (s r : ℕ) :
    ∀ edge ∈ classZeroLiteralBoundaryWalk s r,
      D4EdgeMatchesLabel edge := by
  unfold classZeroLiteralBoundaryWalk
  exact walkLabeledHexEdges_matches _ _
    (classZeroLiteralBoundarySteps_matches s r)

theorem czCedge_forward_or_reverse
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classZeroLiteralBoundaryWalk s r)
    (hlabel : edge.label = .c) :
    isForwardSideFiveEdge edge = true ∨ isReverseSideFiveEdge edge = true := by
  have hmatches := classZeroLiteralBoundaryWalk_matches s r edge hedge
  rcases hmatches with ⟨ha, _⟩ | ⟨hb, _⟩ | ⟨hc, hstep⟩
  · exact (by simp [hlabel] at ha)
  · exact (by simp [hlabel] at hb)
  · rcases hstep with hstep | hstep
    · right; simp [isReverseSideFiveEdge, hc, hstep]
    · left; simp [isForwardSideFiveEdge, hc, hstep]

theorem czForwardSideFiveEdges_nodup (s r : ℕ) :
    (forwardSideFiveEdges (classZeroLiteralBoundaryWalk s r)).Nodup := by
  rw [classZeroBoundaryWalk_forward, czWalkForwardSideFiveEdges]
  exact (czWalkForwardSideFiveCells_nodup s r).map
    cellBoundaryEdgeAt_sideFive_injective

theorem czReverseSideFiveEdges_nodup (s r : ℕ) :
    (reverseSideFiveEdges (classZeroLiteralBoundaryWalk s r)).Nodup := by
  rw [classZeroBoundaryWalk_reverse, czWalkReverseSideFiveEdges]
  exact (czWalkReverseSideFiveCells_nodup s r).map
    reverse_cellBoundaryEdgeAt_sideFive_injective

theorem czBoundary_cLabel_nodup (s r : ℕ) :
    (d4LabelEdges .c (classZeroLiteralBoundaryWalk s r)).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  by_cases hmem : edge ∈ d4LabelEdges .c (classZeroLiteralBoundaryWalk s r)
  · have hedge : edge ∈ classZeroLiteralBoundaryWalk s r := List.mem_of_mem_filter hmem
    have hlabel : edge.label = .c := by
      simpa [d4LabelEdges, isD4Label] using List.of_mem_filter hmem
    rcases czCedge_forward_or_reverse hedge hlabel with hforward | hreverse
    · have hcount := count_filter_eq_count_of_true
        (classZeroLiteralBoundaryWalk s r) isForwardSideFiveEdge edge hforward
      rw [← forwardSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c (classZeroLiteralBoundaryWalk s r)).count edge =
            (classZeroLiteralBoundaryWalk s r).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (forwardSideFiveEdges (classZeroLiteralBoundaryWalk s r)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (czForwardSideFiveEdges_nodup s r) edge
    · have hcount := count_filter_eq_count_of_true
        (classZeroLiteralBoundaryWalk s r) isReverseSideFiveEdge edge hreverse
      rw [← reverseSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c (classZeroLiteralBoundaryWalk s r)).count edge =
            (classZeroLiteralBoundaryWalk s r).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (reverseSideFiveEdges (classZeroLiteralBoundaryWalk s r)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (czReverseSideFiveEdges_nodup s r) edge
  · rw [List.count_eq_zero.mpr hmem]
    omega

theorem czBoundary_label_rotate_perm
    (s r : ℕ) (label : ShadowLabel) :
    List.Perm
      ((d4LabelEdges label (classZeroLiteralBoundaryWalk s r)).map d4RotateEdge)
      (d4LabelEdges (d4RotateLabel label) (classZeroLiteralBoundaryWalk s r)) := by
  rw [d4RotateLabelEdges]
  exact (classZeroBoundaryWalk_rotate_perm s r).filter
    (isD4Label (d4RotateLabel label))

theorem czBoundary_bLabel_nodup (s r : ℕ) :
    (d4LabelEdges .b (classZeroLiteralBoundaryWalk s r)).Nodup := by
  have hmap := (czBoundary_cLabel_nodup s r).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using czBoundary_label_rotate_perm s r .c)

theorem czBoundary_aLabel_nodup (s r : ℕ) :
    (d4LabelEdges .a (classZeroLiteralBoundaryWalk s r)).Nodup := by
  have hmap := (czBoundary_bLabel_nodup s r).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using czBoundary_label_rotate_perm s r .b)

theorem classZeroLiteralBoundaryWalk_nodup (s r : ℕ) :
    (classZeroLiteralBoundaryWalk s r).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  cases hlabel : edge.label
  · rw [← d4LabelEdges_count_eq .a _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (czBoundary_aLabel_nodup s r) edge
  · rw [← d4LabelEdges_count_eq .b _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (czBoundary_bLabel_nodup s r) edge
  · rw [← d4LabelEdges_count_eq .c _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (czBoundary_cLabel_nodup s r) edge

end FiniteDefects

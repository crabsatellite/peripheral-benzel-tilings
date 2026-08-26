import D4KernelOnly.GeneralClassMinusOnePeeling
import D4KernelOnly.D4BoundaryNodup

/-! # No repeated directed edge in the class-minus-one physical boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoLiteralBoundarySteps_matches (s r : ℕ) :
    ∀ step ∈ classMinusOneLiteralBoundarySteps s r,
      D4StepMatchesLabel step := by
  rw [classMinusOneLiteralBoundarySteps_eq_explicit]
  intro step hstep
  simp only [classMinusOneLiteralBoundaryStepsExplicit, List.mem_append,
    List.mem_singleton] at hstep
  rcases hstep with hstep | rfl | hstep | rfl | hstep | rfl |
      hstep | rfl | hstep | rfl | hstep | rfl
  · exact d4StepWordPower_matches d4LiteralStepBlock5
      (by simp [d4LiteralStepBlock5, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock4
      (by simp [d4LiteralStepBlock4, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock3
      (by simp [d4LiteralStepBlock3, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock2
      (by simp [d4LiteralStepBlock2, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock1
      (by simp [d4LiteralStepBlock1, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock0
      (by simp [d4LiteralStepBlock0, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]

theorem cmoLiteralBoundaryWalk_matches (s r : ℕ) :
    ∀ edge ∈ classMinusOneLiteralBoundaryWalk s r,
      D4EdgeMatchesLabel edge := by
  unfold classMinusOneLiteralBoundaryWalk
  exact walkLabeledHexEdges_matches _ _ (cmoLiteralBoundarySteps_matches s r)

theorem cmoCedge_forward_or_reverse
    {s r : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r)
    (hlabel : edge.label = .c) :
    isForwardSideFiveEdge edge = true ∨
      isReverseSideFiveEdge edge = true := by
  have hmatches := cmoLiteralBoundaryWalk_matches s r edge hedge
  rcases hmatches with ⟨ha, _⟩ | ⟨hb, _⟩ | ⟨hc, hstep⟩
  · exact (by simp [hlabel] at ha)
  · exact (by simp [hlabel] at hb)
  · rcases hstep with hstep | hstep
    · right; simp [isReverseSideFiveEdge, hc, hstep]
    · left; simp [isForwardSideFiveEdge, hc, hstep]

theorem cmoWalkForwardSideFiveEdges_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoWalkForwardSideFiveEdges s r).Nodup :=
  (cmoWalkForwardSideFiveCells_nodup s r hs).map
    cellBoundaryEdgeAt_sideFive_injective

theorem cmoWalkReverseSideFiveEdges_nodup (s r : ℕ) :
    (cmoWalkReverseSideFiveEdges s r).Nodup :=
  (cmoWalkReverseSideFiveCells_nodup s r).map
    reverse_cellBoundaryEdgeAt_sideFive_injective

theorem cmoForwardSideFiveEdges_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (forwardSideFiveEdges
      (classMinusOneLiteralBoundaryWalk s r)).Nodup := by
  rw [classMinusOneBoundaryWalk_forward]
  exact cmoWalkForwardSideFiveEdges_nodup s r hs

theorem cmoReverseSideFiveEdges_nodup (s r : ℕ) :
    (reverseSideFiveEdges
      (classMinusOneLiteralBoundaryWalk s r)).Nodup := by
  rw [classMinusOneBoundaryWalk_reverse]
  exact cmoWalkReverseSideFiveEdges_nodup s r

theorem cmoBoundary_cLabel_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (d4LabelEdges .c (classMinusOneLiteralBoundaryWalk s r)).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  by_cases hmem : edge ∈
      d4LabelEdges .c (classMinusOneLiteralBoundaryWalk s r)
  · have hedge : edge ∈ classMinusOneLiteralBoundaryWalk s r :=
      List.mem_of_mem_filter hmem
    have hlabel : edge.label = .c := by
      simpa [d4LabelEdges, isD4Label] using List.of_mem_filter hmem
    rcases cmoCedge_forward_or_reverse hedge hlabel with hforward | hreverse
    · have hcount := count_filter_eq_count_of_true
        (classMinusOneLiteralBoundaryWalk s r)
        isForwardSideFiveEdge edge hforward
      rw [← forwardSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c
            (classMinusOneLiteralBoundaryWalk s r)).count edge =
            (classMinusOneLiteralBoundaryWalk s r).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (forwardSideFiveEdges
              (classMinusOneLiteralBoundaryWalk s r)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (cmoForwardSideFiveEdges_nodup s r hs) edge
    · have hcount := count_filter_eq_count_of_true
        (classMinusOneLiteralBoundaryWalk s r)
        isReverseSideFiveEdge edge hreverse
      rw [← reverseSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c
            (classMinusOneLiteralBoundaryWalk s r)).count edge =
            (classMinusOneLiteralBoundaryWalk s r).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (reverseSideFiveEdges
              (classMinusOneLiteralBoundaryWalk s r)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (cmoReverseSideFiveEdges_nodup s r) edge
  · rw [List.count_eq_zero.mpr hmem]
    omega

theorem cmoBoundary_label_rotate_perm
    (s r : ℕ) (label : ShadowLabel) :
    List.Perm
      ((d4LabelEdges label
        (classMinusOneLiteralBoundaryWalk s r)).map d4RotateEdge)
      (d4LabelEdges (d4RotateLabel label)
        (classMinusOneLiteralBoundaryWalk s r)) := by
  rw [d4RotateLabelEdges]
  exact (classMinusOneBoundaryWalk_rotate_perm s r).filter
    (isD4Label (d4RotateLabel label))

theorem cmoBoundary_bLabel_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (d4LabelEdges .b (classMinusOneLiteralBoundaryWalk s r)).Nodup := by
  have hmap := (cmoBoundary_cLabel_nodup s r hs).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using cmoBoundary_label_rotate_perm s r .c)

theorem cmoBoundary_aLabel_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (d4LabelEdges .a (classMinusOneLiteralBoundaryWalk s r)).Nodup := by
  have hmap := (cmoBoundary_bLabel_nodup s r hs).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using cmoBoundary_label_rotate_perm s r .b)

theorem classMinusOneLiteralBoundaryWalk_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (classMinusOneLiteralBoundaryWalk s r).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  cases hlabel : edge.label
  · rw [← d4LabelEdges_count_eq .a _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp
      (cmoBoundary_aLabel_nodup s r hs) edge
  · rw [← d4LabelEdges_count_eq .b _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp
      (cmoBoundary_bLabel_nodup s r hs) edge
  · rw [← d4LabelEdges_count_eq .c _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp
      (cmoBoundary_cLabel_nodup s r hs) edge

end FiniteDefects

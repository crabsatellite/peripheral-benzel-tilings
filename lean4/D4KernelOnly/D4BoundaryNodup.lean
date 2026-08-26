import D4KernelOnly.D4AllBoundaryCoefficients
import BenzelProblem6Kernel.GeometricBacktrackReduction

/-! # No repeated directed edge in the literal physical d=4 boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

def D4EdgeMatchesLabel (edge : LabeledHexEdge) : Prop :=
  (edge.label = .a ∧
      (edge.target = addHexStep edge.source shadowA ∨
        edge.target = addHexStep edge.source shadowA.neg)) ∨
  (edge.label = .b ∧
      (edge.target = addHexStep edge.source shadowB ∨
        edge.target = addHexStep edge.source shadowB.neg)) ∨
  (edge.label = .c ∧
      (edge.target = addHexStep edge.source shadowC ∨
        edge.target = addHexStep edge.source shadowC.neg))

def D4StepMatchesLabel (step : D4LabeledStep) : Prop :=
  (step.2 = .a ∧ (step.1 = shadowA ∨ step.1 = shadowA.neg)) ∨
  (step.2 = .b ∧ (step.1 = shadowB ∨ step.1 = shadowB.neg)) ∨
  (step.2 = .c ∧ (step.1 = shadowC ∨ step.1 = shadowC.neg))

theorem d4StepWordPower_matches
    (word : List D4LabeledStep)
    (hword : ∀ step ∈ word, D4StepMatchesLabel step) :
    ∀ exponent step, step ∈ labeledStepWordPower word exponent →
      D4StepMatchesLabel step := by
  intro exponent
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      intro step hstep
      rw [labeledStepWordPower_succ, List.mem_append] at hstep
      exact hstep.elim (ih step) (hword step)

theorem d4LiteralBoundarySteps_matches (m : ℕ) :
    ∀ step ∈ d4LiteralBoundarySteps m, D4StepMatchesLabel step := by
  rw [d4LiteralBoundarySteps_eq_explicit]
  intro step hstep
  simp only [d4LiteralBoundaryStepsExplicit, List.mem_append,
    List.mem_singleton] at hstep
  rcases hstep with hstep | rfl | hstep | rfl | hstep | rfl |
      hstep | rfl | hstep | rfl | hstep | rfl
  · exact d4StepWordPower_matches d4LiteralStepBlock5
      (by simp [d4LiteralStepBlock5, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · simp [d4LiteralStepBlock4, D4StepMatchesLabel] at hstep ⊢
    rcases hstep with rfl | rfl | rfl | rfl <;> simp [D4StepMatchesLabel]
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock3
      (by simp [d4LiteralStepBlock3, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · simp [d4LiteralStepBlock2, D4StepMatchesLabel] at hstep ⊢
    rcases hstep with rfl | rfl | rfl | rfl <;> simp [D4StepMatchesLabel]
  · simp [D4StepMatchesLabel]
  · exact d4StepWordPower_matches d4LiteralStepBlock1
      (by simp [d4LiteralStepBlock1, D4StepMatchesLabel]) _ step hstep
  · simp [D4StepMatchesLabel]
  · simp [d4LiteralStepBlock0, D4StepMatchesLabel] at hstep ⊢
    rcases hstep with rfl | rfl | rfl | rfl <;> simp [D4StepMatchesLabel]
  · simp [D4StepMatchesLabel]

theorem walkLabeledHexEdges_matches
    (source : HexVertex) (steps : List D4LabeledStep)
    (hsteps : ∀ step ∈ steps, D4StepMatchesLabel step) :
    ∀ edge ∈ walkLabeledHexEdges source steps,
      D4EdgeMatchesLabel edge := by
  induction steps generalizing source with
  | nil =>
      intro edge hedge
      exact (List.not_mem_nil edge hedge).elim
  | cons head tail ih =>
      intro edge hedge
      simp only [walkLabeledHexEdges, List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · rcases head with ⟨step, label⟩
        have hhead := hsteps (step, label) (by simp)
        rcases hhead with ⟨hlabel, hstep⟩ |
            ⟨hlabel, hstep⟩ | ⟨hlabel, hstep⟩
        all_goals rcases hstep with rfl | rfl
        all_goals change label = _ at hlabel
        all_goals subst label
        all_goals simp [D4EdgeMatchesLabel, advanceLabeledHexEdge]
      · exact ih (addHexStep source head.1)
          (fun step hstep => hsteps step (by simp [hstep])) edge hedge

theorem d4LiteralBoundaryWalk_matches (m : ℕ) :
    ∀ edge ∈ d4LiteralBoundaryWalk m, D4EdgeMatchesLabel edge := by
  unfold d4LiteralBoundaryWalk
  exact walkLabeledHexEdges_matches _ _ (d4LiteralBoundarySteps_matches m)

def isD4Label (label : ShadowLabel) (edge : LabeledHexEdge) : Bool :=
  edge.label == label

def d4LabelEdges (label : ShadowLabel) (edges : List LabeledHexEdge) :
    List LabeledHexEdge := edges.filter (isD4Label label)

theorem d4LabelEdges_count_eq
    (label : ShadowLabel) (edges : List LabeledHexEdge)
    (edge : LabeledHexEdge) (hlabel : edge.label = label) :
    (d4LabelEdges label edges).count edge = edges.count edge := by
  apply count_filter_eq_count_of_true
  simp [isD4Label, hlabel]

theorem d4Cedge_forward_or_reverse {m : ℕ} {edge : LabeledHexEdge}
    (hedge : edge ∈ d4LiteralBoundaryWalk m) (hlabel : edge.label = .c) :
    isForwardSideFiveEdge edge = true ∨
      isReverseSideFiveEdge edge = true := by
  have hmatches := d4LiteralBoundaryWalk_matches m edge hedge
  rcases hmatches with ⟨ha, _⟩ | ⟨hb, _⟩ | ⟨hc, hstep⟩
  · exact (by simp [hlabel] at ha)
  · exact (by simp [hlabel] at hb)
  · rcases hstep with hstep | hstep
    · right
      simp [isReverseSideFiveEdge, hc, hstep]
    · left
      simp [isForwardSideFiveEdge, hc, hstep]

theorem d4WalkForwardSideFiveEdges_nodup (m : ℕ) :
    (d4WalkForwardSideFiveEdges m).Nodup :=
  (d4WalkForwardSideFiveCells_nodup m).map
    cellBoundaryEdgeAt_sideFive_injective

theorem d4WalkReverseSideFiveEdges_nodup (m : ℕ) :
    (d4WalkReverseSideFiveEdges m).Nodup :=
  (d4WalkReverseSideFiveCells_nodup m).map
    reverse_cellBoundaryEdgeAt_sideFive_injective

theorem forwardSideFiveEdges_nodup (m : ℕ) :
    (forwardSideFiveEdges (d4LiteralBoundaryWalk m)).Nodup := by
  rw [d4LiteralBoundaryWalk_forward]
  exact d4WalkForwardSideFiveEdges_nodup m

theorem reverseSideFiveEdges_nodup (m : ℕ) :
    (reverseSideFiveEdges (d4LiteralBoundaryWalk m)).Nodup := by
  rw [d4LiteralBoundaryWalk_reverse]
  exact d4WalkReverseSideFiveEdges_nodup m

theorem d4Boundary_cLabel_nodup (m : ℕ) :
    (d4LabelEdges .c (d4LiteralBoundaryWalk m)).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  by_cases hmem : edge ∈ d4LabelEdges .c (d4LiteralBoundaryWalk m)
  · have hedge : edge ∈ d4LiteralBoundaryWalk m :=
      List.mem_of_mem_filter hmem
    have hlabel : edge.label = .c := by
      simpa [d4LabelEdges, isD4Label] using List.of_mem_filter hmem
    rcases d4Cedge_forward_or_reverse hedge hlabel with hforward | hreverse
    · have hcount := count_filter_eq_count_of_true
        (d4LiteralBoundaryWalk m) isForwardSideFiveEdge edge hforward
      rw [← forwardSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c (d4LiteralBoundaryWalk m)).count edge =
            (d4LiteralBoundaryWalk m).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (forwardSideFiveEdges (d4LiteralBoundaryWalk m)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (forwardSideFiveEdges_nodup m) edge
    · have hcount := count_filter_eq_count_of_true
        (d4LiteralBoundaryWalk m) isReverseSideFiveEdge edge hreverse
      rw [← reverseSideFiveEdges] at hcount
      calc
        (d4LabelEdges .c (d4LiteralBoundaryWalk m)).count edge =
            (d4LiteralBoundaryWalk m).count edge :=
          d4LabelEdges_count_eq .c _ edge hlabel
        _ = (reverseSideFiveEdges (d4LiteralBoundaryWalk m)).count edge :=
          hcount.symm
        _ ≤ 1 := List.nodup_iff_count_le_one.mp
          (reverseSideFiveEdges_nodup m) edge
  · rw [List.count_eq_zero.mpr hmem]
    omega

theorem d4RotateLabelEdges (label : ShadowLabel)
    (edges : List LabeledHexEdge) :
    (d4LabelEdges label edges).map d4RotateEdge =
      d4LabelEdges (d4RotateLabel label) (edges.map d4RotateEdge) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      rcases edge with ⟨source, target, edgeLabel⟩
      cases label <;> cases edgeLabel
      all_goals
        simpa [d4LabelEdges, isD4Label, d4RotateEdge, d4RotateLabel] using ih

theorem d4Boundary_label_rotate_perm (m : ℕ) (label : ShadowLabel) :
    List.Perm ((d4LabelEdges label (d4LiteralBoundaryWalk m)).map
        d4RotateEdge)
      (d4LabelEdges (d4RotateLabel label) (d4LiteralBoundaryWalk m)) := by
  rw [d4RotateLabelEdges]
  exact (d4LiteralBoundaryWalk_rotate_perm m).filter
    (isD4Label (d4RotateLabel label))

theorem d4Boundary_bLabel_nodup (m : ℕ) :
    (d4LabelEdges .b (d4LiteralBoundaryWalk m)).Nodup := by
  have hmap := (d4Boundary_cLabel_nodup m).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using d4Boundary_label_rotate_perm m .c)

theorem d4Boundary_aLabel_nodup (m : ℕ) :
    (d4LabelEdges .a (d4LiteralBoundaryWalk m)).Nodup := by
  have hmap := (d4Boundary_bLabel_nodup m).map d4RotateEdge_injective
  exact hmap.perm (by
    simpa [d4RotateLabel] using d4Boundary_label_rotate_perm m .b)

theorem d4LiteralBoundaryWalk_nodup (m : ℕ) :
    (d4LiteralBoundaryWalk m).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro edge
  cases hlabel : edge.label
  · rw [← d4LabelEdges_count_eq .a _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (d4Boundary_aLabel_nodup m) edge
  · rw [← d4LabelEdges_count_eq .b _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (d4Boundary_bLabel_nodup m) edge
  · rw [← d4LabelEdges_count_eq .c _ edge hlabel]
    exact List.nodup_iff_count_le_one.mp (d4Boundary_cLabel_nodup m) edge

end FiniteDefects

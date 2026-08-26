import FiniteDefects.D4SourceCover

/-! # Every good edge ends at its labelled boundary through unique successors -/

namespace FiniteDefects

theorem d4_edge_target_boundary_or_successor {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    (∃ endpointLabel, edge.target = d4BoundaryOwner m endpointLabel ∧
      edge.label = endpointLabel) ∨
    (∃! successor : D4GoodBonePlacement tiling,
      successor.source = edge.target ∧ successor.label = edge.label) := by
  have hactive : edge.target ∈ d4ActiveOwnerSet tiling := by
    simp [d4ActiveOwnerSet, d4Edge_target_active edge]
  rw [← d4_source_union_boundary_eq_active tiling] at hactive
  simp only [Finset.mem_union] at hactive
  rcases hactive with hsource | hboundary
  · right
    simp only [d4EdgeSourceSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hsource
    obtain ⟨successor, hsource⟩ := hsource
    have hlabel : successor.label = edge.label := by
      by_contra hne
      have hcurrentPresent := d4GoodEdge_target_present edge.edge
      have hcurrentCover := d4TilingEdge_covers_target edge hcurrentPresent
      have hsuccessorPresent : inBenzel (m + 4) (2 * m + 4)
          (ownerCell successor.source edge.label) := by
        simpa [hsource] using hcurrentPresent
      have hsuccessorCover := d4TilingEdge_covers_source_other successor
        edge.label (fun heq => hne heq.symm) hsuccessorPresent
      have hcurrentEq := d4CoveringPlacement_unique tiling
        ⟨ownerCell edge.target edge.label, hcurrentPresent⟩ edge.1 edge.2.1
        hcurrentCover
      have hsuccessorEq := d4CoveringPlacement_unique tiling
        ⟨ownerCell edge.target edge.label, hcurrentPresent⟩ successor.1
        successor.2.1 (by simpa [hsource] using hsuccessorCover)
      have heq : edge = successor := by
        apply Subtype.ext
        exact hcurrentEq.trans hsuccessorEq.symm
      exact hne (congrArg D4GoodBonePlacement.label heq).symm
    refine ⟨successor, ⟨hsource, hlabel⟩, ?_⟩
    intro candidate hcandidate
    exact d4TilingEdge_source_unique candidate successor
      (hcandidate.1.trans hsource.symm)
  · left
    simp only [d4BoundaryOwnerSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hboundary
    obtain ⟨endpointLabel, htarget⟩ := hboundary
    have hpresent := d4GoodEdge_target_present edge.edge
    have hlabel : edge.label = endpointLabel :=
      (d4BoundaryOwner_present_iff m endpointLabel edge.label).1 (by
        simpa [htarget] using hpresent)
    exact ⟨endpointLabel, htarget.symm, hlabel⟩

noncomputable def d4Successor {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotBoundary : ¬∃ endpointLabel,
      edge.target = d4BoundaryOwner m endpointLabel ∧ edge.label = endpointLabel) :
    D4GoodBonePlacement tiling :=
  ((d4_edge_target_boundary_or_successor edge).resolve_left
    hnotBoundary).choose

theorem d4Successor_source {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotBoundary) :
    (d4Successor edge hnotBoundary).source = edge.target :=
  ((d4_edge_target_boundary_or_successor edge).resolve_left
    hnotBoundary).choose_spec.1.1

theorem d4Successor_label {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotBoundary) :
    (d4Successor edge hnotBoundary).label = edge.label :=
  ((d4_edge_target_boundary_or_successor edge).resolve_left
    hnotBoundary).choose_spec.1.2

theorem d4LabelRank_le_twice {t : ℕ} (label : MicroLabel)
    (p : SimplexPoint t) : d4LabelRank label p ≤ 2 * t := by
  have hsum := p.sum_eq
  rcases label <;> simp [d4LabelRank] <;> omega

noncomputable def d4ForwardMeasure {m : ℕ} {tiling : D4LiteralTiling m}
    (edge : D4GoodBonePlacement tiling) : ℕ :=
  2 * (m + 2) - d4LabelRank edge.label edge.target

theorem d4Successor_measure_lt {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling)
    (hnotBoundary) :
    d4ForwardMeasure (d4Successor edge hnotBoundary) <
      d4ForwardMeasure edge := by
  have hstep := d4TilingEdge_rank_step (d4Successor edge hnotBoundary)
  rw [d4Successor_source edge hnotBoundary,
    d4Successor_label edge hnotBoundary] at hstep
  have hbound := d4LabelRank_le_twice edge.label edge.target
  have hbound' := d4LabelRank_le_twice edge.label
    (d4Successor edge hnotBoundary).target
  unfold d4ForwardMeasure
  rw [d4Successor_label edge hnotBoundary]
  omega

theorem reversePath_previous_mem {m : ℕ}
    {tiling : D4LiteralTiling m} {label : MicroLabel}
    {terminal : SimplexPoint (m + 2)}
    {edges : List (D4GoodBonePlacement tiling)}
    (hpath : IsD4ReversePath label terminal
      (d4DefectCore tiling label) edges)
    (edge : D4GoodBonePlacement tiling) (hmem : edge ∈ edges)
    (hnotcore : edge.source ≠ d4DefectCore tiling edge.label) :
    d4PreviousEdge edge hnotcore ∈ edges := by
  induction edges generalizing terminal with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [IsD4ReversePath] at hpath
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst head
        have hedgeLabel : edge.label = label := hpath.2.1
        cases rest with
        | nil =>
            simp only [IsD4ReversePath] at hpath
            apply False.elim
            apply hnotcore
            rw [hedgeLabel]
            exact hpath.2.2
        | cons next tail =>
            simp only [IsD4ReversePath] at hpath
            have hnext : next = d4PreviousEdge edge hnotcore :=
              (d4_edge_source_predecessor edge hnotcore).choose_spec.2 next
                ⟨hpath.2.2.1, hpath.2.2.2.1.trans hedgeLabel.symm⟩
            simp [hnext]
      · exact List.mem_cons_of_mem head (ih hpath.2.2 hmem)

theorem d4ReversePathFromEdge_head {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    edge ∈ d4ReversePathFromEdge edge := by
  unfold d4ReversePathFromEdge
  rw [d4ReversePathFromEdgeData]
  split <;> simp

noncomputable def d4EdgeCanonicalEndpoint {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    {endpointLabel : MicroLabel //
      edge.label = endpointLabel ∧
        edge ∈ d4ReverseBoundaryPath tiling endpointLabel} := by
  by_cases hboundary : ∃ endpointLabel,
      edge.target = d4BoundaryOwner m endpointLabel ∧ edge.label = endpointLabel
  · have htargetSelf : edge.target = d4BoundaryOwner m edge.label := by
      have htarget := hboundary.choose_spec.1
      have hlabel := hboundary.choose_spec.2
      rw [hlabel]
      exact htarget
    refine ⟨edge.label, rfl, ?_⟩
    have hpath := d4ReversePathFromEdge_spec edge
    rw [htargetSelf] at hpath
    have heq := d4ReverseBoundaryPath_unique tiling edge.label
      (d4ReversePathFromEdge edge) hpath
    rw [← heq]
    exact d4ReversePathFromEdge_head edge
  · let successor := d4Successor edge hboundary
    let tail := d4EdgeCanonicalEndpoint successor
    refine ⟨tail.1, (d4Successor_label edge hboundary).symm.trans tail.2.1, ?_⟩
    have hsuccessorMem := tail.2.2
    have hpath := d4ReverseBoundaryPath_spec tiling tail.1
    have hlabel : successor.label = tail.1 := tail.2.1
    have hnotcore : successor.source ≠
        d4DefectCore tiling successor.label := by
      rw [d4Successor_source edge hboundary,
        d4Successor_label edge hboundary]
      exact d4TilingEdge_target_ne_core edge
    have hpreviousMem := reversePath_previous_mem hpath successor
      hsuccessorMem (by simpa [hlabel] using hnotcore)
    have hprevious : d4PreviousEdge successor hnotcore = edge := by
      apply d4TilingEdge_target_label_unique
      · rw [d4PreviousEdge_target successor hnotcore,
          d4Successor_source edge hboundary]
      · rw [d4PreviousEdge_label successor hnotcore,
          d4Successor_label edge hboundary]
    simpa [hprevious] using hpreviousMem
termination_by d4ForwardMeasure edge
decreasing_by exact d4Successor_measure_lt edge hboundary

end FiniteDefects

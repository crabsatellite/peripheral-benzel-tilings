import BenzelProblem6Kernel.EdgePotentialRank

/-!
# Backward termination at a labelled corner source
-/

namespace BenzelProblem6Kernel

theorem exists_corner_ancestor
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    ∃ rootEdge ∈ literalDirectedEdges hstone tiling,
      (rootEdge.source = sourceZero (m + 3) ∨
        rootEdge.source = sourceOne (m + 3) ∨
        rootEdge.source = sourceTwo (m + 3)) ∧
      rootEdge.boneClass.label = edge.boneClass.label := by
  generalize hrank : simplexLabelRank edge.boneClass.label edge.source = rank
  induction rank using Nat.strong_induction_on generalizing edge with
  | h rank ih =>
      rcases simplex_corner_or_full (t := m + 3) (by omega) edge.source with
        hzero | hone | htwo | hfull
      · exact ⟨edge, hedge, Or.inl hzero, rfl⟩
      · exact ⟨edge, hedge, Or.inr (Or.inl hone), rfl⟩
      · exact ⟨edge, hedge, Or.inr (Or.inr htwo), rfl⟩
      · obtain ⟨inEdge, hin, htarget, hlabel⟩ :=
          exists_incoming_same_label_at_full_source hstone tiling edge hedge
            hfull.1 hfull.2.1 hfull.2.2
        have hlt : simplexLabelRank inEdge.boneClass.label inEdge.source < rank := by
          have hlt' := incoming_rank_lt_source_rank inEdge edge htarget hlabel
          rw [hrank] at hlt'
          simpa [hlabel] using hlt'
        obtain ⟨rootEdge, hroot, hcorner, hrootLabel⟩ :=
          ih _ hlt inEdge hin rfl
        exact ⟨rootEdge, hroot, hcorner, hrootLabel.trans hlabel⟩

theorem corner_ancestor_of_label_zero
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling)
    (hlabel : edge.boneClass.label = .zero) :
    ∃ rootEdge ∈ literalDirectedEdges hstone tiling,
      rootEdge.source = sourceZero (m + 3) ∧
        rootEdge.boneClass.label = .zero := by
  obtain ⟨root, hroot, hcorner, hrootLabel⟩ :=
    exists_corner_ancestor hstone tiling edge hedge
  rcases hcorner with hzero | hone | htwo
  · exact ⟨root, hroot, hzero, hrootLabel.trans hlabel⟩
  · have := edge_from_sourceOne_has_label_one root hone
    rw [hrootLabel, hlabel] at this
    contradiction
  · have := edge_from_sourceTwo_has_label_two root htwo
    rw [hrootLabel, hlabel] at this
    contradiction

theorem corner_ancestor_of_label_one
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling)
    (hlabel : edge.boneClass.label = .one) :
    ∃ rootEdge ∈ literalDirectedEdges hstone tiling,
      rootEdge.source = sourceOne (m + 3) ∧
        rootEdge.boneClass.label = .one := by
  obtain ⟨root, hroot, hcorner, hrootLabel⟩ :=
    exists_corner_ancestor hstone tiling edge hedge
  rcases hcorner with hzero | hone | htwo
  · have := edge_from_sourceZero_has_label_zero root hzero
    rw [hrootLabel, hlabel] at this
    contradiction
  · exact ⟨root, hroot, hone, hrootLabel.trans hlabel⟩
  · have := edge_from_sourceTwo_has_label_two root htwo
    rw [hrootLabel, hlabel] at this
    contradiction

theorem corner_ancestor_of_label_two
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling)
    (hlabel : edge.boneClass.label = .two) :
    ∃ rootEdge ∈ literalDirectedEdges hstone tiling,
      rootEdge.source = sourceTwo (m + 3) ∧
        rootEdge.boneClass.label = .two := by
  obtain ⟨root, hroot, hcorner, hrootLabel⟩ :=
    exists_corner_ancestor hstone tiling edge hedge
  rcases hcorner with hzero | hone | htwo
  · have := edge_from_sourceZero_has_label_zero root hzero
    rw [hrootLabel, hlabel] at this
    contradiction
  · have := edge_from_sourceOne_has_label_one root hone
    rw [hrootLabel, hlabel] at this
    contradiction
  · exact ⟨root, hroot, htwo, hrootLabel.trans hlabel⟩

end BenzelProblem6Kernel

import BenzelProblem6Kernel.SinkCandidateType

/-!
# Corner source labels and full-owner pass-through labels
-/

namespace BenzelProblem6Kernel

theorem edge_from_sourceZero_has_label_zero {m : ℕ}
    (edge : LiteralDirectedEdge m)
    (hsource : edge.source = sourceZero (m + 3)) :
    edge.boneClass.label = .zero := by
  by_contra hlabel
  have hmem := literalDirectedEdge_source_cell_mem edge .zero
    (fun h => hlabel h.symm)
  have hmissing := (owner_zero_missing_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  rw [hsource] at hmem
  exact hmissing hmem

theorem edge_from_sourceOne_has_label_one {m : ℕ}
    (edge : LiteralDirectedEdge m)
    (hsource : edge.source = sourceOne (m + 3)) :
    edge.boneClass.label = .one := by
  by_contra hlabel
  have hmem := literalDirectedEdge_source_cell_mem edge .one
    (fun h => hlabel h.symm)
  have hmissing := (owner_one_missing_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  rw [hsource] at hmem
  exact hmissing hmem

theorem edge_from_sourceTwo_has_label_two {m : ℕ}
    (edge : LiteralDirectedEdge m)
    (hsource : edge.source = sourceTwo (m + 3)) :
    edge.boneClass.label = .two := by
  by_contra hlabel
  have hmem := literalDirectedEdge_source_cell_mem edge .two
    (fun h => hlabel h.symm)
  have hmissing := (owner_two_missing_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  rw [hsource] at hmem
  exact hmissing hmem

theorem exists_incoming_same_label_at_full_source
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (outEdge : LiteralDirectedEdge m)
    (hout : outEdge ∈ literalDirectedEdges hstone tiling)
    (hu : outEdge.source.u < m + 3)
    (hv : outEdge.source.v < m + 3)
    (hw : outEdge.source.w < m + 3) :
    ∃ inEdge ∈ literalDirectedEdges hstone tiling,
      inEdge.target = outEdge.source ∧
        inEdge.boneClass.label = outEdge.boneClass.label := by
  have hpActive := edge_source_mem_active hstone tiling outEdge hout
  have hmem : inPeripheralBenzel (m + 5)
      (ownerCell outEdge.source outEdge.boneClass.label) := by
    rcases hlabel : outEdge.boneClass.label with _ | _ | _
    · exact (owner_zero_mem_iff (n := m + 5) (by omega) outEdge.source).2 hv
    · exact (owner_one_mem_iff (n := m + 5) (by omega) outEdge.source).2 hw
    · exact (owner_two_mem_iff (n := m + 5) (by omega) outEdge.source).2 hu
  obtain ⟨edge, hedge, hrole⟩ := active_owner_present_label_role hstone tiling
    outEdge.source hpActive outEdge.boneClass.label hmem
  rcases hrole with hsource | htarget
  · have hedgeEq : edge = outEdge :=
      edgeSource_injective_on hstone tiling hedge hout hsource.1
    subst edge
    exact (hsource.2 rfl).elim
  · exact ⟨edge, hedge, htarget⟩

theorem incoming_same_label_unique
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (p : SimplexPoint (m + 3)) (label : MicroLabel)
    (left right : LiteralDirectedEdge m)
    (hleft : left ∈ literalDirectedEdges hstone tiling)
    (hright : right ∈ literalDirectedEdges hstone tiling)
    (hleftTarget : left.target = p) (hrightTarget : right.target = p)
    (hleftLabel : left.boneClass.label = label)
    (hrightLabel : right.boneClass.label = label) : left = right := by
  apply literalEdges_eq_of_placement_eq hstone tiling hleft hright
  apply edge_placements_eq_of_same_target_label hstone tiling hleft hright
  · exact hleftTarget.trans hrightTarget.symm
  · exact hleftLabel.trans hrightLabel.symm

theorem incoming_to_full_source_has_outgoing_label
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (inEdge outEdge : LiteralDirectedEdge m)
    (hin : inEdge ∈ literalDirectedEdges hstone tiling)
    (hout : outEdge ∈ literalDirectedEdges hstone tiling)
    (hmeet : inEdge.target = outEdge.source) :
    inEdge.boneClass.label = outEdge.boneClass.label := by
  by_contra hlabel
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell outEdge.source inEdge.boneClass.label,
      literalDirectedEdge_source_cell_mem outEdge inEdge.boneClass.label
        hlabel⟩
  have houtCover : PlacementCovers outEdge.placement cell :=
    literalDirectedEdge_covers_source_cell outEdge inEdge.boneClass.label
      hlabel
  have hinCover : PlacementCovers inEdge.placement cell := by
    have hc := literalDirectedEdge_covers_target_cell inEdge
    have hcell :
        (⟨ownerCell inEdge.target inEdge.boneClass.label,
          literalDirectedEdge_target_cell_mem inEdge⟩ : BenzelCell (m + 5)) =
          cell := by
      apply Subtype.ext
      simp [cell, hmeet]
    simpa [hcell] using hc
  have houtMem := (mem_literalDirectedEdges_placement hstone tiling outEdge hout).1
  have hinMem := (mem_literalDirectedEdges_placement hstone tiling inEdge hin).1
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have hplacements :=
    (hunique inEdge.placement ⟨hinMem, hinCover⟩).trans
      (hunique outEdge.placement ⟨houtMem, houtCover⟩).symm
  have hedgeEq := literalEdges_eq_of_placement_eq hstone tiling hin hout hplacements
  subst inEdge
  exact literalDirectedEdge_source_ne_target outEdge hmeet.symm

end BenzelProblem6Kernel

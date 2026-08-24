import BenzelProblem6Kernel.CornerAncestor

/-!
# Finite same-label paths in the literal edge graph
-/

namespace BenzelProblem6Kernel

inductive LiteralEdgePath
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    LiteralDirectedEdge m → LiteralDirectedEdge m → Prop
  | single (edge : LiteralDirectedEdge m)
      (hedge : edge ∈ literalDirectedEdges hstone tiling) :
      LiteralEdgePath hstone tiling edge edge
  | snoc {first last next : LiteralDirectedEdge m}
      (path : LiteralEdgePath hstone tiling first last)
      (hnext : next ∈ literalDirectedEdges hstone tiling)
      (hmeet : last.target = next.source)
      (hlabel : last.boneClass.label = next.boneClass.label) :
      LiteralEdgePath hstone tiling first next

theorem LiteralEdgePath.first_mem
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last) :
    first ∈ literalDirectedEdges hstone tiling := by
  induction path with
  | single hedge => exact hedge
  | snoc path _ _ _ ih => exact ih

theorem LiteralEdgePath.last_mem
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last) :
    last ∈ literalDirectedEdges hstone tiling := by
  cases path with
  | single hedge => exact hedge
  | snoc _ hnext _ _ => exact hnext

theorem LiteralEdgePath.label_eq
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last) :
    first.boneClass.label = last.boneClass.label := by
  induction path with
  | single => rfl
  | snoc path _ _ hlabel ih => exact ih.trans hlabel

theorem exists_corner_ancestor_path
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    ∃ rootEdge,
      LiteralEdgePath hstone tiling rootEdge edge ∧
      (rootEdge.source = sourceZero (m + 3) ∨
        rootEdge.source = sourceOne (m + 3) ∨
        rootEdge.source = sourceTwo (m + 3)) := by
  generalize hrank : simplexLabelRank edge.boneClass.label edge.source = rank
  induction rank using Nat.strong_induction_on generalizing edge with
  | h rank ih =>
      rcases simplex_corner_or_full (t := m + 3) (by omega) edge.source with
        hzero | hone | htwo | hfull
      · exact ⟨edge, LiteralEdgePath.single edge hedge, Or.inl hzero⟩
      · exact ⟨edge, LiteralEdgePath.single edge hedge, Or.inr (Or.inl hone)⟩
      · exact ⟨edge, LiteralEdgePath.single edge hedge, Or.inr (Or.inr htwo)⟩
      · obtain ⟨inEdge, hin, htarget, hlabel⟩ :=
          exists_incoming_same_label_at_full_source hstone tiling edge hedge
            hfull.1 hfull.2.1 hfull.2.2
        have hlt : simplexLabelRank inEdge.boneClass.label inEdge.source < rank := by
          have hlt' := incoming_rank_lt_source_rank inEdge edge htarget hlabel
          rw [hrank] at hlt'
          simpa [hlabel] using hlt'
        obtain ⟨rootEdge, hpath, hcorner⟩ := ih _ hlt inEdge hin rfl
        exact ⟨rootEdge, LiteralEdgePath.snoc hpath hedge htarget hlabel, hcorner⟩

theorem LiteralEdgePath.label_zero_root
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hcorner : first.source = sourceZero (m + 3) ∨
      first.source = sourceOne (m + 3) ∨ first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .zero) :
    first.source = sourceZero (m + 3) := by
  have hfirstLabel := path.label_eq.trans hlabel
  rcases hcorner with hzero | hone | htwo
  · exact hzero
  · have h := edge_from_sourceOne_has_label_one first hone
    rw [hfirstLabel] at h
    contradiction
  · have h := edge_from_sourceTwo_has_label_two first htwo
    rw [hfirstLabel] at h
    contradiction

theorem LiteralEdgePath.label_one_root
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hcorner : first.source = sourceZero (m + 3) ∨
      first.source = sourceOne (m + 3) ∨ first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .one) :
    first.source = sourceOne (m + 3) := by
  have hfirstLabel := path.label_eq.trans hlabel
  rcases hcorner with hzero | hone | htwo
  · have h := edge_from_sourceZero_has_label_zero first hzero
    rw [hfirstLabel] at h
    contradiction
  · exact hone
  · have h := edge_from_sourceTwo_has_label_two first htwo
    rw [hfirstLabel] at h
    contradiction

theorem LiteralEdgePath.label_two_root
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hcorner : first.source = sourceZero (m + 3) ∨
      first.source = sourceOne (m + 3) ∨ first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .two) :
    first.source = sourceTwo (m + 3) := by
  have hfirstLabel := path.label_eq.trans hlabel
  rcases hcorner with hzero | hone | htwo
  · have h := edge_from_sourceZero_has_label_zero first hzero
    rw [hfirstLabel] at h
    contradiction
  · have h := edge_from_sourceOne_has_label_one first hone
    rw [hfirstLabel] at h
    contradiction
  · exact htwo

end BenzelProblem6Kernel

import BenzelProblem6Kernel.CornerSinkExclusion

/-!
# The unique full three-incoming sink
-/

namespace BenzelProblem6Kernel

theorem exists_unique_full_sink
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∃! sink : SimplexPoint (m + 3),
      sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling ∧
      sink.u < m + 3 ∧ sink.v < m + 3 ∧ sink.w < m + 3 ∧
      literalIndegree hstone tiling sink = 3 := by
  obtain ⟨sink, hsink, hsinkUnique⟩ :=
    exists_unique_noOutgoingActiveOwner hstone tiling
  have hnot0 := unique_noOut_owner_not_sourceZero hstone tiling sink hsink hsinkUnique
  have hnot1 := unique_noOut_owner_not_sourceOne hstone tiling sink hsink hsinkUnique
  have hnot2 := unique_noOut_owner_not_sourceTwo hstone tiling sink hsink hsinkUnique
  have htype := noOutgoing_active_owner_sink_type hstone tiling sink hsink.1 hsink.2
  have hfull :
      (sink.u < m + 3 ∧ sink.v < m + 3 ∧ sink.w < m + 3) ∧
        literalIndegree hstone tiling sink = 3 := by
    rcases htype with hcorner | hfull
    · rcases hcorner.1 with h0 | h1 | h2
      · exact (hnot0 h0).elim
      · exact (hnot1 h1).elim
      · exact (hnot2 h2).elim
    · exact hfull
  refine ⟨sink, ⟨hsink.1, hsink.2, hfull.1.1, hfull.1.2.1,
    hfull.1.2.2, hfull.2⟩, ?_⟩
  intro other hother
  exact hsinkUnique other ⟨hother.1, hother.2.1⟩

end BenzelProblem6Kernel

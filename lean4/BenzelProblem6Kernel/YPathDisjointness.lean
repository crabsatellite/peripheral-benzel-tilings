import BenzelProblem6Kernel.LiteralYPaths

/-!
# Pairwise path intersection only at the full sink
-/

namespace BenzelProblem6Kernel

theorem visit_nonSink_has_outgoing_root_label
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (p sink : SimplexPoint (m + 3))
    (hvisit : path.Visits p)
    (hsink : sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (hpNe : p ≠ sink) :
    ∃ outEdge ∈ literalDirectedEdges hstone tiling,
      outEdge.source = p ∧
        outEdge.boneClass.label = first.boneClass.label := by
  rcases hvisit.source_or_incoming with hsource | ⟨inEdge, hinEdge,
      hinLabel, hinTarget⟩
  · exact ⟨first, path.first_mem, hsource.symm, rfl⟩
  · have hpActive : p ∈ activeOwnerFinset hstone tiling := by
      simpa [hinTarget] using edge_target_mem_active hstone tiling inEdge hinEdge
    have hpSource : p ∈ activeOwnerEdgeSourceFinset hstone tiling := by
      by_contra hpNoOut
      have hunique := (exists_unique_noOutgoingActiveOwner hstone tiling).unique
        ⟨hpActive, hpNoOut⟩ hsink
      exact hpNe hunique
    simp only [activeOwnerEdgeSourceFinset, Finset.mem_image] at hpSource
    obtain ⟨outEdge, houtEdge, houtSource⟩ := hpSource
    have hcontinue := incoming_to_full_source_has_outgoing_label hstone tiling
      inEdge outEdge hinEdge houtEdge (hinTarget.trans houtSource.symm)
    exact ⟨outEdge, houtEdge, houtSource,
      hcontinue.symm.trans hinLabel⟩

theorem two_paths_meet_only_at_sink
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {firstA lastA firstB lastB : LiteralDirectedEdge m}
    (pathA : LiteralEdgePath hstone tiling firstA lastA)
    (pathB : LiteralEdgePath hstone tiling firstB lastB)
    (sink : SimplexPoint (m + 3))
    (hsink : sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (hlabels : firstA.boneClass.label ≠ firstB.boneClass.label)
    (p : SimplexPoint (m + 3))
    (hvisitA : pathA.Visits p) (hvisitB : pathB.Visits p) : p = sink := by
  by_contra hpNe
  obtain ⟨outA, houtA, houtASource, houtALabel⟩ :=
    visit_nonSink_has_outgoing_root_label hstone tiling pathA p sink hvisitA hsink hpNe
  obtain ⟨outB, houtB, houtBSource, houtBLabel⟩ :=
    visit_nonSink_has_outgoing_root_label hstone tiling pathB p sink hvisitB hsink hpNe
  have houtEq := edgeSource_injective_on hstone tiling houtA houtB
    (houtASource.trans houtBSource.symm)
  subst outB
  exact hlabels (houtALabel.symm.trans houtBLabel)

theorem LiteralYPaths.zero_one_disjoint
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (paths : LiteralYPaths hstone tiling)
    (p : SimplexPoint (m + 3))
    (hzero : paths.zeroPath.Visits p)
    (hone : paths.onePath.Visits p) : p = paths.sink := by
  have hne : paths.zeroFirst.boneClass.label ≠ paths.oneFirst.boneClass.label := by
    have hz := paths.zeroPath.label_eq.trans paths.zero_label
    have ho := paths.onePath.label_eq.trans paths.one_label
    rw [hz, ho]
    decide
  exact two_paths_meet_only_at_sink hstone tiling paths.zeroPath paths.onePath
    paths.sink ⟨paths.sink_active, paths.sink_no_out⟩ hne p hzero hone

theorem LiteralYPaths.one_two_disjoint
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (paths : LiteralYPaths hstone tiling)
    (p : SimplexPoint (m + 3))
    (hone : paths.onePath.Visits p)
    (htwo : paths.twoPath.Visits p) : p = paths.sink := by
  have hne : paths.oneFirst.boneClass.label ≠ paths.twoFirst.boneClass.label := by
    have ho := paths.onePath.label_eq.trans paths.one_label
    have ht := paths.twoPath.label_eq.trans paths.two_label
    rw [ho, ht]
    decide
  exact two_paths_meet_only_at_sink hstone tiling paths.onePath paths.twoPath
    paths.sink ⟨paths.sink_active, paths.sink_no_out⟩ hne p hone htwo

theorem LiteralYPaths.two_zero_disjoint
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (paths : LiteralYPaths hstone tiling)
    (p : SimplexPoint (m + 3))
    (htwo : paths.twoPath.Visits p)
    (hzero : paths.zeroPath.Visits p) : p = paths.sink := by
  have hne : paths.twoFirst.boneClass.label ≠ paths.zeroFirst.boneClass.label := by
    have ht := paths.twoPath.label_eq.trans paths.two_label
    have hz := paths.zeroPath.label_eq.trans paths.zero_label
    rw [ht, hz]
    decide
  exact two_paths_meet_only_at_sink hstone tiling paths.twoPath paths.zeroPath
    paths.sink ⟨paths.sink_active, paths.sink_no_out⟩ hne p htwo hzero

end BenzelProblem6Kernel

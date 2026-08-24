import BenzelProblem6Kernel.CyclicPathCoordinates

/-!
# Coordinate exclusion of a corner sink
-/

namespace BenzelProblem6Kernel

theorem exists_incoming_at_noOut_present
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (hpNoOut : p ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5) (ownerCell p label)) :
    ∃ edge ∈ literalDirectedEdges hstone tiling,
      edge.target = p ∧ edge.boneClass.label = label := by
  obtain ⟨edge, hedge, hrole⟩ :=
    active_owner_present_label_role hstone tiling p hpActive label hmem
  rcases hrole with hsource | htarget
  · exfalso
    apply hpNoOut
    simp only [activeOwnerEdgeSourceFinset, Finset.mem_image]
    exact ⟨edge, hedge, hsource.1⟩
  · exact ⟨edge, hedge, htarget⟩

theorem visited_pivot_forces_label_contradiction
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last pivot : LiteralDirectedEdge m}
    (path : LiteralEdgePath hstone tiling first last)
    (hpivot : pivot ∈ literalDirectedEdges hstone tiling)
    (hvisit : path.Visits pivot.target)
    (hlabelNe : pivot.boneClass.label ≠ first.boneClass.label)
    (sink : SimplexPoint (m + 3))
    (hsinkUnique : ∀ q, q ∈ activeOwnerFinset hstone tiling ∧
      q ∉ activeOwnerEdgeSourceFinset hstone tiling → q = sink)
    (hpivotNeSink : pivot.target ≠ sink) : False := by
  rcases hvisit.source_or_incoming with hsource | ⟨edgePath, hedgePath,
      hedgePathLabel, hedgePathTarget⟩
  · have hlabels := incoming_to_full_source_has_outgoing_label hstone tiling
      pivot first hpivot path.first_mem hsource
    exact hlabelNe hlabels
  · have hpivotActive := edge_target_mem_active hstone tiling pivot hpivot
    have hpivotSource : pivot.target ∈ activeOwnerEdgeSourceFinset hstone tiling := by
      by_contra hnot
      exact hpivotNeSink (hsinkUnique pivot.target ⟨hpivotActive, hnot⟩)
    simp only [activeOwnerEdgeSourceFinset, Finset.mem_image] at hpivotSource
    obtain ⟨outEdge, houtEdge, houtSource⟩ := hpivotSource
    have hpivotOut := incoming_to_full_source_has_outgoing_label hstone tiling
      pivot outEdge hpivot houtEdge houtSource.symm
    have hpathOut := incoming_to_full_source_has_outgoing_label hstone tiling
      edgePath outEdge hedgePath houtEdge (hedgePathTarget.trans houtSource.symm)
    apply hlabelNe
    exact hpivotOut.trans (hpathOut.symm.trans hedgePathLabel)

theorem unique_noOut_owner_not_sourceZero
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (sink : SimplexPoint (m + 3))
    (hsink : sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (hsinkUnique : ∀ q, q ∈ activeOwnerFinset hstone tiling ∧
      q ∉ activeOwnerEdgeSourceFinset hstone tiling → q = sink) :
    sink ≠ sourceZero (m + 3) := by
  intro hsinkZero
  have hmemOne := (owner_one_mem_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  have hmemTwo := (owner_two_mem_iff (n := m + 5) (by omega)
    (sourceZero (m + 3))).2 (by simp [sourceZero])
  obtain ⟨inOne, hinOne, hinOneTarget, hinOneLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .one (by simpa [hsinkZero] using hmemOne)
  obtain ⟨inTwo, hinTwo, hinTwoTarget, hinTwoLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .two (by simpa [hsinkZero] using hmemTwo)
  obtain ⟨rootOne, pathOne, hcornerOne⟩ :=
    exists_corner_ancestor_path hstone tiling inOne hinOne
  have hrootOne := pathOne.label_one_root hstone tiling hcornerOne hinOneLabel
  obtain ⟨rootTwo, pathTwo, hcornerTwo⟩ :=
    exists_corner_ancestor_path hstone tiling inTwo hinTwo
  have hrootTwo := pathTwo.label_two_root hstone tiling hcornerTwo hinTwoLabel
  have hpathOneEnd : inOne.target = sourceZero (m + 3) :=
    hinOneTarget.trans hsinkZero
  have hpathTwoEnd : inTwo.target = sourceZero (m + 3) :=
    hinTwoTarget.trans hsinkZero
  obtain ⟨pivot, hpivot, hpivotLabel, hpivotA, hpivotU⟩ :=
    pathTwo.exists_labelTwo_last_A_target_u_zero hinTwoLabel
      (by simp [hrootTwo, sourceTwo]) (by simp [hpathTwoEnd, sourceZero])
  have hpivotW : 0 < pivot.target.w := labelTwo_A_target_w_pos pivot hpivotA
  have hb : pivot.target.v ≤ m + 3 := by
    have := pivot.target.sum_eq
    omega
  obtain ⟨visited, hvisit, hvisitU, hvisitV, hvisitW⟩ :=
    labelOne_corner_path_visits_all_vertical pathOne hrootOne hpathOneEnd
      hinOneLabel pivot.target.v hb
  have hvisitedEq : visited = pivot.target := by
    apply simplexPoint_ext
    · omega
    · exact hvisitV
    · have hpivotSum := pivot.target.sum_eq
      omega
  rw [hvisitedEq] at hvisit
  apply visited_pivot_forces_label_contradiction hstone tiling pathOne hpivot
    hvisit (by
      have hfirst := pathOne.label_eq.trans hinOneLabel
      rw [hpivotLabel, hfirst]
      decide) sink hsinkUnique
  intro heq
  rw [heq, hsinkZero] at hpivotW
  simp [sourceZero] at hpivotW

theorem unique_noOut_owner_not_sourceOne
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (sink : SimplexPoint (m + 3))
    (hsink : sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (hsinkUnique : ∀ q, q ∈ activeOwnerFinset hstone tiling ∧
      q ∉ activeOwnerEdgeSourceFinset hstone tiling → q = sink) :
    sink ≠ sourceOne (m + 3) := by
  intro hsinkOne
  have hmemZero := (owner_zero_mem_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  have hmemTwo := (owner_two_mem_iff (n := m + 5) (by omega)
    (sourceOne (m + 3))).2 (by simp [sourceOne])
  obtain ⟨inTwo, hinTwo, hinTwoTarget, hinTwoLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .two (by simpa [hsinkOne] using hmemTwo)
  obtain ⟨inZero, hinZero, hinZeroTarget, hinZeroLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .zero (by simpa [hsinkOne] using hmemZero)
  obtain ⟨rootTwo, pathTwo, hcornerTwo⟩ :=
    exists_corner_ancestor_path hstone tiling inTwo hinTwo
  have hrootTwo := pathTwo.label_two_root hstone tiling hcornerTwo hinTwoLabel
  obtain ⟨rootZero, pathZero, hcornerZero⟩ :=
    exists_corner_ancestor_path hstone tiling inZero hinZero
  have hrootZero := pathZero.label_zero_root hstone tiling hcornerZero hinZeroLabel
  have hpathTwoEnd : inTwo.target = sourceOne (m + 3) :=
    hinTwoTarget.trans hsinkOne
  have hpathZeroEnd : inZero.target = sourceOne (m + 3) :=
    hinZeroTarget.trans hsinkOne
  have hallA := pathTwo.labelTwo_all_steps_A hinTwoLabel
    (by simp [hpathTwoEnd, sourceOne])
  obtain ⟨pivot, hpivot, hpivotLabel, hpivotC, hpivotV⟩ :=
    pathZero.exists_labelZero_last_C_target_v_zero hinZeroLabel
      (by simp [hrootZero, sourceZero]) (by simp [hpathZeroEnd, sourceOne])
  have hpivotU : 0 < pivot.target.u := labelZero_C_target_u_pos pivot hpivotC
  have hb : pivot.target.w ≤ m + 3 := by
    have := pivot.target.sum_eq
    omega
  obtain ⟨visited, hvisit, hvisitV, hvisitW, hvisitU⟩ :=
    allA_path_visits_horizontal_prefix hallA
      (by simp [hrootTwo, sourceTwo]) (by simp [hrootTwo, sourceTwo])
      (by simp [hpathTwoEnd, sourceOne])
      (m + 3) (by simp [hpathTwoEnd, sourceOne]) pivot.target.w hb
  have hvisitedEq : visited = pivot.target := by
    apply simplexPoint_ext
    · have hpivotSum := pivot.target.sum_eq
      omega
    · omega
    · exact hvisitW
  rw [hvisitedEq] at hvisit
  apply visited_pivot_forces_label_contradiction hstone tiling pathTwo hpivot
    hvisit (by
      have hfirst := pathTwo.label_eq.trans hinTwoLabel
      rw [hpivotLabel, hfirst]
      decide) sink hsinkUnique
  intro heq
  rw [heq, hsinkOne] at hpivotU
  simp [sourceOne] at hpivotU

theorem unique_noOut_owner_not_sourceTwo
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (sink : SimplexPoint (m + 3))
    (hsink : sink ∈ activeOwnerFinset hstone tiling ∧
      sink ∉ activeOwnerEdgeSourceFinset hstone tiling)
    (hsinkUnique : ∀ q, q ∈ activeOwnerFinset hstone tiling ∧
      q ∉ activeOwnerEdgeSourceFinset hstone tiling → q = sink) :
    sink ≠ sourceTwo (m + 3) := by
  intro hsinkTwo
  have hmemZero := (owner_zero_mem_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  have hmemOne := (owner_one_mem_iff (n := m + 5) (by omega)
    (sourceTwo (m + 3))).2 (by simp [sourceTwo])
  obtain ⟨inZero, hinZero, hinZeroTarget, hinZeroLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .zero (by simpa [hsinkTwo] using hmemZero)
  obtain ⟨inOne, hinOne, hinOneTarget, hinOneLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2
      .one (by simpa [hsinkTwo] using hmemOne)
  obtain ⟨rootZero, pathZero, hcornerZero⟩ :=
    exists_corner_ancestor_path hstone tiling inZero hinZero
  have hrootZero := pathZero.label_zero_root hstone tiling hcornerZero hinZeroLabel
  obtain ⟨rootOne, pathOne, hcornerOne⟩ :=
    exists_corner_ancestor_path hstone tiling inOne hinOne
  have hrootOne := pathOne.label_one_root hstone tiling hcornerOne hinOneLabel
  have hpathZeroEnd : inZero.target = sourceTwo (m + 3) :=
    hinZeroTarget.trans hsinkTwo
  have hpathOneEnd : inOne.target = sourceTwo (m + 3) :=
    hinOneTarget.trans hsinkTwo
  have hallC := pathZero.labelZero_all_steps_C hinZeroLabel
    (by simp [hpathZeroEnd, sourceTwo])
  obtain ⟨pivot, hpivot, hpivotLabel, hpivotB, hpivotW⟩ :=
    pathOne.exists_labelOne_last_B_target_w_zero hinOneLabel
      (by simp [hrootOne, sourceOne]) (by simp [hpathOneEnd, sourceTwo])
  have hpivotV : 0 < pivot.target.v := labelOne_B_target_v_pos pivot hpivotB
  have hb : pivot.target.u ≤ m + 3 := by
    have := pivot.target.sum_eq
    omega
  obtain ⟨visited, hvisit, hvisitW, hvisitU, hvisitV⟩ :=
    allC_path_visits_diagonal_prefix hallC
      (by simp [hrootZero, sourceZero]) (by simp [hrootZero, sourceZero])
      (by simp [hpathZeroEnd, sourceTwo])
      (m + 3) (by simp [hpathZeroEnd, sourceTwo]) pivot.target.u hb
  have hvisitedEq : visited = pivot.target := by
    apply simplexPoint_ext
    · exact hvisitU
    · have hpivotSum := pivot.target.sum_eq
      omega
    · omega
  rw [hvisitedEq] at hvisit
  apply visited_pivot_forces_label_contradiction hstone tiling pathZero hpivot
    hvisit (by
      have hfirst := pathZero.label_eq.trans hinZeroLabel
      rw [hpivotLabel, hfirst]
      decide) sink hsinkUnique
  intro heq
  rw [heq, hsinkTwo] at hpivotV
  simp [sourceTwo] at hpivotV
end BenzelProblem6Kernel

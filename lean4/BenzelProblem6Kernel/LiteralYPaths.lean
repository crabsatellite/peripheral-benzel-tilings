import BenzelProblem6Kernel.FullSink

/-!
# Three finite labelled paths from the corners to the full sink
-/

namespace BenzelProblem6Kernel

structure LiteralYPaths
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) where
  sink : SimplexPoint (m + 3)
  sink_active : sink ∈ activeOwnerFinset hstone tiling
  sink_no_out : sink ∉ activeOwnerEdgeSourceFinset hstone tiling
  sink_positive : sink.u < m + 3 ∧ sink.v < m + 3 ∧ sink.w < m + 3
  zeroFirst : LiteralDirectedEdge m
  zeroLast : LiteralDirectedEdge m
  oneFirst : LiteralDirectedEdge m
  oneLast : LiteralDirectedEdge m
  twoFirst : LiteralDirectedEdge m
  twoLast : LiteralDirectedEdge m
  zeroPath : LiteralEdgePath hstone tiling zeroFirst zeroLast
  onePath : LiteralEdgePath hstone tiling oneFirst oneLast
  twoPath : LiteralEdgePath hstone tiling twoFirst twoLast
  zero_source : zeroFirst.source = sourceZero (m + 3)
  one_source : oneFirst.source = sourceOne (m + 3)
  two_source : twoFirst.source = sourceTwo (m + 3)
  zero_target : zeroLast.target = sink
  one_target : oneLast.target = sink
  two_target : twoLast.target = sink
  zero_label : zeroLast.boneClass.label = .zero
  one_label : oneLast.boneClass.label = .one
  two_label : twoLast.boneClass.label = .two

theorem nonempty_literalYPathsOfTiling
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Nonempty (LiteralYPaths hstone tiling) := by
  let sink := (exists_unique_full_sink hstone tiling).choose
  have hsink := (exists_unique_full_sink hstone tiling).choose_spec.1
  have hmemZero := (owner_zero_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.2.1
  have hmemOne := (owner_one_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.2.2.1
  have hmemTwo := (owner_two_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.1
  obtain ⟨zeroLast, hzeroLast, hzeroTarget, hzeroLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1
      .zero hmemZero
  obtain ⟨oneLast, honeLast, honeTarget, honeLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1
      .one hmemOne
  obtain ⟨twoLast, htwoLast, htwoTarget, htwoLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1
      .two hmemTwo
  obtain ⟨zeroFirst, zeroPath, hzeroCorner⟩ :=
    exists_corner_ancestor_path hstone tiling zeroLast hzeroLast
  obtain ⟨oneFirst, onePath, honeCorner⟩ :=
    exists_corner_ancestor_path hstone tiling oneLast honeLast
  obtain ⟨twoFirst, twoPath, htwoCorner⟩ :=
    exists_corner_ancestor_path hstone tiling twoLast htwoLast
  exact ⟨
    { sink := sink
      sink_active := hsink.1
      sink_no_out := hsink.2.1
      sink_positive := ⟨hsink.2.2.1, hsink.2.2.2.1, hsink.2.2.2.2.1⟩
      zeroFirst := zeroFirst
      zeroLast := zeroLast
      oneFirst := oneFirst
      oneLast := oneLast
      twoFirst := twoFirst
      twoLast := twoLast
      zeroPath := zeroPath
      onePath := onePath
      twoPath := twoPath
      zero_source := zeroPath.label_zero_root hstone tiling hzeroCorner hzeroLabel
      one_source := onePath.label_one_root hstone tiling honeCorner honeLabel
      two_source := twoPath.label_two_root hstone tiling htwoCorner htwoLabel
      zero_target := hzeroTarget
      one_target := honeTarget
      two_target := htwoTarget
      zero_label := hzeroLabel
      one_label := honeLabel
      two_label := htwoLabel }⟩

end BenzelProblem6Kernel

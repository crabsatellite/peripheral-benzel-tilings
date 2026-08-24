import BenzelProblem6Kernel.LiteralEdgePathData

/-!
# Data-valued three-arm Y carrier
-/

namespace BenzelProblem6Kernel

structure LiteralYPathData
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
  zeroPath : LiteralEdgePathData hstone tiling zeroFirst zeroLast
  onePath : LiteralEdgePathData hstone tiling oneFirst oneLast
  twoPath : LiteralEdgePathData hstone tiling twoFirst twoLast
  zero_source : zeroFirst.source = sourceZero (m + 3)
  one_source : oneFirst.source = sourceOne (m + 3)
  two_source : twoFirst.source = sourceTwo (m + 3)
  zero_target : zeroLast.target = sink
  one_target : oneLast.target = sink
  two_target : twoLast.target = sink
  zero_label : zeroLast.boneClass.label = .zero
  one_label : oneLast.boneClass.label = .one
  two_label : twoLast.boneClass.label = .two

def LiteralYPathData.toPaths
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling) : LiteralYPaths hstone tiling where
  sink := data.sink
  sink_active := data.sink_active
  sink_no_out := data.sink_no_out
  sink_positive := data.sink_positive
  zeroFirst := data.zeroFirst
  zeroLast := data.zeroLast
  oneFirst := data.oneFirst
  oneLast := data.oneLast
  twoFirst := data.twoFirst
  twoLast := data.twoLast
  zeroPath := LiteralEdgePathData.toPath _ _ data.zeroPath
  onePath := LiteralEdgePathData.toPath _ _ data.onePath
  twoPath := LiteralEdgePathData.toPath _ _ data.twoPath
  zero_source := data.zero_source
  one_source := data.one_source
  two_source := data.two_source
  zero_target := data.zero_target
  one_target := data.one_target
  two_target := data.two_target
  zero_label := data.zero_label
  one_label := data.one_label
  two_label := data.two_label

theorem nonempty_literalYPathData
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Nonempty (LiteralYPathData hstone tiling) := by
  let sink := (exists_unique_full_sink hstone tiling).choose
  have hsink := (exists_unique_full_sink hstone tiling).choose_spec.1
  have hmemZero := (owner_zero_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.2.1
  have hmemOne := (owner_one_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.2.2.1
  have hmemTwo := (owner_two_mem_iff (n := m + 5) (by omega) sink).2 hsink.2.2.1
  obtain ⟨zeroLast, hzeroLast, hzeroTarget, hzeroLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1 .zero hmemZero
  obtain ⟨oneLast, honeLast, honeTarget, honeLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1 .one hmemOne
  obtain ⟨twoLast, htwoLast, htwoTarget, htwoLabel⟩ :=
    exists_incoming_at_noOut_present hstone tiling sink hsink.1 hsink.2.1 .two hmemTwo
  obtain ⟨zeroFirst, ⟨zeroData⟩, hzeroCorner⟩ :=
    nonempty_corner_ancestor_pathData hstone tiling zeroLast hzeroLast
  obtain ⟨oneFirst, ⟨oneData⟩, honeCorner⟩ :=
    nonempty_corner_ancestor_pathData hstone tiling oneLast honeLast
  obtain ⟨twoFirst, ⟨twoData⟩, htwoCorner⟩ :=
    nonempty_corner_ancestor_pathData hstone tiling twoLast htwoLast
  let zeroPath := LiteralEdgePathData.toPath _ _ zeroData
  let onePath := LiteralEdgePathData.toPath _ _ oneData
  let twoPath := LiteralEdgePathData.toPath _ _ twoData
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
      zeroPath := zeroData
      onePath := oneData
      twoPath := twoData
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

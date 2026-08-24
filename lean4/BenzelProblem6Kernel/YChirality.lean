import BenzelProblem6Kernel.LiteralYPathData

/-!
# The two possible triples of final edge directions
-/

namespace BenzelProblem6Kernel

theorem owner_coordinates_injective {t : ℕ} {p q : SimplexPoint t}
    (hq : ownerQ p = ownerQ q) (hr : ownerR p = ownerR q) : p = q := by
  have hu0 := recover_u_numerator p
  have hu1 := recover_u_numerator q
  have hv0 := recover_v_numerator p
  have hv1 := recover_v_numerator q
  have hw0 := recover_w_numerator p
  have hw1 := recover_w_numerator q
  apply simplexPoint_ext <;> omega

theorem same_target_same_step_same_source {m : ℕ}
    {left right : LiteralDirectedEdge m}
    (htarget : left.target = right.target)
    (hstep : left.boneClass.step = right.boneClass.step) :
    left.source = right.source := by
  have hl := literalDirectedEdge_anchor_step left
  have hr := literalDirectedEdge_anchor_step right
  rw [hstep, htarget] at hl
  have hanchors :
      (ownerQ left.source, ownerR left.source) =
        (ownerQ right.source, ownerR right.source) := by
    have hq := congrArg Prod.fst (hl.trans hr.symm)
    have hs := congrArg Prod.snd (hl.trans hr.symm)
    simp [addCell] at hq hs
    exact Prod.ext hq hs
  exact owner_coordinates_injective (congrArg Prod.fst hanchors)
    (congrArg Prod.snd hanchors)

theorem incoming_distinct_labels_have_distinct_steps
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {left right : LiteralDirectedEdge m}
    (hleft : left ∈ literalDirectedEdges hstone tiling)
    (hright : right ∈ literalDirectedEdges hstone tiling)
    (htarget : left.target = right.target)
    (hlabel : left.boneClass.label ≠ right.boneClass.label) :
    left.boneClass.step ≠ right.boneClass.step := by
  intro hstep
  have hsource := same_target_same_step_same_source htarget hstep
  have hedgeEq := edgeSource_injective_on hstone tiling hleft hright hsource
  exact hlabel (congrArg (fun edge => edge.boneClass.label) hedgeEq)

theorem LiteralYPathData.final_chirality
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling) :
    (data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) ∨
    (data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) := by
  have hzAllowed := literalDirectedEdge_allowed data.zeroLast
  have hoAllowed := literalDirectedEdge_allowed data.oneLast
  have htAllowed := literalDirectedEdge_allowed data.twoLast
  rw [data.zero_label] at hzAllowed
  rw [data.one_label] at hoAllowed
  rw [data.two_label] at htAllowed
  have hzMem := (LiteralEdgePathData.toPath _ _ data.zeroPath).last_mem
  have hoMem := (LiteralEdgePathData.toPath _ _ data.onePath).last_mem
  have htMem := (LiteralEdgePathData.toPath _ _ data.twoPath).last_mem
  have hzoTarget : data.zeroLast.target = data.oneLast.target :=
    data.zero_target.trans data.one_target.symm
  have hotTarget : data.oneLast.target = data.twoLast.target :=
    data.one_target.trans data.two_target.symm
  have hztTarget : data.zeroLast.target = data.twoLast.target :=
    data.zero_target.trans data.two_target.symm
  have hzo := incoming_distinct_labels_have_distinct_steps hstone tiling
    hzMem hoMem hzoTarget (by rw [data.zero_label, data.one_label]; decide)
  have hot := incoming_distinct_labels_have_distinct_steps hstone tiling
    hoMem htMem hotTarget (by rw [data.one_label, data.two_label]; decide)
  have hzt := incoming_distinct_labels_have_distinct_steps hstone tiling
    hzMem htMem hztTarget (by rw [data.zero_label, data.two_label]; decide)
  rcases hzAllowed with hzA | hzC <;>
    rcases hoAllowed with hoB | hoC <;>
    rcases htAllowed with htA | htB
  all_goals simp_all

theorem LiteralYPathData.sink_coordinates_positive
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling) :
    0 < data.sink.u ∧ 0 < data.sink.v ∧ 0 < data.sink.w := by
  rcases data.final_chirality with hpos | hneg
  · have hzAnchor := literalDirectedEdge_anchor_step data.zeroLast
    rw [hpos.1] at hzAnchor
    have hz := stepC_simplex_coordinates data.zeroLast.source
      data.zeroLast.target hzAnchor
    have hoAnchor := literalDirectedEdge_anchor_step data.oneLast
    rw [hpos.2.1] at hoAnchor
    have ho := stepB_simplex_coordinates data.oneLast.source
      data.oneLast.target hoAnchor
    have htAnchor := literalDirectedEdge_anchor_step data.twoLast
    rw [hpos.2.2] at htAnchor
    have ht := stepA_simplex_coordinates data.twoLast.source
      data.twoLast.target htAnchor
    rw [data.zero_target] at hz
    rw [data.one_target] at ho
    rw [data.two_target] at ht
    omega
  · have hzAnchor := literalDirectedEdge_anchor_step data.zeroLast
    rw [hneg.1] at hzAnchor
    have hz := stepA_simplex_coordinates data.zeroLast.source
      data.zeroLast.target hzAnchor
    have hoAnchor := literalDirectedEdge_anchor_step data.oneLast
    rw [hneg.2.1] at hoAnchor
    have ho := stepC_simplex_coordinates data.oneLast.source
      data.oneLast.target hoAnchor
    have htAnchor := literalDirectedEdge_anchor_step data.twoLast
    rw [hneg.2.2] at htAnchor
    have ht := stepB_simplex_coordinates data.twoLast.source
      data.twoLast.target htAnchor
    rw [data.zero_target] at hz
    rw [data.one_target] at ho
    rw [data.two_target] at ht
    omega

end BenzelProblem6Kernel

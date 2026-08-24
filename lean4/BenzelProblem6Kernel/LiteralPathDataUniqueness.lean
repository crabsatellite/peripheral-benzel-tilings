import BenzelProblem6Kernel.PathModelToLiteralTiling

/-!
# Uniqueness of the labelled path word in the deterministic literal graph
-/

namespace BenzelProblem6Kernel

theorem LiteralEdgePathData.last_mem
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    last ∈ literalDirectedEdges hstone tiling := by
  cases path with
  | single hedge => exact hedge
  | snoc _ hnext _ _ => exact hnext

theorem LiteralEdgePathData.first_mem
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    first ∈ literalDirectedEdges hstone tiling := by
  induction path with
  | single hedge => exact hedge
  | snoc _ _ _ _ ih => exact ih

theorem LiteralEdgePathData.start_rank_le
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    simplexLabelRank last.boneClass.label first.source ≤
      simplexLabelRank last.boneClass.label last.source := by
  induction path with
  | single hedge => exact Nat.le_refl _
  | @snoc previous next path hnext hmeet hlabel ih =>
      have ih' := ih
      rw [hlabel] at ih'
      exact ih'.trans (incoming_rank_lt_source_rank previous next hmeet hlabel).le

theorem LiteralEdgePathData.ballotWord_unique
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (left right : LiteralEdgePathData hstone tiling first last) :
    LiteralEdgePathData.ballotWord first last left =
      LiteralEdgePathData.ballotWord first last right := by
  induction left with
  | single hedge =>
      cases right with
      | single => rfl
      | snoc path hnext hmeet hlabel =>
          have hle := LiteralEdgePathData.start_rank_le path
          have hlt := incoming_rank_lt_source_rank _ first hmeet hlabel
          rw [hlabel] at hle
          omega
  | @snoc previous last pathPrefix hlast hmeet hlabel ih =>
      cases right with
      | single =>
          have hle := LiteralEdgePathData.start_rank_le pathPrefix
          have hlt := incoming_rank_lt_source_rank previous first hmeet hlabel
          rw [hlabel] at hle
          omega
      | snoc rightPrefix hlast' hmeet' hlabel' =>
          have hprevious := incoming_same_label_unique hstone tiling last.source
            last.boneClass.label previous _ pathPrefix.last_mem rightPrefix.last_mem
            hmeet hmeet' hlabel hlabel'
          cases hprevious
          simp only [LiteralEdgePathData.ballotWord]
          rw [ih rightPrefix]

theorem LiteralEdgePathData.ballotWord_unique_of_edges_eq
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {leftFirst leftLast rightFirst rightLast : LiteralDirectedEdge m}
    (hfirst : leftFirst = rightFirst) (hlast : leftLast = rightLast)
    (left : LiteralEdgePathData hstone tiling leftFirst leftLast)
    (right : LiteralEdgePathData hstone tiling rightFirst rightLast) :
    LiteralEdgePathData.ballotWord leftFirst leftLast left =
      LiteralEdgePathData.ballotWord rightFirst rightLast right := by
  subst rightFirst
  subst rightLast
  exact LiteralEdgePathData.ballotWord_unique hstone tiling left right

theorem LiteralYPathData.sink_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.sink = right.sink := by
  have hleft := (exists_unique_noOutgoingActiveOwner hstone tiling).choose_spec.2
    left.sink ⟨left.sink_active, left.sink_no_out⟩
  have hright := (exists_unique_noOutgoingActiveOwner hstone tiling).choose_spec.2
    right.sink ⟨right.sink_active, right.sink_no_out⟩
  exact hleft.trans hright.symm

theorem LiteralYPathData.zeroFirst_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.zeroFirst = right.zeroFirst := by
  apply edgeSource_injective_on hstone tiling
    left.zeroPath.first_mem right.zeroPath.first_mem
  exact left.zero_source.trans right.zero_source.symm

theorem LiteralYPathData.oneFirst_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.oneFirst = right.oneFirst := by
  apply edgeSource_injective_on hstone tiling
    left.onePath.first_mem right.onePath.first_mem
  exact left.one_source.trans right.one_source.symm

theorem LiteralYPathData.twoFirst_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.twoFirst = right.twoFirst := by
  apply edgeSource_injective_on hstone tiling
    left.twoPath.first_mem right.twoPath.first_mem
  exact left.two_source.trans right.two_source.symm

theorem LiteralYPathData.zeroLast_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.zeroLast = right.zeroLast := by
  apply incoming_same_label_unique hstone tiling left.sink .zero
    left.zeroLast right.zeroLast left.zeroPath.last_mem right.zeroPath.last_mem
  · exact left.zero_target
  · exact right.zero_target.trans (left.sink_unique right).symm
  · exact left.zero_label
  · exact right.zero_label

theorem LiteralYPathData.oneLast_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.oneLast = right.oneLast := by
  apply incoming_same_label_unique hstone tiling left.sink .one
    left.oneLast right.oneLast left.onePath.last_mem right.onePath.last_mem
  · exact left.one_target
  · exact right.one_target.trans (left.sink_unique right).symm
  · exact left.one_label
  · exact right.one_label

theorem LiteralYPathData.twoLast_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.twoLast = right.twoLast := by
  apply incoming_same_label_unique hstone tiling left.sink .two
    left.twoLast right.twoLast left.twoPath.last_mem right.twoPath.last_mem
  · exact left.two_target
  · exact right.two_target.trans (left.sink_unique right).symm
  · exact left.two_label
  · exact right.two_label

theorem LiteralYPathData.zeroBallotWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    LiteralEdgePathData.ballotWord left.zeroFirst left.zeroLast left.zeroPath =
      LiteralEdgePathData.ballotWord right.zeroFirst right.zeroLast right.zeroPath := by
  exact LiteralEdgePathData.ballotWord_unique_of_edges_eq hstone tiling
    (left.zeroFirst_unique right) (left.zeroLast_unique right)
    left.zeroPath right.zeroPath

theorem LiteralYPathData.oneBallotWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    LiteralEdgePathData.ballotWord left.oneFirst left.oneLast left.onePath =
      LiteralEdgePathData.ballotWord right.oneFirst right.oneLast right.onePath := by
  exact LiteralEdgePathData.ballotWord_unique_of_edges_eq hstone tiling
    (left.oneFirst_unique right) (left.oneLast_unique right)
    left.onePath right.onePath

theorem LiteralYPathData.twoBallotWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    LiteralEdgePathData.ballotWord left.twoFirst left.twoLast left.twoPath =
      LiteralEdgePathData.ballotWord right.twoFirst right.twoLast right.twoPath := by
  exact LiteralEdgePathData.ballotWord_unique_of_edges_eq hstone tiling
    (left.twoFirst_unique right) (left.twoLast_unique right)
    left.twoPath right.twoPath

theorem LiteralYPathData.zeroArmWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.zeroPath.armWord = right.zeroPath.armWord := by
  simp only [LiteralEdgePathData.armWord]
  exact congrArg List.dropLast (left.zeroBallotWord_unique right)

theorem LiteralYPathData.oneArmWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.onePath.armWord = right.onePath.armWord := by
  simp only [LiteralEdgePathData.armWord]
  exact congrArg List.dropLast (left.oneBallotWord_unique right)

theorem LiteralYPathData.twoArmWord_unique
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (left right : LiteralYPathData hstone tiling) :
    left.twoPath.armWord = right.twoPath.armWord := by
  simp only [LiteralEdgePathData.armWord]
  exact congrArg List.dropLast (left.twoBallotWord_unique right)

end BenzelProblem6Kernel

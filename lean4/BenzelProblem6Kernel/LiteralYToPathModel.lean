import BenzelProblem6Kernel.LiteralPathDropLast
import BenzelProblem6Kernel.YChirality
import BenzelProblem6Kernel.PathModelCarrier

/-!
# Forward transport from literal Y data to the counted path-model carrier
-/

namespace BenzelProblem6Kernel

def LiteralYPathData.reducedSink
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling) : SimplexPoint m where
  u := data.sink.u - 1
  v := data.sink.v - 1
  w := data.sink.w - 1
  sum_eq := by
    have hsum := data.sink.sum_eq
    have hpos := data.sink_coordinates_positive
    omega

noncomputable def recursiveOfConcrete {up down : ℕ}
    (word : List BallotMove)
    (hmajor : majorityCount word = up)
    (hminor : minorityCount word = down)
    (hballot : IsBallotSequence word) : RecursiveBallot up down :=
  (recursiveBallotEquivConcrete up down).symm
    { word := word, majority_eq := hmajor, minority_eq := hminor, ballot := hballot }

noncomputable def LiteralYPathData.positiveArmTriple
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) :
    PositiveArmTriple data.reducedSink.u data.reducedSink.v data.reducedSink.w := by
  let x := data.reducedSink.u
  let y := data.reducedSink.v
  let z := data.reducedSink.w
  have hsinkPos := data.sink_coordinates_positive
  have hx : data.sink.u = x + 1 := by simp [x, LiteralYPathData.reducedSink]; omega
  have hy : data.sink.v = y + 1 := by simp [y, LiteralYPathData.reducedSink]; omega
  have hz : data.sink.w = z + 1 := by simp [z, LiteralYPathData.reducedSink]; omega
  have hzeroBallot := data.zeroPath.labelZero_ballot data.zero_label
    (by simp [data.zero_source, sourceZero])
  have honeBallot := data.onePath.labelOne_ballot data.one_label
    (by simp [data.one_source, sourceOne])
  have htwoBallot := data.twoPath.labelTwo_ballot data.two_label
    (by simp [data.two_source, sourceTwo])
  have hzeroMinor := data.zeroPath.labelZero_minorityCount data.zero_label
    (by simp [data.zero_source, sourceZero])
  have honeMinor := data.onePath.labelOne_minorityCount data.one_label
    (by simp [data.one_source, sourceOne])
  have htwoMinor := data.twoPath.labelTwo_minorityCount data.two_label
    (by simp [data.two_source, sourceTwo])
  rw [data.zero_target, hz] at hzeroMinor
  rw [data.one_target, hx] at honeMinor
  rw [data.two_target, hy] at htwoMinor
  rw [data.zero_target, hx] at hzeroBallot
  rw [data.one_target, hy] at honeBallot
  rw [data.two_target, hz] at htwoBallot
  have hzeroFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.zeroFirst data.zeroLast data.zeroPath) =
        x + z + 2 := by
    have hle := hzeroBallot.1.count_le
    omega
  have honeFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.oneFirst data.oneLast data.onePath) =
        x + y + 2 := by
    have hle := honeBallot.1.count_le
    omega
  have htwoFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.twoFirst data.twoLast data.twoPath) =
        y + z + 2 := by
    have hle := htwoBallot.1.count_le
    omega
  have hzMove : data.zeroLast.boneClass.ballotMove = .majority :=
    goodBoneClass_ballotMove_majority_iff data.zeroLast.boneClass |>.2
      (Or.inl ⟨data.zero_label, hpos.1⟩)
  have hoMove : data.oneLast.boneClass.ballotMove = .majority :=
    goodBoneClass_ballotMove_majority_iff data.oneLast.boneClass |>.2
      (Or.inr (Or.inl ⟨data.one_label, hpos.2.1⟩))
  have htMove : data.twoLast.boneClass.ballotMove = .majority :=
    goodBoneClass_ballotMove_majority_iff data.twoLast.boneClass |>.2
      (Or.inr (Or.inr ⟨data.two_label, hpos.2.2⟩))
  have hzCounts := data.zeroPath.armWord_counts_of_last_majority hzMove
  have hoCounts := data.onePath.armWord_counts_of_last_majority hoMove
  have htCounts := data.twoPath.armWord_counts_of_last_majority htMove
  have hzValid := data.zeroPath.armWord_isBallot hzeroBallot.1
  have hoValid := data.onePath.armWord_isBallot honeBallot.1
  have htValid := data.twoPath.armWord_isBallot htwoBallot.1
  exact
    (recursiveOfConcrete data.zeroPath.armWord (by omega) (by omega) hzValid,
      recursiveOfConcrete data.onePath.armWord (by omega) (by omega) hoValid,
      recursiveOfConcrete data.twoPath.armWord (by omega) (by omega) htValid)

noncomputable def LiteralYPathData.negativeArmTriple
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hneg : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) :
    NegativeArmTriple data.reducedSink.u data.reducedSink.v data.reducedSink.w := by
  let x := data.reducedSink.u
  let y := data.reducedSink.v
  let z := data.reducedSink.w
  have hsinkPos := data.sink_coordinates_positive
  have hx : data.sink.u = x + 1 := by simp [x, LiteralYPathData.reducedSink]; omega
  have hy : data.sink.v = y + 1 := by simp [y, LiteralYPathData.reducedSink]; omega
  have hz : data.sink.w = z + 1 := by simp [z, LiteralYPathData.reducedSink]; omega
  have hzeroBallot := data.zeroPath.labelZero_ballot data.zero_label
    (by simp [data.zero_source, sourceZero])
  have honeBallot := data.onePath.labelOne_ballot data.one_label
    (by simp [data.one_source, sourceOne])
  have htwoBallot := data.twoPath.labelTwo_ballot data.two_label
    (by simp [data.two_source, sourceTwo])
  have hzeroMinor := data.zeroPath.labelZero_minorityCount data.zero_label
    (by simp [data.zero_source, sourceZero])
  have honeMinor := data.onePath.labelOne_minorityCount data.one_label
    (by simp [data.one_source, sourceOne])
  have htwoMinor := data.twoPath.labelTwo_minorityCount data.two_label
    (by simp [data.two_source, sourceTwo])
  rw [data.zero_target, hz] at hzeroMinor
  rw [data.one_target, hx] at honeMinor
  rw [data.two_target, hy] at htwoMinor
  rw [data.zero_target, hx] at hzeroBallot
  rw [data.one_target, hy] at honeBallot
  rw [data.two_target, hz] at htwoBallot
  have hzeroFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.zeroFirst data.zeroLast data.zeroPath) =
        x + z + 2 := by have hle := hzeroBallot.1.count_le; omega
  have honeFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.oneFirst data.oneLast data.onePath) =
        x + y + 2 := by have hle := honeBallot.1.count_le; omega
  have htwoFullMajor : majorityCount
      (LiteralEdgePathData.ballotWord data.twoFirst data.twoLast data.twoPath) =
        y + z + 2 := by have hle := htwoBallot.1.count_le; omega
  have hzMove : data.zeroLast.boneClass.ballotMove = .minority :=
    goodBoneClass_ballotMove_minority_iff data.zeroLast.boneClass |>.2
      (Or.inl ⟨data.zero_label, hneg.1⟩)
  have hoMove : data.oneLast.boneClass.ballotMove = .minority :=
    goodBoneClass_ballotMove_minority_iff data.oneLast.boneClass |>.2
      (Or.inr (Or.inl ⟨data.one_label, hneg.2.1⟩))
  have htMove : data.twoLast.boneClass.ballotMove = .minority :=
    goodBoneClass_ballotMove_minority_iff data.twoLast.boneClass |>.2
      (Or.inr (Or.inr ⟨data.two_label, hneg.2.2⟩))
  have hzCounts := data.zeroPath.armWord_counts_of_last_minority hzMove
  have hoCounts := data.onePath.armWord_counts_of_last_minority hoMove
  have htCounts := data.twoPath.armWord_counts_of_last_minority htMove
  have hzValid := data.zeroPath.armWord_isBallot hzeroBallot.1
  have hoValid := data.onePath.armWord_isBallot honeBallot.1
  have htValid := data.twoPath.armWord_isBallot htwoBallot.1
  exact
    (recursiveOfConcrete data.zeroPath.armWord (by omega) (by omega) hzValid,
      recursiveOfConcrete data.onePath.armWord (by omega) (by omega) hoValid,
      recursiveOfConcrete data.twoPath.armWord (by omega) (by omega) htValid)

noncomputable def LiteralYPathData.toPathModelConfiguration
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling) : PathModelConfiguration m := by
  classical
  let positive : Prop :=
    data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA
  by_cases hpos : positive
  · exact ⟨data.reducedSink, Sum.inl (data.positiveArmTriple hpos)⟩
  · have hneg :
        data.zeroLast.boneClass.step = stepA ∧
          data.oneLast.boneClass.step = stepC ∧
          data.twoLast.boneClass.step = stepB :=
      data.final_chirality.resolve_left hpos
    exact ⟨data.reducedSink, Sum.inr (data.negativeArmTriple hneg)⟩

noncomputable def literalTilingToPathModel
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : PathModelConfiguration m :=
  (Classical.choice (nonempty_literalYPathData hstone tiling)).toPathModelConfiguration

end BenzelProblem6Kernel

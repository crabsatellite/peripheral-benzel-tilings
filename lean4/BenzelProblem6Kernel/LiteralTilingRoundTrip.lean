import BenzelProblem6Kernel.PositiveSourceReconstruction
import BenzelProblem6Kernel.NegativeSourceReconstruction

/-!
# Literal reconstruction is a left inverse of forward extraction
-/

namespace BenzelProblem6Kernel

theorem positivePathModel_reconstructs_source
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (sink : SimplexPoint m) (tiling : LiteralTiling m)
    (arms : PositiveArmTriple sink.u sink.v sink.w)
    (data : LiteralYPathData hstone tiling)
    (hsinkU : data.sink.u = sink.u + 1)
    (hsinkV : data.sink.v = sink.v + 1)
    (hsinkW : data.sink.w = sink.w + 1)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    pathModelToLiteralTiling
      (⟨sink, Sum.inl arms⟩ : PathModelConfiguration m) = tiling := by
  rcases sink with ⟨x, y, z, hsum⟩
  change x + y + z = m at hsum
  subst m
  simp at hsinkU hsinkV hsinkW
  have hsink : data.sink = sinkPoint x y z := by
    apply simplexPoint_ext
    · simpa [sinkPoint] using hsinkU
    · simpa [sinkPoint] using hsinkV
    · simpa [sinkPoint] using hsinkW
  unfold pathModelToLiteralTiling
  dsimp only
  exact positiveYLiteralTiling_eq_source hstone x y z tiling arms data
    hsink hpos hzeroWord honeWord htwoWord

theorem negativePathModel_reconstructs_source
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (sink : SimplexPoint m) (tiling : LiteralTiling m)
    (arms : NegativeArmTriple sink.u sink.v sink.w)
    (data : LiteralYPathData hstone tiling)
    (hsinkU : data.sink.u = sink.u + 1)
    (hsinkV : data.sink.v = sink.v + 1)
    (hsinkW : data.sink.w = sink.w + 1)
    (hneg : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    pathModelToLiteralTiling
      (⟨sink, Sum.inr arms⟩ : PathModelConfiguration m) = tiling := by
  rcases sink with ⟨x, y, z, hsum⟩
  change x + y + z = m at hsum
  subst m
  simp at hsinkU hsinkV hsinkW
  have hsink : data.sink = sinkPoint x y z := by
    apply simplexPoint_ext
    · simpa [sinkPoint] using hsinkU
    · simpa [sinkPoint] using hsinkV
    · simpa [sinkPoint] using hsinkW
  unfold pathModelToLiteralTiling
  dsimp only
  exact negativeYLiteralTiling_eq_source hstone x y z tiling arms data
    hsink hneg hzeroWord honeWord htwoWord

theorem pathModelToLiteralTiling_data_roundTrip
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (data : LiteralYPathData hstone tiling) :
    pathModelToLiteralTiling data.toPathModelConfiguration = tiling := by
  have hpositive := data.sink_coordinates_positive
  have hsinkU : data.sink.u = data.reducedSink.u + 1 := by
    simp [LiteralYPathData.reducedSink]
    omega
  have hsinkV : data.sink.v = data.reducedSink.v + 1 := by
    simp [LiteralYPathData.reducedSink]
    omega
  have hsinkW : data.sink.w = data.reducedSink.w + 1 := by
    simp [LiteralYPathData.reducedSink]
    omega
  unfold LiteralYPathData.toPathModelConfiguration
  dsimp only
  split
  · rename_i hpos
    exact positivePathModel_reconstructs_source hstone data.reducedSink tiling
      (data.positiveArmTriple hpos) data hsinkU hsinkV hsinkW hpos
      (data.positiveArmTriple_zero_word hpos)
      (data.positiveArmTriple_one_word hpos)
      (data.positiveArmTriple_two_word hpos)
  · rename_i hnotPositive
    have hneg : data.zeroLast.boneClass.step = stepA ∧
        data.oneLast.boneClass.step = stepC ∧
        data.twoLast.boneClass.step = stepB :=
      data.final_chirality.resolve_left hnotPositive
    exact negativePathModel_reconstructs_source hstone data.reducedSink tiling
      (data.negativeArmTriple hneg) data hsinkU hsinkV hsinkW hneg
      (data.negativeArmTriple_zero_word hneg)
      (data.negativeArmTriple_one_word hneg)
      (data.negativeArmTriple_two_word hneg)

theorem pathModelToLiteralTiling_literalTilingToPathModel
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    pathModelToLiteralTiling (literalTilingToPathModel hstone tiling) =
      tiling := by
  unfold literalTilingToPathModel
  exact pathModelToLiteralTiling_data_roundTrip hstone tiling
    (Classical.choice (nonempty_literalYPathData hstone tiling))

end BenzelProblem6Kernel

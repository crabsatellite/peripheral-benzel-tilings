import BenzelProblem6Kernel.PositiveReconstructedPaths

/-!
# Forward extraction recovers positive-chirality reconstructed path data
-/

namespace BenzelProblem6Kernel

theorem recursiveOfConcrete_word {up down : ℕ}
    (word : List BallotMove)
    (hmajor : majorityCount word = up)
    (hminor : minorityCount word = down)
    (hballot : IsBallotSequence word) :
    recursiveBallotWord (recursiveOfConcrete word hmajor hminor hballot) =
      word := by
  unfold recursiveOfConcrete
  exact concreteToRecursiveBallot_word
    { word := word
      majority_eq := hmajor
      minority_eq := hminor
      ballot := hballot }

theorem LiteralYPathData.positiveArmTriple_zero_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) :
    recursiveBallotWord (data.positiveArmTriple hpos).1 =
      data.zeroPath.armWord := by
  simp only [LiteralYPathData.positiveArmTriple]
  apply recursiveOfConcrete_word

theorem LiteralYPathData.positiveArmTriple_one_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) :
    recursiveBallotWord (data.positiveArmTriple hpos).2.1 =
      data.onePath.armWord := by
  simp only [LiteralYPathData.positiveArmTriple]
  apply recursiveOfConcrete_word

theorem LiteralYPathData.positiveArmTriple_two_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) :
    recursiveBallotWord (data.positiveArmTriple hpos).2.2 =
      data.twoPath.armWord := by
  simp only [LiteralYPathData.positiveArmTriple]
  apply recursiveOfConcrete_word

theorem positiveReconstructedData_sink
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.sink = sinkPoint x y z := by
  obtain ⟨witness, hspec⟩ :=
    exists_positiveLiteralYPathData hstone x y z arms
  exact (data.sink_unique witness).trans hspec.1

theorem positiveReconstructedData_zeroArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.zeroPath.armWord = recursiveBallotWord arms.1 := by
  obtain ⟨witness, hspec⟩ :=
    exists_positiveLiteralYPathData hstone x y z arms
  have hfull := data.zeroBallotWord_unique witness
  rw [hspec.2.2.2.2.1] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem positiveReconstructedData_oneArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.onePath.armWord = recursiveBallotWord arms.2.1 := by
  obtain ⟨witness, hspec⟩ :=
    exists_positiveLiteralYPathData hstone x y z arms
  have hfull := data.oneBallotWord_unique witness
  rw [hspec.2.2.2.2.2.1] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem positiveReconstructedData_twoArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.twoPath.armWord = recursiveBallotWord arms.2.2 := by
  obtain ⟨witness, hspec⟩ :=
    exists_positiveLiteralYPathData hstone x y z arms
  have hfull := data.twoBallotWord_unique witness
  rw [hspec.2.2.2.2.2.2] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem positiveReconstructedData_chirality
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA := by
  obtain ⟨witness, hspec⟩ :=
    exists_positiveLiteralYPathData hstone x y z arms
  have hz := data.zeroLast_unique witness
  have ho := data.oneLast_unique witness
  have ht := data.twoLast_unique witness
  rw [hz, ho, ht]
  exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩

def reducedXYZSink (x y z : ℕ) : SimplexPoint (x + y + z) where
  u := x
  v := y
  w := z
  sum_eq := by omega

theorem positiveChoice_heq_of_indices
    {x y z x' y' z' : ℕ}
    (hx : x = x') (hy : y = y') (hz : z = z')
    {left : PositiveArmTriple x y z}
    {right : PositiveArmTriple x' y' z'}
    (harms : HEq left right) :
    HEq (Sum.inl left : FixedSinkArmChoice x y z)
      (Sum.inl right : FixedSinkArmChoice x' y' z') := by
  subst x'
  subst y'
  subst z'
  exact heq_of_eq (congrArg Sum.inl (eq_of_heq harms))

theorem positiveReconstructedData_reducedSink
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.reducedSink = reducedXYZSink x y z := by
  have hsink := positiveReconstructedData_sink hstone x y z arms data
  apply simplexPoint_ext <;>
    simp [LiteralYPathData.reducedSink, reducedXYZSink] <;>
    have hu := congrArg SimplexPoint.u hsink <;>
    have hv := congrArg SimplexPoint.v hsink <;>
    have hw := congrArg SimplexPoint.w hsink <;>
    simp [sinkPoint] at hu hv hw <;> omega

theorem positiveReconstructedData_arms
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms))
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA) :
    HEq (data.positiveArmTriple hpos) arms := by
  have hred := positiveReconstructedData_reducedSink hstone x y z arms data
  have hx := congrArg SimplexPoint.u hred
  have hy := congrArg SimplexPoint.v hred
  have hz := congrArg SimplexPoint.w hred
  simp [reducedXYZSink] at hx hy hz
  have recursive_heq {up down up' down' : ℕ}
      (hup : up = up') (hdown : down = down')
      (left : RecursiveBallot up down) (right : RecursiveBallot up' down')
      (hword : recursiveBallotWord left = recursiveBallotWord right) :
      HEq left right := by
    let recast := recastRecursiveBallot hup hdown right
    have heq : left = recast := by
      apply recursiveBallotWord_injective
      rw [recursiveBallotWord_recast]
      exact hword
    have hcast : HEq recast right := by
      unfold recast recastRecursiveBallot
      exact cast_heq _ _
    exact (heq_of_eq heq).trans hcast
  have prod_heq {α α' β β' : Type}
      {left₀ : α} {right₀ : α'} {left₁ : β} {right₁ : β'}
      (h₀ : HEq left₀ right₀) (h₁ : HEq left₁ right₁) :
      HEq (left₀, left₁) (right₀, right₁) := by
    cases h₀
    cases h₁
    rfl
  have hzero : HEq (data.positiveArmTriple hpos).1 arms.1 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.positiveArmTriple_zero_word hpos,
      positiveReconstructedData_zeroArmWord hstone x y z arms data]
  have hone : HEq (data.positiveArmTriple hpos).2.1 arms.2.1 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.positiveArmTriple_one_word hpos,
      positiveReconstructedData_oneArmWord hstone x y z arms data]
  have htwo : HEq (data.positiveArmTriple hpos).2.2 arms.2.2 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.positiveArmTriple_two_word hpos,
      positiveReconstructedData_twoArmWord hstone x y z arms data]
  exact prod_heq hzero (prod_heq hone htwo)

theorem positiveReconstructedData_toPathModel
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms)) :
    data.toPathModelConfiguration =
      ⟨reducedXYZSink x y z, Sum.inl arms⟩ := by
  have hpos := positiveReconstructedData_chirality hstone x y z arms data
  have hred := positiveReconstructedData_reducedSink hstone x y z arms data
  have harms := positiveReconstructedData_arms hstone x y z arms data hpos
  have hx := congrArg SimplexPoint.u hred
  have hy := congrArg SimplexPoint.v hred
  have hz := congrArg SimplexPoint.w hred
  simp [reducedXYZSink] at hx hy hz
  have hsum := positiveChoice_heq_of_indices hx hy hz harms
  unfold LiteralYPathData.toPathModelConfiguration
  dsimp only
  split
  · rename_i hpositive
    have hproof : hpositive = hpos := Subsingleton.elim _ _
    subst hpositive
    exact Sigma.ext hred hsum
  · rename_i hnegative
    exact (hnegative hpos).elim

theorem literalTilingToPathModel_positive_roundTrip
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    literalTilingToPathModel hstone (positiveYLiteralTiling x y z arms) =
      ⟨reducedXYZSink x y z, Sum.inl arms⟩ := by
  unfold literalTilingToPathModel
  exact positiveReconstructedData_toPathModel hstone x y z arms
    (Classical.choice
      (nonempty_literalYPathData hstone (positiveYLiteralTiling x y z arms)))

end BenzelProblem6Kernel

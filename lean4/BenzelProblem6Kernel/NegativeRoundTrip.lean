import BenzelProblem6Kernel.PositiveRoundTrip
import BenzelProblem6Kernel.NegativeReconstructedPaths

/-!
# Forward extraction recovers negative-chirality reconstructed path data
-/

namespace BenzelProblem6Kernel

theorem LiteralYPathData.negativeArmTriple_zero_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) :
    recursiveBallotWord (data.negativeArmTriple hpos).1 =
      data.zeroPath.armWord := by
  simp only [LiteralYPathData.negativeArmTriple]
  apply recursiveOfConcrete_word

theorem LiteralYPathData.negativeArmTriple_one_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) :
    recursiveBallotWord (data.negativeArmTriple hpos).2.1 =
      data.onePath.armWord := by
  simp only [LiteralYPathData.negativeArmTriple]
  apply recursiveOfConcrete_word

theorem LiteralYPathData.negativeArmTriple_two_word
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) :
    recursiveBallotWord (data.negativeArmTriple hpos).2.2 =
      data.twoPath.armWord := by
  simp only [LiteralYPathData.negativeArmTriple]
  apply recursiveOfConcrete_word

theorem negativeReconstructedData_sink
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.sink = sinkPoint x y z := by
  obtain ⟨witness, hspec⟩ :=
    exists_negativeLiteralYPathData hstone x y z arms
  exact (data.sink_unique witness).trans hspec.1

theorem negativeReconstructedData_zeroArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.zeroPath.armWord = recursiveBallotWord arms.1 := by
  obtain ⟨witness, hspec⟩ :=
    exists_negativeLiteralYPathData hstone x y z arms
  have hfull := data.zeroBallotWord_unique witness
  rw [hspec.2.2.2.2.1] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem negativeReconstructedData_oneArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.onePath.armWord = recursiveBallotWord arms.2.1 := by
  obtain ⟨witness, hspec⟩ :=
    exists_negativeLiteralYPathData hstone x y z arms
  have hfull := data.oneBallotWord_unique witness
  rw [hspec.2.2.2.2.2.1] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem negativeReconstructedData_twoArmWord
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.twoPath.armWord = recursiveBallotWord arms.2.2 := by
  obtain ⟨witness, hspec⟩ :=
    exists_negativeLiteralYPathData hstone x y z arms
  have hfull := data.twoBallotWord_unique witness
  rw [hspec.2.2.2.2.2.2] at hfull
  simpa [LiteralEdgePathData.armWord] using congrArg List.dropLast hfull

theorem negativeReconstructedData_chirality
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB := by
  obtain ⟨witness, hspec⟩ :=
    exists_negativeLiteralYPathData hstone x y z arms
  have hz := data.zeroLast_unique witness
  have ho := data.oneLast_unique witness
  have ht := data.twoLast_unique witness
  rw [hz, ho, ht]
  exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩

theorem negativeChoice_heq_of_indices
    {x y z x' y' z' : ℕ}
    (hx : x = x') (hy : y = y') (hz : z = z')
    {left : NegativeArmTriple x y z}
    {right : NegativeArmTriple x' y' z'}
    (harms : HEq left right) :
    HEq (Sum.inr left : FixedSinkArmChoice x y z)
      (Sum.inr right : FixedSinkArmChoice x' y' z') := by
  subst x'
  subst y'
  subst z'
  exact heq_of_eq (congrArg Sum.inr (eq_of_heq harms))

theorem negativeReconstructedData_reducedSink
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.reducedSink = reducedXYZSink x y z := by
  have hsink := negativeReconstructedData_sink hstone x y z arms data
  apply simplexPoint_ext <;>
    simp [LiteralYPathData.reducedSink, reducedXYZSink] <;>
    have hu := congrArg SimplexPoint.u hsink <;>
    have hv := congrArg SimplexPoint.v hsink <;>
    have hw := congrArg SimplexPoint.w hsink <;>
    simp [sinkPoint] at hu hv hw <;> omega

theorem negativeReconstructedData_arms
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms))
    (hpos : data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB) :
    HEq (data.negativeArmTriple hpos) arms := by
  have hred := negativeReconstructedData_reducedSink hstone x y z arms data
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
  have hzero : HEq (data.negativeArmTriple hpos).1 arms.1 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.negativeArmTriple_zero_word hpos,
      negativeReconstructedData_zeroArmWord hstone x y z arms data]
  have hone : HEq (data.negativeArmTriple hpos).2.1 arms.2.1 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.negativeArmTriple_one_word hpos,
      negativeReconstructedData_oneArmWord hstone x y z arms data]
  have htwo : HEq (data.negativeArmTriple hpos).2.2 arms.2.2 := by
    apply recursive_heq (by omega) (by omega)
    rw [data.negativeArmTriple_two_word hpos,
      negativeReconstructedData_twoArmWord hstone x y z arms data]
  exact prod_heq hzero (prod_heq hone htwo)

theorem negativeReconstructedData_toPathModel
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms)) :
    data.toPathModelConfiguration =
      ⟨reducedXYZSink x y z, Sum.inr arms⟩ := by
  have hpos := negativeReconstructedData_chirality hstone x y z arms data
  have hred := negativeReconstructedData_reducedSink hstone x y z arms data
  have harms := negativeReconstructedData_arms hstone x y z arms data hpos
  have hx := congrArg SimplexPoint.u hred
  have hy := congrArg SimplexPoint.v hred
  have hz := congrArg SimplexPoint.w hred
  simp [reducedXYZSink] at hx hy hz
  have hsum := negativeChoice_heq_of_indices hx hy hz harms
  unfold LiteralYPathData.toPathModelConfiguration
  dsimp only
  split
  · rename_i hpositive
    have hfalse : stepA = stepC := hpos.1.symm.trans hpositive.1
    exact (by decide : stepA ≠ stepC) hfalse |>.elim
  · rename_i hnotPositive
    have hnegative : data.zeroLast.boneClass.step = stepA ∧
        data.oneLast.boneClass.step = stepC ∧
        data.twoLast.boneClass.step = stepB :=
      data.final_chirality.resolve_left hnotPositive
    have hproof : hnegative = hpos := Subsingleton.elim _ _
    subst hnegative
    exact Sigma.ext hred hsum

theorem literalTilingToPathModel_negative_roundTrip
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    literalTilingToPathModel hstone (negativeYLiteralTiling x y z arms) =
      ⟨reducedXYZSink x y z, Sum.inr arms⟩ := by
  unfold literalTilingToPathModel
  exact negativeReconstructedData_toPathModel hstone x y z arms
    (Classical.choice
      (nonempty_literalYPathData hstone (negativeYLiteralTiling x y z arms)))

end BenzelProblem6Kernel

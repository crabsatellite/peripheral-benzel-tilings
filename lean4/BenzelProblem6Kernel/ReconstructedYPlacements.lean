import BenzelProblem6Kernel.ReverseStoneCoverage

/-!
# The finite reconstructed placement family of a path-model configuration
-/

namespace BenzelProblem6Kernel

noncomputable def positiveYBonePlacements (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    List (LiteralPlacement (x + y + z)) :=
  labelZeroWordBonePlacements (m := x + y + z) arms.1 (by omega) (by omega) ++
    [positiveLabelZeroTerminalBone x y z arms.1] ++
  labelOneWordBonePlacements (m := x + y + z) arms.2.1 (by omega) (by omega) ++
    [positiveLabelOneTerminalBone x y z arms.2.1] ++
  labelTwoWordBonePlacements (m := x + y + z) arms.2.2 (by omega) (by omega) ++
    [positiveLabelTwoTerminalBone x y z arms.2.2]

noncomputable def negativeYBonePlacements (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    List (LiteralPlacement (x + y + z)) :=
  labelZeroWordBonePlacements (m := x + y + z) arms.1 (by omega) (by omega) ++
    [negativeLabelZeroTerminalBone x y z arms.1] ++
  labelOneWordBonePlacements (m := x + y + z) arms.2.1 (by omega) (by omega) ++
    [negativeLabelOneTerminalBone x y z arms.2.1] ++
  labelTwoWordBonePlacements (m := x + y + z) arms.2.2 (by omega) (by omega) ++
    [negativeLabelTwoTerminalBone x y z arms.2.2]

@[simp] theorem positiveYBonePlacements_length (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYBonePlacements x y z arms).length =
      3 * (x + y + z + 3) := by
  simp [positiveYBonePlacements]
  omega

@[simp] theorem negativeYBonePlacements_length (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYBonePlacements x y z arms).length =
      3 * (x + y + z + 3) := by
  simp [negativeYBonePlacements]
  omega

def simplexPointToInt {t : ℕ} (point : SimplexPoint t) : IntSimplex :=
  ⟨point.u, point.v, point.w⟩

@[simp] theorem simplexPointToInt_u {t : ℕ} (point : SimplexPoint t) :
    (simplexPointToInt point).u = point.u := rfl

@[simp] theorem simplexPointToInt_v {t : ℕ} (point : SimplexPoint t) :
    (simplexPointToInt point).v = point.v := rfl

@[simp] theorem simplexPointToInt_w {t : ℕ} (point : SimplexPoint t) :
    (simplexPointToInt point).w = point.w := rfl

def PositiveYArmOwner (x y z : ℕ) (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) : Prop :=
  PositiveLabelZeroPoint x y z arms.1 (simplexPointToInt point) ∨
    PositiveLabelOnePoint x y z arms.2.1 (simplexPointToInt point) ∨
    PositiveLabelTwoPoint x y z arms.2.2 (simplexPointToInt point)

def NegativeYArmOwner (x y z : ℕ) (arms : NegativeArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) : Prop :=
  NegativeLabelZeroPoint x y z arms.1 (simplexPointToInt point) ∨
    NegativeLabelOnePoint x y z arms.2.1 (simplexPointToInt point) ∨
    NegativeLabelTwoPoint x y z arms.2.2 (simplexPointToInt point)

def IsFullSimplexOwner {t : ℕ} (point : SimplexPoint t) : Prop :=
  point.u < t ∧ point.v < t ∧ point.w < t

noncomputable def positiveYStoneOwners (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    Finset (SimplexPoint (x + y + z + 3)) := by
  classical
  exact Finset.univ.filter fun point =>
    IsFullSimplexOwner point ∧ ¬PositiveYArmOwner x y z arms point

noncomputable def negativeYStoneOwners (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    Finset (SimplexPoint (x + y + z + 3)) := by
  classical
  exact Finset.univ.filter fun point =>
    IsFullSimplexOwner point ∧ ¬NegativeYArmOwner x y z arms point

theorem positiveYStoneOwners_full (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (owner : SimplexPoint (x + y + z + 3))
    (hmem : owner ∈ positiveYStoneOwners x y z arms) :
    IsFullSimplexOwner owner := by
  classical
  have h := hmem
  simp [positiveYStoneOwners] at h
  exact h.1

theorem negativeYStoneOwners_full (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (owner : SimplexPoint (x + y + z + 3))
    (hmem : owner ∈ negativeYStoneOwners x y z arms) :
    IsFullSimplexOwner owner := by
  classical
  have h := hmem
  simp [negativeYStoneOwners] at h
  exact h.1

noncomputable def positiveYStonePlacements (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    Finset (LiteralPlacement (x + y + z)) :=
  (positiveYStoneOwners x y z arms).attach.image fun owner =>
    reverseStonePlacement owner.1
      (positiveYStoneOwners_full x y z arms owner.1 owner.2).1
      (positiveYStoneOwners_full x y z arms owner.1 owner.2).2.1
      (positiveYStoneOwners_full x y z arms owner.1 owner.2).2.2

noncomputable def negativeYStonePlacements (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    Finset (LiteralPlacement (x + y + z)) :=
  (negativeYStoneOwners x y z arms).attach.image fun owner =>
    reverseStonePlacement owner.1
      (negativeYStoneOwners_full x y z arms owner.1 owner.2).1
      (negativeYStoneOwners_full x y z arms owner.1 owner.2).2.1
      (negativeYStoneOwners_full x y z arms owner.1 owner.2).2.2

noncomputable def positiveYChosenPlacements (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    Finset (LiteralPlacement (x + y + z)) :=
  (positiveYBonePlacements x y z arms).toFinset ∪
    positiveYStonePlacements x y z arms

noncomputable def negativeYChosenPlacements (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    Finset (LiteralPlacement (x + y + z)) :=
  (negativeYBonePlacements x y z arms).toFinset ∪
    negativeYStonePlacements x y z arms

end BenzelProblem6Kernel

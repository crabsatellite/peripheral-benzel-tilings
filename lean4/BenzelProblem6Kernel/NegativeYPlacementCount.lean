import BenzelProblem6Kernel.NegativeYOwnerCount
import BenzelProblem6Kernel.TilingIncidence

/-!
# Cardinal upper bound for the reconstructed negative placement family
-/

namespace BenzelProblem6Kernel

theorem negativeYStonePlacements_card_le (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYStonePlacements x y z arms).card ≤
      (negativeYStoneOwners x y z arms).card := by
  classical
  rw [negativeYStonePlacements]
  calc
    ((negativeYStoneOwners x y z arms).attach.image fun owner =>
      reverseStonePlacement owner.1
        (negativeYStoneOwners_full x y z arms owner.1 owner.2).1
        (negativeYStoneOwners_full x y z arms owner.1 owner.2).2.1
        (negativeYStoneOwners_full x y z arms owner.1 owner.2).2.2).card ≤
        (negativeYStoneOwners x y z arms).attach.card := Finset.card_image_le
    _ = (negativeYStoneOwners x y z arms).card := Finset.card_attach

theorem negativeYChosen_card_bound (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYChosenPlacements x y z arms).card ≤
      (negativeYBonePlacements x y z arms).length +
        (negativeYStoneOwners x y z arms).card := by
  classical
  calc
    (negativeYChosenPlacements x y z arms).card ≤
        (negativeYBonePlacements x y z arms).toFinset.card +
          (negativeYStonePlacements x y z arms).card := by
      simpa [negativeYChosenPlacements] using
        (Finset.card_union_le
          (s := (negativeYBonePlacements x y z arms).toFinset)
          (t := negativeYStonePlacements x y z arms))
    _ ≤ (negativeYBonePlacements x y z arms).length +
        (negativeYStoneOwners x y z arms).card :=
      Nat.add_le_add (List.toFinset_card_le _)
        (negativeYStonePlacements_card_le x y z arms)

theorem negativeYChosen_card_add_one_le_simplex (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYChosenPlacements x y z arms).card + 1 ≤
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  have hchosen := negativeYChosen_card_bound x y z arms
  have hstone := negativeYStoneOwners_card_bound x y z arms
  rw [negativeYBonePlacements_length] at hchosen
  omega

end BenzelProblem6Kernel

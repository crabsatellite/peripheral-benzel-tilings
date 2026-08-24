import BenzelProblem6Kernel.PositiveYOwnerCount
import BenzelProblem6Kernel.TilingIncidence

/-!
# Cardinal upper bound for the reconstructed positive placement family
-/

namespace BenzelProblem6Kernel

theorem positiveYStonePlacements_card_le (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYStonePlacements x y z arms).card ≤
      (positiveYStoneOwners x y z arms).card := by
  classical
  rw [positiveYStonePlacements]
  calc
    ((positiveYStoneOwners x y z arms).attach.image fun owner =>
      reverseStonePlacement owner.1
        (positiveYStoneOwners_full x y z arms owner.1 owner.2).1
        (positiveYStoneOwners_full x y z arms owner.1 owner.2).2.1
        (positiveYStoneOwners_full x y z arms owner.1 owner.2).2.2).card ≤
        (positiveYStoneOwners x y z arms).attach.card := Finset.card_image_le
    _ = (positiveYStoneOwners x y z arms).card := Finset.card_attach

theorem positiveYChosen_card_bound (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYChosenPlacements x y z arms).card ≤
      (positiveYBonePlacements x y z arms).length +
        (positiveYStoneOwners x y z arms).card := by
  classical
  calc
    (positiveYChosenPlacements x y z arms).card ≤
        (positiveYBonePlacements x y z arms).toFinset.card +
          (positiveYStonePlacements x y z arms).card := by
      simpa [positiveYChosenPlacements] using
        (Finset.card_union_le
          (s := (positiveYBonePlacements x y z arms).toFinset)
          (t := positiveYStonePlacements x y z arms))
    _ ≤ (positiveYBonePlacements x y z arms).length +
        (positiveYStoneOwners x y z arms).card :=
      Nat.add_le_add (List.toFinset_card_le _)
        (positiveYStonePlacements_card_le x y z arms)

theorem positiveYChosen_card_add_one_le_simplex (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYChosenPlacements x y z arms).card + 1 ≤
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  have hchosen := positiveYChosen_card_bound x y z arms
  have hstone := positiveYStoneOwners_card_bound x y z arms
  rw [positiveYBonePlacements_length] at hchosen
  omega

end BenzelProblem6Kernel

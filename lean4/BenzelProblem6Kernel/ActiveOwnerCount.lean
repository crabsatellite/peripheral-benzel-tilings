import BenzelProblem6Kernel.LiteralStoneOwners

/-!
# Count of owners not occupied by an in-phase stone
-/

namespace BenzelProblem6Kernel

noncomputable def activeOwnerFinset
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Finset (SimplexPoint (m + 3)) :=
  Finset.univ \ stoneOwnerFinset hstone tiling

theorem activeOwnerFinset_card
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    (activeOwnerFinset hstone tiling).card = 3 * (m + 3) + 1 := by
  classical
  have hcard :
      (activeOwnerFinset hstone tiling).card =
        Fintype.card (SimplexPoint (m + 3)) -
          (stoneOwnerFinset hstone tiling).card := by
    rw [activeOwnerFinset, Finset.card_sdiff]
    rfl
    exact Finset.subset_univ (stoneOwnerFinset hstone tiling)
  rw [hcard, card_simplexPoint, stoneOwnerFinset_card hstone]
  rw [show m + 3 + 2 = m + 5 by omega, Nat.choose_two_right]
  rw [show m + 5 - 1 = m + 4 by omega]
  have htotalEven : 2 ∣ (m + 5) * (m + 4) := by
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · refine ⟨(2 * k + 5) * (k + 2), ?_⟩
      ring
    · refine ⟨(k + 3) * (2 * k + 5), ?_⟩
      ring
  have hstoneEven := two_dvd_stone_product m
  have hprodLe : m * (m + 3) ≤ (m + 5) * (m + 4) := by nlinarith
  have hdivLe : m * (m + 3) / 2 ≤ (m + 5) * (m + 4) / 2 :=
    Nat.div_le_div_right hprodLe
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sub hdivLe]
  rw [Nat.cast_div htotalEven (by norm_num : (2 : ℚ) ≠ 0),
    Nat.cast_div hstoneEven (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

end BenzelProblem6Kernel

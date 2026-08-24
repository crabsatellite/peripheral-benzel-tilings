import BenzelProblem6Kernel.ReconstructedExactCover
import BenzelProblem6Kernel.NegativeYPlacementCount

/-!
# Incidence saturation for the reconstructed negative Y
-/

namespace BenzelProblem6Kernel

theorem negativeYChosen_card_eq (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    (negativeYChosenPlacements x y z arms).card + 1 =
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  classical
  let chosen := negativeYChosenPlacements x y z arms
  have hdouble := chosen_incidence_double_count chosen
  simp_rw [card_placementBenzelCells] at hdouble
  have hcoverage : ∀ cell : BenzelCell (x + y + z + 5),
      1 ≤ (chosen.filter fun placement => PlacementCovers placement cell).card := by
    intro cell
    obtain ⟨placement, hchosen, hcover⟩ :=
      negativeY_cell_has_cover x y z arms cell
    apply Finset.card_pos.mpr
    exact ⟨placement, by simp [chosen, hchosen, hcover]⟩
  have hlower : Fintype.card (BenzelCell (x + y + z + 5)) ≤
      ∑ cell : BenzelCell (x + y + z + 5),
        (chosen.filter fun placement => PlacementCovers placement cell).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro cell _
    exact hcoverage cell
  have hleft :
      ∑ placement ∈ chosen, (3 : ℕ) = chosen.card * 3 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hleft] at hdouble
  have harea : Fintype.card (BenzelCell (x + y + z + 5)) =
      3 * (Fintype.card (SimplexPoint (x + y + z + 3)) - 1) := by
    simpa [Nat.add_assoc] using
      card_benzel_eq_three_mul_simplex_sub_one (x + y + z)
  have hupper := negativeYChosen_card_add_one_le_simplex x y z arms
  change chosen.card + 1 ≤
    Fintype.card (SimplexPoint (x + y + z + 3)) at hupper
  have hpositive : 0 < Fintype.card (SimplexPoint (x + y + z + 3)) :=
    Fintype.card_pos_iff.mpr ⟨sourceZero (x + y + z + 3)⟩
  have hlowerChosen :
      3 * (Fintype.card (SimplexPoint (x + y + z + 3)) - 1) ≤
        chosen.card * 3 := by
    rw [← harea]
    exact hlower.trans_eq hdouble.symm
  have hlower' :
      Fintype.card (SimplexPoint (x + y + z + 3)) ≤ chosen.card + 1 := by
    simpa [Nat.mul_comm] using hlowerChosen
  change chosen.card + 1 =
    Fintype.card (SimplexPoint (x + y + z + 3))
  omega

theorem negativeY_cover_filter_card (x y z : ℕ)
    (arms : NegativeArmTriple x y z)
    (cell : BenzelCell (x + y + z + 5)) :
    ((negativeYChosenPlacements x y z arms).filter fun placement =>
      PlacementCovers placement cell).card = 1 := by
  classical
  let chosen := negativeYChosenPlacements x y z arms
  let coverCount := fun target : BenzelCell (x + y + z + 5) =>
    (chosen.filter fun placement => PlacementCovers placement target).card
  have hdouble := chosen_incidence_double_count chosen
  simp_rw [card_placementBenzelCells] at hdouble
  have hchosen := negativeYChosen_card_eq x y z arms
  have harea := card_benzel_eq_three_mul_simplex_sub_one (x + y + z)
  have hsum : ∑ target : BenzelCell (x + y + z + 5), coverCount target =
      Fintype.card (BenzelCell (x + y + z + 5)) := by
    dsimp [coverCount]
    have hleft : ∑ placement ∈ chosen, (3 : ℕ) = chosen.card * 3 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hleft] at hdouble
    change chosen.card + 1 =
      Fintype.card (SimplexPoint (x + y + z + 3)) at hchosen
    omega
  have hone : ∀ target : BenzelCell (x + y + z + 5),
      1 ≤ coverCount target := by
    intro target
    obtain ⟨placement, hchosenMem, hcover⟩ :=
      negativeY_cell_has_cover x y z arms target
    apply Finset.card_pos.mpr
    exact ⟨placement, by simp [coverCount, chosen, hchosenMem, hcover]⟩
  have heraseLower : (Finset.univ.erase cell).card ≤
      ∑ target ∈ Finset.univ.erase cell, coverCount target := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro target _
    exact hone target
  have hdecomp :
      (∑ target ∈ Finset.univ.erase cell, coverCount target) +
          coverCount cell =
        ∑ target ∈ Finset.univ, coverCount target :=
    Finset.sum_erase_add (s := Finset.univ)
      (f := coverCount) (Finset.mem_univ cell)
  have hcardErase : (Finset.univ.erase cell).card + 1 =
      Fintype.card (BenzelCell (x + y + z + 5)) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ cell), Finset.card_univ]
    have hpos := Fintype.card_pos_iff.mpr ⟨cell⟩
    omega
  have hsum' : ∑ target ∈ Finset.univ, coverCount target =
      Fintype.card (BenzelCell (x + y + z + 5)) := by
    simpa using hsum
  have hcellLower := hone cell
  have hcellEq : coverCount cell = 1 := by omega
  simpa [coverCount, chosen] using hcellEq

theorem negativeYChosen_isLiteralTiling (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    IsLiteralTiling (negativeYChosenPlacements x y z arms) := by
  intro cell
  obtain ⟨placement, hchosen, hcover⟩ :=
    negativeY_cell_has_cover x y z arms cell
  refine ⟨placement, ⟨hchosen, hcover⟩, ?_⟩
  intro candidate hcandidate
  have hcard := negativeY_cover_filter_card x y z arms cell
  have hplacement : placement ∈
      (negativeYChosenPlacements x y z arms).filter fun item =>
        PlacementCovers item cell := by simp [hchosen, hcover]
  have hcandidate : candidate ∈
      (negativeYChosenPlacements x y z arms).filter fun item =>
        PlacementCovers item cell := by simp [hcandidate.1, hcandidate.2]
  obtain ⟨only, hsingleton⟩ := Finset.card_eq_one.mp hcard
  rw [hsingleton] at hplacement hcandidate
  simp only [Finset.mem_singleton] at hplacement hcandidate
  exact hcandidate.trans hplacement.symm

noncomputable def negativeYLiteralTiling (x y z : ℕ)
    (arms : NegativeArmTriple x y z) : LiteralTiling (x + y + z) :=
  ⟨negativeYChosenPlacements x y z arms,
    negativeYChosen_isLiteralTiling x y z arms⟩

end BenzelProblem6Kernel

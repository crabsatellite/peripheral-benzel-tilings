import BenzelProblem6Kernel.PositiveYPlacementCount

/-!
# Incidence saturation turns reconstructed coverage into an exact cover
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

theorem card_benzel_eq_three_mul_simplex_sub_one (m : ℕ) :
    Fintype.card (BenzelCell (m + 5)) =
      3 * (Fintype.card (SimplexPoint (m + 3)) - 1) := by
  classical
  rw [Fintype.card_congr (benzelOwnerEquiv (n := m + 5) (by omega))]
  have hpartition := Fintype.card_subtype_compl
    (fun pair : OwnerLabelPair (m + 5) =>
      ¬IsPresentOwnerLabel (m + 5) pair)
  simp only [not_not] at hpartition
  rw [hpartition, Fintype.card_prod, card_missingOwnerLabel (n := m + 5)
    (by omega)]
  have hlabel : Fintype.card MicroLabel = 3 := by decide
  rw [hlabel]
  have hlevel : m + 5 - 2 = m + 3 := by omega
  rw [hlevel]
  have hpositive : 0 < Fintype.card (SimplexPoint (m + 3)) :=
    Fintype.card_pos_iff.mpr ⟨sourceZero (m + 3)⟩
  omega

theorem chosen_incidence_double_count {m : ℕ}
    (chosen : Finset (LiteralPlacement m)) :
    ∑ placement ∈ chosen, (placementBenzelCells placement).card =
      ∑ cell : BenzelCell (m + 5),
        (chosen.filter fun placement => PlacementCovers placement cell).card := by
  classical
  calc
    ∑ placement ∈ chosen, (placementBenzelCells placement).card =
        ∑ placement ∈ chosen,
          ∑ cell : BenzelCell (m + 5),
            if PlacementCovers placement cell then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro placement _
      have hfilter :
          Finset.univ.filter (fun cell : BenzelCell (m + 5) =>
            PlacementCovers placement cell) = placementBenzelCells placement := by
        ext cell
        simp [mem_placementBenzelCells_iff]
      rw [← hfilter, Finset.card_filter]
    _ = ∑ cell : BenzelCell (m + 5),
        ∑ placement ∈ chosen,
          if PlacementCovers placement cell then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ cell : BenzelCell (m + 5),
        (chosen.filter fun placement => PlacementCovers placement cell).card := by
      apply Finset.sum_congr rfl
      intro cell _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem positiveYChosen_card_eq (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    (positiveYChosenPlacements x y z arms).card + 1 =
      Fintype.card (SimplexPoint (x + y + z + 3)) := by
  classical
  let chosen := positiveYChosenPlacements x y z arms
  have hdouble := chosen_incidence_double_count chosen
  simp_rw [card_placementBenzelCells] at hdouble
  have hcoverage : ∀ cell : BenzelCell (x + y + z + 5),
      1 ≤ (chosen.filter fun placement => PlacementCovers placement cell).card := by
    intro cell
    obtain ⟨placement, hchosen, hcover⟩ :=
      positiveY_cell_has_cover x y z arms cell
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
  have hupper := positiveYChosen_card_add_one_le_simplex x y z arms
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

theorem positiveY_cover_filter_card (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (cell : BenzelCell (x + y + z + 5)) :
    ((positiveYChosenPlacements x y z arms).filter fun placement =>
      PlacementCovers placement cell).card = 1 := by
  classical
  let chosen := positiveYChosenPlacements x y z arms
  let coverCount := fun target : BenzelCell (x + y + z + 5) =>
    (chosen.filter fun placement => PlacementCovers placement target).card
  have hdouble := chosen_incidence_double_count chosen
  simp_rw [card_placementBenzelCells] at hdouble
  have hchosen := positiveYChosen_card_eq x y z arms
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
      positiveY_cell_has_cover x y z arms target
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

theorem positiveYChosen_isLiteralTiling (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    IsLiteralTiling (positiveYChosenPlacements x y z arms) := by
  intro cell
  obtain ⟨placement, hchosen, hcover⟩ :=
    positiveY_cell_has_cover x y z arms cell
  refine ⟨placement, ⟨hchosen, hcover⟩, ?_⟩
  intro candidate hcandidate
  have hcard := positiveY_cover_filter_card x y z arms cell
  have hplacement : placement ∈
      (positiveYChosenPlacements x y z arms).filter fun item =>
        PlacementCovers item cell := by simp [hchosen, hcover]
  have hcandidate : candidate ∈
      (positiveYChosenPlacements x y z arms).filter fun item =>
        PlacementCovers item cell := by simp [hcandidate.1, hcandidate.2]
  obtain ⟨only, hsingleton⟩ := Finset.card_eq_one.mp hcard
  rw [hsingleton] at hplacement hcandidate
  simp only [Finset.mem_singleton] at hplacement hcandidate
  exact hcandidate.trans hplacement.symm

noncomputable def positiveYLiteralTiling (x y z : ℕ)
    (arms : PositiveArmTriple x y z) : LiteralTiling (x + y + z) :=
  ⟨positiveYChosenPlacements x y z arms,
    positiveYChosen_isLiteralTiling x y z arms⟩

end BenzelProblem6Kernel

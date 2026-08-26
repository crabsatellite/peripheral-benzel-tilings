import FiniteDefects.D4ParameterWeightSum

/-! # Exact ballot-sum formula for literal d=4 type-103 tilings -/

namespace FiniteDefects

noncomputable def d4TilingCount (m : ℕ) : ℕ :=
  @Fintype.card (D4LiteralTiling m) (d4LiteralTilingCountingFintype m)

theorem d4DefectWeightSum_eq_parameterWeightSum (m : ℕ) :
    letI := d4DefectPlacementFintype m
    (∑ defect : D4DefectPlacement m, d4DefectWeight defect) =
      d4ParameterWeightSum m := by
  letI := d4DefectPlacementFintype m
  letI := d4DefectParameterFintype m
  unfold d4ParameterWeightSum
  apply Fintype.sum_equiv (d4DefectPlacementEquivParameter m)
  intro defect
  change d4DefectWeight defect = d4DefectWeight defect.parameter.defect
  rw [defect.parameter_defect]

theorem d4TilingCount_eq_parameterWeightSum (m : ℕ) :
    d4TilingCount m = d4ParameterWeightSum m := by
  letI := d4DefectPlacementFintype m
  letI (defect : D4DefectPlacement m) := d4ArmTripleFintype defect
  letI := d4SigmaArmTripleFintype m
  letI := d4LiteralTilingCountingFintype m
  unfold d4TilingCount
  rw [Fintype.card_congr (d4LiteralTilingEquivSigmaArmTriple m)]
  rw [Fintype.card_sigma]
  simp_rw [card_d4ArmTriple]
  change (∑ defect : D4DefectPlacement m, d4DefectWeight defect) = _
  exact d4DefectWeightSum_eq_parameterWeightSum m

theorem d4TilingCount_ballot_formula (m : ℕ) :
    d4TilingCount m = d4A m + d4C m + 3 * d4H m := by
  rw [d4TilingCount_eq_parameterWeightSum,
    d4ParameterWeightSum_formula]

end FiniteDefects

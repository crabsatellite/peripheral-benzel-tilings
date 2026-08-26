import FiniteDefects.D4BallotWeights

/-! # Summing the five literal defect fibers -/

namespace FiniteDefects

def d4ParameterSumWeight {m : ℕ} : D4DefectParameterSum m → ℕ
  | .inl p => d4CWeight p
  | .inr (.inl p) => d4AWeight p
  | .inr (.inr (.inl p)) => d4HWeight p
  | .inr (.inr (.inr (.inl p))) => d4BoneBWeight p
  | .inr (.inr (.inr (.inr p))) => d4BoneCWeight p

noncomputable def d4ParameterWeightSum (m : ℕ) : ℕ := by
  letI := d4DefectParameterFintype m
  exact ∑ parameter : D4DefectParameter m, d4DefectParameterWeight parameter

theorem d4DefectParameterEquivSum_weight {m : ℕ}
    (parameter : D4DefectParameter m) :
    d4DefectParameterWeight parameter =
      d4ParameterSumWeight (d4DefectParameterEquivSum m parameter) := by
  rcases parameter <;> simp [d4DefectParameterEquivSum,
    d4ParameterSumWeight]

theorem d4ParameterWeightSum_formula (m : ℕ) :
    d4ParameterWeightSum m = d4A m + d4C m + 3 * d4H m := by
  letI := d4DefectParameterFintype m
  unfold d4ParameterWeightSum
  rw [Fintype.sum_equiv (d4DefectParameterEquivSum m)
    d4DefectParameterWeight d4ParameterSumWeight
    d4DefectParameterEquivSum_weight]
  simp only [Fintype.sum_sum_type, d4ParameterSumWeight]
  rw [sum_d4BoneBWeight, sum_d4BoneCWeight]
  unfold d4A d4C d4H
  omega

end FiniteDefects

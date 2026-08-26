import D4KernelOnly.GeneralEnergyDoubleCount
import FiniteDefects.OwnerBoundaryLiteral

/-! # Pointwise owner-energy classification at offsets `3k` and `3k+1` -/

namespace FiniteDefects

open scoped BigOperators

def offsetOwnerLabelEnergy {t : ℕ} (p : SimplexPoint t)
    (label : MicroLabel) : ℤ := ownerPotential label (ownerQ p) (ownerR p)

noncomputable def offsetOwnerPresentEnergy (t d : ℕ)
    (p : SimplexPoint t) : ℤ := by
  classical
  exact ∑ label : MicroLabel,
    if inBenzel (t + 2) (offsetB t d) (ownerCell p label) then
      offsetOwnerLabelEnergy p label else 0

theorem offset_owner_label_mem_d3k (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) (label : MicroLabel) :
    inBenzel (t + 2) (offsetB t (3 * k)) (ownerCell p label) ↔
      d3kLabelPresent (k := k) label p := by
  have hdb : 3 * k ≤ 2 * t + 4 := by omega
  calc
    _ ↔ ownerLabelPresentAtOffset (3 * k) label p := by
      simpa [offsetB] using
        (ownerLabelPresentAtOffset_iff_inBenzel t (3 * k) hdb label p).symm
    _ ↔ _ := ownerLabelPresentAtOffset_d3k t k hroom label p

theorem offset_owner_label_mem_d3k1 (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) (label : MicroLabel) :
    inBenzel (t + 2) (offsetB t (3 * k + 1)) (ownerCell p label) ↔
      d3k1LabelPresent (k := k) label p := by
  have hdb : 3 * k + 1 ≤ 2 * t + 4 := by omega
  calc
    _ ↔ ownerLabelPresentAtOffset (3 * k + 1) label p := by
      simpa [offsetB] using
        (ownerLabelPresentAtOffset_iff_inBenzel t (3 * k + 1) hdb label p).symm
    _ ↔ _ := ownerLabelPresentAtOffset_d3k1 t k hroom label p

theorem d3k_owner_energy_cases (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    offsetOwnerPresentEnergy t (3 * k) p =
      (if p.u = t - k + 1 then
        offsetOwnerLabelEnergy p .zero + offsetOwnerLabelEnergy p .one else 0) +
      (if p.v = t - k + 1 then
        offsetOwnerLabelEnergy p .one + offsetOwnerLabelEnergy p .two else 0) +
      (if p.w = t - k + 1 then
        offsetOwnerLabelEnergy p .zero + offsetOwnerLabelEnergy p .two else 0) := by
  classical
  unfold offsetOwnerPresentEnergy
  rw [microLabel_sum]
  simp_rw [offset_owner_label_mem_d3k t k hroom]
  have hsum := p.sum_eq
  have hkt : k ≤ t := by omega
  by_cases hu : p.u = t - k + 1
  · have hv : p.v ≤ t - k := by omega
    have hw : p.w ≤ t - k := by omega
    have hvL : p.v ≤ t - k + 1 := by omega
    have hwL : p.w ≤ t - k + 1 := by omega
    have hvNe : p.v ≠ t - k + 1 := by omega
    have hwNe : p.w ≠ t - k + 1 := by omega
    simp [hu, hv, hw, hvL, hwL, hvNe, hwNe, d3kLabelPresent]
  · by_cases hvEq : p.v = t - k + 1
    · have huLe : p.u ≤ t - k := by omega
      have hw : p.w ≤ t - k := by omega
      have huL : p.u ≤ t - k + 1 := by omega
      have hwL : p.w ≤ t - k + 1 := by omega
      have hwNe : p.w ≠ t - k + 1 := by omega
      simp [hu, hvEq, huLe, hw, huL, hwL, hwNe, d3kLabelPresent]
    · by_cases hwEq : p.w = t - k + 1
      · have huLe : p.u ≤ t - k := by omega
        have hv : p.v ≤ t - k := by omega
        have huL : p.u ≤ t - k + 1 := by omega
        have hvL : p.v ≤ t - k + 1 := by omega
        simp [hu, hvEq, hwEq, huLe, hv, huL, hvL, d3kLabelPresent]
      · by_cases hdomain :
          p.u ≤ t - k + 1 ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k + 1
        · have huLe : p.u ≤ t - k := by omega
          have hvLe : p.v ≤ t - k := by omega
          have hwLe : p.w ≤ t - k := by omega
          simp [hu, hvEq, hwEq, huLe, hvLe, hwLe,
            hdomain.1, hdomain.2.1, hdomain.2.2, d3kLabelPresent]
          simpa [offsetOwnerLabelEnergy] using
            ownerPotential_sum (ownerQ p) (ownerR p)
        · have hout : t - k + 1 < p.u ∨ t - k + 1 < p.v ∨
              t - k + 1 < p.w := by omega
          rcases hout with hout | hout | hout
          · simp [hu, hvEq, hwEq, d3kLabelPresent]
            all_goals omega
          · simp [hu, hvEq, hwEq, d3kLabelPresent]
            all_goals omega
          · simp [hu, hvEq, hwEq, d3kLabelPresent]
            all_goals omega

theorem d3k1_owner_energy_cases (t k : ℕ)
    (hroom : 2 * k ≤ t + 1) (p : SimplexPoint t) :
    offsetOwnerPresentEnergy t (3 * k + 1) p =
      (if p.u = t - k + 1 then offsetOwnerLabelEnergy p .one else 0) +
      (if p.v = t - k + 1 then offsetOwnerLabelEnergy p .two else 0) +
      (if p.w = t - k + 1 then offsetOwnerLabelEnergy p .zero else 0) := by
  classical
  unfold offsetOwnerPresentEnergy
  rw [microLabel_sum]
  simp_rw [offset_owner_label_mem_d3k1 t k hroom]
  have hsum := p.sum_eq
  have hkt : k ≤ t := by omega
  by_cases hu : p.u = t - k + 1
  · have hv : p.v ≤ t - k := by omega
    have hw : p.w ≤ t - k := by omega
    have hvL : p.v ≤ t - k + 1 := by omega
    have hwL : p.w ≤ t - k + 1 := by omega
    have hvNe : p.v ≠ t - k + 1 := by omega
    have hwNe : p.w ≠ t - k + 1 := by omega
    simp [hu, hv, hw, hvL, hwL, hvNe, hwNe, d3k1LabelPresent]
  · by_cases hvEq : p.v = t - k + 1
    · have huLe : p.u ≤ t - k := by omega
      have hw : p.w ≤ t - k := by omega
      have huL : p.u ≤ t - k + 1 := by omega
      have hwL : p.w ≤ t - k + 1 := by omega
      have hwNe : p.w ≠ t - k + 1 := by omega
      simp [hu, hvEq, huLe, hw, huL, hwL, hwNe, d3k1LabelPresent]
    · by_cases hwEq : p.w = t - k + 1
      · have huLe : p.u ≤ t - k := by omega
        have hv : p.v ≤ t - k := by omega
        have huL : p.u ≤ t - k + 1 := by omega
        have hvL : p.v ≤ t - k + 1 := by omega
        simp [hu, hvEq, hwEq, huLe, hv, huL, hvL, d3k1LabelPresent]
      · by_cases hdomain :
          p.u ≤ t - k + 1 ∧ p.v ≤ t - k + 1 ∧ p.w ≤ t - k + 1
        · have huLe : p.u ≤ t - k := by omega
          have hvLe : p.v ≤ t - k := by omega
          have hwLe : p.w ≤ t - k := by omega
          simp [hu, hvEq, hwEq, huLe, hvLe, hwLe,
            hdomain.1, hdomain.2.1, hdomain.2.2, d3k1LabelPresent]
          simpa [offsetOwnerLabelEnergy] using
            ownerPotential_sum (ownerQ p) (ownerR p)
        · have hout : t - k + 1 < p.u ∨ t - k + 1 < p.v ∨
              t - k + 1 < p.w := by omega
          rcases hout with hout | hout | hout
          · simp [hu, hvEq, hwEq, d3k1LabelPresent]
            all_goals omega
          · simp [hu, hvEq, hwEq, d3k1LabelPresent]
            all_goals omega
          · simp [hu, hvEq, hwEq, d3k1LabelPresent]
            all_goals omega

end FiniteDefects

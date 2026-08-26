import FiniteDefects.D4GoodSeriesDefinitions

/-! # Final rational simplification after the three Good evaluations -/

namespace FiniteDefects

noncomputable def d4FinalPolynomial : PowerSeries ℚ :=
  9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
      35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
    2 * ternarySeries ^ 5 - ternarySeries ^ 6

noncomputable def d4FinalClosed : PowerSeries ℚ :=
  ternarySeries ^ 3 * d4FinalPolynomial * d4GoodDenominator⁻¹

theorem d4Good_final_of_components
    (hA0 : d4A0Series = d4A0Closed)
    (hC : d4CSeries = d4CClosed)
    (hH : d4HSeries = d4HClosed) :
    d4TilingSeries = d4FinalClosed := by
  rw [d4TilingSeries_ballot_decomposition, hC, hH]
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero :
    (PowerSeries.X : PowerSeries ℚ) ≠ 0)
  have hx3 := ternarySeries_X_equation
  have hx6 : PowerSeries.X * ternarySeries ^ 6 =
      (ternarySeries - 1) * ternarySeries ^ 3 := by
    calc
      PowerSeries.X * ternarySeries ^ 6 =
          (PowerSeries.X * ternarySeries ^ 3) * ternarySeries ^ 3 := by ring
      _ = (ternarySeries - 1) * ternarySeries ^ 3 := by rw [hx3]
  have hx5 : PowerSeries.X * ternarySeries ^ 5 =
      (ternarySeries - 1) * ternarySeries ^ 2 := by
    calc
      PowerSeries.X * ternarySeries ^ 5 =
          (PowerSeries.X * ternarySeries ^ 3) * ternarySeries ^ 2 := by ring
      _ = (ternarySeries - 1) * ternarySeries ^ 2 := by rw [hx3]
  have hden := d4GoodDenominator_mul_inv
  calc
    PowerSeries.X *
          (d4ASeries + d4CClosed + 3 * d4HClosed) =
        PowerSeries.X * d4ASeries +
          (PowerSeries.X * ternarySeries ^ 6) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ +
          3 * (PowerSeries.X * ternarySeries ^ 5) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ := by
      unfold d4CClosed d4HClosed
      ring
    _ = (d4A0Series - 1) +
          ((ternarySeries - 1) * ternarySeries ^ 3) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ +
          3 * ((ternarySeries - 1) * ternarySeries ^ 2) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ := by
      rw [d4A_shift_equation, hx6, hx5]
    _ = (d4A0Closed - 1) +
          ((ternarySeries - 1) * ternarySeries ^ 3) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ +
          3 * ((ternarySeries - 1) * ternarySeries ^ 2) *
            (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹ := by rw [hA0]
    _ = (ternarySeries - 1) * d4FinalPolynomial *
          d4GoodDenominator⁻¹ := by
      unfold d4A0Closed d4FinalPolynomial
      have hden' :
          ((3 - 2 * ternarySeries) *
              (ternarySeries ^ 2 - 3 * ternarySeries + 3)) *
            d4GoodDenominator⁻¹ = 1 := by
        change d4GoodDenominator * d4GoodDenominator⁻¹ = 1
        exact hden
      linear_combination hden'
    _ = PowerSeries.X * d4FinalClosed := by
      unfold d4FinalClosed
      rw [← hx3]
      ring

end FiniteDefects

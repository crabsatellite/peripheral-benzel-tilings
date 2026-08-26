import FiniteDefects.D4TernarySeries

/-! # Formal series appearing in the d=4 Lagrange--Good evaluation -/

namespace FiniteDefects

noncomputable def d4A0 (n : ℕ) : ℕ :=
  ∑ p : SimplexPoint n, d4AWeight p

noncomputable def d4A0Series : PowerSeries ℚ :=
  PowerSeries.mk fun n => (d4A0 n : ℚ)

noncomputable def d4ASeries : PowerSeries ℚ :=
  PowerSeries.mk fun m => (d4A m : ℚ)

noncomputable def d4CSeries : PowerSeries ℚ :=
  PowerSeries.mk fun m => (d4C m : ℚ)

noncomputable def d4HSeries : PowerSeries ℚ :=
  PowerSeries.mk fun m => (d4H m : ℚ)

noncomputable def d4TilingSeries : PowerSeries ℚ :=
  PowerSeries.mk fun m => (d4TilingCount m : ℚ)

noncomputable def d4GoodDenominator : PowerSeries ℚ :=
  (3 - 2 * ternarySeries) *
    (ternarySeries ^ 2 - 3 * ternarySeries + 3)

noncomputable def d4A0Closed : PowerSeries ℚ :=
  ternarySeries ^ 3 * (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹

noncomputable def d4CClosed : PowerSeries ℚ :=
  ternarySeries ^ 6 * (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹

noncomputable def d4HClosed : PowerSeries ℚ :=
  ternarySeries ^ 5 * (2 - ternarySeries) ^ 3 * d4GoodDenominator⁻¹

theorem d4A_eq_A0_succ (m : ℕ) : d4A m = d4A0 (m + 1) := by
  rfl

@[simp] theorem coeff_d4A0Series (n : ℕ) :
    PowerSeries.coeff ℚ n d4A0Series = (d4A0 n : ℚ) := by
  simp [d4A0Series]

@[simp] theorem coeff_d4ASeries (m : ℕ) :
    PowerSeries.coeff ℚ m d4ASeries = (d4A m : ℚ) := by
  simp [d4ASeries]

@[simp] theorem coeff_d4CSeries (m : ℕ) :
    PowerSeries.coeff ℚ m d4CSeries = (d4C m : ℚ) := by
  simp [d4CSeries]

@[simp] theorem coeff_d4HSeries (m : ℕ) :
    PowerSeries.coeff ℚ m d4HSeries = (d4H m : ℚ) := by
  simp [d4HSeries]

@[simp] theorem coeff_d4TilingSeries (m : ℕ) :
    PowerSeries.coeff ℚ m d4TilingSeries = (d4TilingCount m : ℚ) := by
  simp [d4TilingSeries]

theorem d4A0_zero : d4A0 0 = 1 := by
  classical
  have huniv : (Finset.univ : Finset (SimplexPoint 0)) = {cornerU 0} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply simplexPoint_ext <;>
      simp [cornerU] <;>
      have h := p.sum_eq <;> omega
  rw [d4A0, huniv]
  simp [d4AWeight, d4R, ballotNumber, cornerU]

theorem d4A_shift_equation :
    PowerSeries.X * d4ASeries = d4A0Series - 1 := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul]
    rw [map_sub]
    simp [d4A0_zero]
  · rw [map_sub]
    simp only [PowerSeries.coeff_succ_X_mul, coeff_d4ASeries,
      coeff_d4A0Series, PowerSeries.coeff_one, if_false, sub_zero]
    rw [if_neg (by omega), sub_zero]
    rw [d4A_eq_A0_succ]

theorem d4TilingSeries_ballot_decomposition :
    d4TilingSeries = d4ASeries + d4CSeries + 3 * d4HSeries := by
  ext m
  simp only [map_add, map_mul, coeff_d4TilingSeries, coeff_d4ASeries,
    coeff_d4CSeries, coeff_d4HSeries]
  rw [show (3 : PowerSeries ℚ) = PowerSeries.C ℚ 3 by rfl,
    PowerSeries.coeff_C_mul]
  rw [coeff_d4HSeries]
  exact_mod_cast d4TilingCount_ballot_formula m

@[simp] theorem constantCoeff_d4GoodDenominator :
    PowerSeries.constantCoeff ℚ d4GoodDenominator = 1 := by
  unfold d4GoodDenominator
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C ℚ 2 := rfl
  have h3 : (3 : PowerSeries ℚ) = PowerSeries.C ℚ 3 := rfl
  rw [h2, h3]
  simp [constantCoeff_ternarySeries]
  norm_num

theorem d4GoodDenominator_mul_inv :
    d4GoodDenominator * d4GoodDenominator⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp

theorem ternarySeries_X_equation :
    PowerSeries.X * ternarySeries ^ 3 = ternarySeries - 1 := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact ternarySeries_equation.symm

end FiniteDefects

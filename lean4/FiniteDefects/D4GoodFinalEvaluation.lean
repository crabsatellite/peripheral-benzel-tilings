import FiniteDefects.D4GoodComponentGFs
import FiniteDefects.D4GoodFinalAlgebra

/-! # Reversion of the Good parameter and the final d=4 series -/

namespace FiniteDefects

noncomputable def d4SmallRoot : PowerSeries ℚ := ternarySeries - 1

@[simp] theorem constantCoeff_d4SmallRoot :
    PowerSeries.constantCoeff ℚ d4SmallRoot = 0 := by
  simp [d4SmallRoot]

theorem one_add_d4SmallRoot :
    1 + d4SmallRoot = ternarySeries := by
  unfold d4SmallRoot
  ring

theorem d4SmallRoot_eq_X_mul :
    PowerSeries.X * ternarySeries ^ 3 = d4SmallRoot := by
  exact ternarySeries_X_equation

theorem fpsCompose_d4SmallRoot_goodU :
    fpsCompose d4SmallRoot goodU = ternarySeries := by
  unfold goodU
  rw [fpsCompose_add, fpsCompose_one,
    fpsCompose_X d4SmallRoot constantCoeff_d4SmallRoot]
  exact one_add_d4SmallRoot

theorem fpsCompose_d4SmallRoot_oneSubX :
    fpsCompose d4SmallRoot (1 - PowerSeries.X) = 2 - ternarySeries := by
  rw [fpsCompose_sub, fpsCompose_one,
    fpsCompose_X d4SmallRoot constantCoeff_d4SmallRoot]
  unfold d4SmallRoot
  ring

theorem fpsCompose_d4SmallRoot_goodCore :
    fpsCompose d4SmallRoot goodCore = d4GoodDenominator := by
  change fpsComposeRingHom d4SmallRoot constantCoeff_d4SmallRoot goodCore = _
  unfold goodCore d4GoodDenominator
  simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat,
    fpsComposeRingHom_X]
  unfold d4SmallRoot
  ring

theorem fpsCompose_d4SmallRoot_goodQ :
    fpsCompose d4SmallRoot goodQ = PowerSeries.X := by
  unfold goodQ
  rw [fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot]
  rw [fpsCompose_X d4SmallRoot constantCoeff_d4SmallRoot]
  rw [fpsCompose_inv d4SmallRoot
    ((1 + PowerSeries.X : PowerSeries ℚ) ^ 3)
    constantCoeff_d4SmallRoot (by simp)]
  rw [fpsCompose_pow d4SmallRoot (1 + PowerSeries.X)
    constantCoeff_d4SmallRoot]
  rw [fpsCompose_add, fpsCompose_one,
    fpsCompose_X d4SmallRoot constantCoeff_d4SmallRoot]
  rw [one_add_d4SmallRoot]
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  exact ternarySeries_X_equation

theorem fpsCompose_d4SmallRoot_A_rhs :
    fpsCompose d4SmallRoot
        ((1 - PowerSeries.X) ^ 3 * goodU ^ 3 * goodCore⁻¹) =
      d4A0Closed := by
  unfold d4A0Closed
  rw [fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot,
    fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot]
  rw [fpsCompose_pow d4SmallRoot (1 - PowerSeries.X)
      constantCoeff_d4SmallRoot,
    fpsCompose_pow d4SmallRoot goodU constantCoeff_d4SmallRoot]
  rw [fpsCompose_inv d4SmallRoot goodCore constantCoeff_d4SmallRoot
    (by simp)]
  rw [fpsCompose_d4SmallRoot_oneSubX,
    fpsCompose_d4SmallRoot_goodU, fpsCompose_d4SmallRoot_goodCore]
  ring

theorem fpsCompose_d4SmallRoot_C_rhs :
    fpsCompose d4SmallRoot
        ((1 - PowerSeries.X) ^ 3 * goodU ^ 6 * goodCore⁻¹) =
      d4CClosed := by
  unfold d4CClosed
  rw [fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot,
    fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot]
  rw [fpsCompose_pow d4SmallRoot (1 - PowerSeries.X)
      constantCoeff_d4SmallRoot,
    fpsCompose_pow d4SmallRoot goodU constantCoeff_d4SmallRoot]
  rw [fpsCompose_inv d4SmallRoot goodCore constantCoeff_d4SmallRoot
    (by simp)]
  rw [fpsCompose_d4SmallRoot_oneSubX,
    fpsCompose_d4SmallRoot_goodU, fpsCompose_d4SmallRoot_goodCore]
  ring

theorem fpsCompose_d4SmallRoot_H_rhs :
    fpsCompose d4SmallRoot
        ((1 - PowerSeries.X) ^ 3 * goodU ^ 5 * goodCore⁻¹) =
      d4HClosed := by
  unfold d4HClosed
  rw [fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot,
    fpsCompose_mul d4SmallRoot constantCoeff_d4SmallRoot]
  rw [fpsCompose_pow d4SmallRoot (1 - PowerSeries.X)
      constantCoeff_d4SmallRoot,
    fpsCompose_pow d4SmallRoot goodU constantCoeff_d4SmallRoot]
  rw [fpsCompose_inv d4SmallRoot goodCore constantCoeff_d4SmallRoot
    (by simp)]
  rw [fpsCompose_d4SmallRoot_oneSubX,
    fpsCompose_d4SmallRoot_goodU, fpsCompose_d4SmallRoot_goodCore]
  ring

theorem d4Good_A0_component : d4A0Series = d4A0Closed := by
  have h := congrArg (fpsCompose d4SmallRoot) d4A0_Good_equation
  rw [fpsCompose_assoc d4SmallRoot goodQ d4A0Series
      constantCoeff_d4SmallRoot constantCoeff_goodQ,
    fpsCompose_d4SmallRoot_goodQ, fpsCompose_X_left,
    fpsCompose_d4SmallRoot_A_rhs] at h
  exact h

theorem d4Good_C_component : d4CSeries = d4CClosed := by
  have h := congrArg (fpsCompose d4SmallRoot) d4C_Good_equation
  rw [fpsCompose_assoc d4SmallRoot goodQ d4CSeries
      constantCoeff_d4SmallRoot constantCoeff_goodQ,
    fpsCompose_d4SmallRoot_goodQ, fpsCompose_X_left,
    fpsCompose_d4SmallRoot_C_rhs] at h
  exact h

theorem d4Good_H_component : d4HSeries = d4HClosed := by
  have h := congrArg (fpsCompose d4SmallRoot) d4H_Good_equation
  rw [fpsCompose_assoc d4SmallRoot goodQ d4HSeries
      constantCoeff_d4SmallRoot constantCoeff_goodQ,
    fpsCompose_d4SmallRoot_goodQ, fpsCompose_X_left,
    fpsCompose_d4SmallRoot_H_rhs] at h
  exact h

theorem d4Good_generating_function :
    d4TilingSeries =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹ := by
  exact d4Good_final_of_components d4Good_A0_component
    d4Good_C_component d4Good_H_component

end FiniteDefects

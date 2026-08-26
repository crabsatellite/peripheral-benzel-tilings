import FiniteDefects.D4GoodKernelCoefficient

/-! # Duality of Good functionals and the w-monomial basis -/

namespace FiniteDefects

open Finset BigOperators Finsupp

theorem goodXPower_eq_monomial (n : GoodIndex) :
    goodXPower n = MvPowerSeries.monomial ℚ n 1 := by
  rw [← goodIndex_coordinates n]
  unfold goodXPower
  simp only [Fin.prod_univ_succ, goodIndex_zero, goodIndex_one,
    goodIndex_two]
  simp [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
    goodIndex, add_assoc]

theorem goodPhi_inv_pow_mul_pow {i : Fin 3} {lower upper : ℕ}
    (h : lower ≤ upper) :
    (goodPhi i)⁻¹ ^ lower * goodPhi i ^ upper =
      goodPhi i ^ (upper - lower) := by
  calc
    (goodPhi i)⁻¹ ^ lower * goodPhi i ^ upper =
        (goodPhi i)⁻¹ ^ lower *
          (goodPhi i ^ lower * goodPhi i ^ (upper - lower)) := by
            rw [← pow_add, Nat.add_sub_of_le h]
    _ = ((goodPhi i)⁻¹ * goodPhi i) ^ lower *
          goodPhi i ^ (upper - lower) := by
            rw [mul_pow]
            ring
    _ = goodPhi i ^ (upper - lower) := by
      rw [MvPowerSeries.inv_mul_cancel (goodPhi i) (by simp),
        one_pow, one_mul]

theorem goodWPower_factor (k : GoodIndex) :
    goodWPower k = goodXPower k *
      goodFamilyPower (fun i => (goodPhi i)⁻¹) k := by
  unfold goodWPower goodFamilyPower goodW
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib]
  rfl

theorem goodWPower_mul_phiPower {k n : GoodIndex} (hkn : k ≤ n) :
    goodWPower k * goodPhiPower n =
      goodXPower k * goodPhiPower (n - k) := by
  unfold goodWPower goodPhiPower goodFamilyPower goodW
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin 3,
        (MvPowerSeries.X i * (goodPhi i)⁻¹) ^ k i *
          goodPhi i ^ n i) =
        ∏ i : Fin 3,
          MvPowerSeries.X i ^ k i * goodPhi i ^ (n i - k i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [mul_pow]
      calc
        MvPowerSeries.X i ^ k i * (goodPhi i)⁻¹ ^ k i * goodPhi i ^ n i =
            MvPowerSeries.X i ^ k i *
              ((goodPhi i)⁻¹ ^ k i * goodPhi i ^ n i) := by ring
        _ = MvPowerSeries.X i ^ k i * goodPhi i ^ (n i - k i) := by
          rw [goodPhi_inv_pow_mul_pow (hkn i)]
    _ = (∏ i : Fin 3, MvPowerSeries.X i ^ k i) *
        ∏ i : Fin 3, goodPhi i ^ (n - k) i := by
      rw [Finset.prod_mul_distrib]
      apply congrArg₂ (· * ·) rfl
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finsupp.coe_tsub]

theorem goodWPower_coeff_zero_of_not_le {k m : GoodIndex} (hnot : ¬k ≤ m) :
    MvPowerSeries.coeff ℚ m (goodWPower k) = 0 := by
  rw [goodWPower_factor, goodXPower_eq_monomial]
  rw [MvPowerSeries.coeff_monomial_mul, if_neg hnot]

theorem goodFunctional_wPower (n k : GoodIndex) :
    goodFunctional n (goodWPower k) = if k = n then 1 else 0 := by
  by_cases hkn : k ≤ n
  · unfold goodFunctional
    rw [goodWPower_mul_phiPower hkn,
      goodXPower_eq_monomial, mul_assoc,
      MvPowerSeries.coeff_monomial_mul, if_pos hkn, one_mul]
    rw [goodKernelCoefficient_index]
    by_cases hknEq : k = n
    · subst k
      simp
    · rw [if_neg hknEq]
      rw [if_neg]
      intro hsub
      have hle : n ≤ k := by
        intro i
        have hz := congrArg (fun x : GoodIndex => x i) hsub
        simp [Finsupp.coe_tsub] at hz
        omega
      exact hknEq (le_antisymm hkn hle)
  · unfold goodFunctional
    rw [goodWPower_factor, goodXPower_eq_monomial]
    rw [show MvPowerSeries.monomial ℚ k 1 *
          goodFamilyPower (fun i => (goodPhi i)⁻¹) k * goodPhiPower n *
          goodDeterminant =
        MvPowerSeries.monomial ℚ k 1 *
          (goodFamilyPower (fun i => (goodPhi i)⁻¹) k *
            goodPhiPower n * goodDeterminant) by ring]
    rw [MvPowerSeries.coeff_monomial_mul, if_neg hkn]
    exact (if_neg (fun heq => hkn (le_of_eq heq))).symm

end FiniteDefects

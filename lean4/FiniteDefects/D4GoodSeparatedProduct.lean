import FiniteDefects.D4GoodExpansion

/-! # Coefficients of products of three one-axis series -/

namespace FiniteDefects

open Finset BigOperators Finsupp

theorem goodSeparatedProduct01_coeff
    (series0 series1 : GoodSeries) (value0 value1 : ℕ → ℚ)
    (h0 : ∀ n, MvPowerSeries.coeff ℚ n series0 =
      if goodAxisOnly 0 n then value0 (n 0) else 0)
    (h1 : ∀ n, MvPowerSeries.coeff ℚ n series1 =
      if goodAxisOnly 1 n then value1 (n 1) else 0)
    (a b : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b 0) (series0 * series1) =
      value0 a * value1 b := by
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single
    (Finsupp.single 0 a, Finsupp.single 1 b)]
  · rw [h0, h1]
    simp [goodAxisOnly]
  · intro pair hpair hne
    rw [h0, h1]
    by_cases hleft : goodAxisOnly 0 pair.1
    · by_cases hright : goodAxisOnly 1 pair.2
      · exfalso
        apply hne
        have hsum := Finset.mem_antidiagonal.mp hpair
        have hr0 : pair.2 0 = 0 := by
          unfold goodAxisOnly at hright
          rw [hright]
          simp
        have hl1 : pair.1 1 = 0 := by
          unfold goodAxisOnly at hleft
          rw [hleft]
          simp
        apply Prod.ext
        · unfold goodAxisOnly at hleft
          rw [hleft]
          congr 1
          have hx := congrArg (fun n : GoodIndex => n 0) hsum
          simp [goodIndex, hr0] at hx
          omega
        · unfold goodAxisOnly at hright
          rw [hright]
          congr 1
          have hy := congrArg (fun n : GoodIndex => n 1) hsum
          simp [goodIndex, hl1] at hy
          omega
      · simp [hright]
    · simp [hleft]
  · intro hnotmem
    exfalso
    apply hnotmem
    rw [Finset.mem_antidiagonal]
    ext i
    fin_cases i <;> simp [goodIndex]

theorem goodSeparatedProduct01_coeff_zero_of_two_ne_zero
    (series0 series1 : GoodSeries) (value0 value1 : ℕ → ℚ)
    (h0 : ∀ n, MvPowerSeries.coeff ℚ n series0 =
      if goodAxisOnly 0 n then value0 (n 0) else 0)
    (h1 : ∀ n, MvPowerSeries.coeff ℚ n series1 =
      if goodAxisOnly 1 n then value1 (n 1) else 0)
    (n : GoodIndex) (hne : n 2 ≠ 0) :
    MvPowerSeries.coeff ℚ n (series0 * series1) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  rw [h0, h1]
  by_cases hleft : goodAxisOnly 0 pair.1
  · by_cases hright : goodAxisOnly 1 pair.2
    · exfalso
      apply hne
      have hsum := Finset.mem_antidiagonal.mp hpair
      have hz := congrArg (fun index : GoodIndex => index 2) hsum
      unfold goodAxisOnly at hleft hright
      rw [hleft, hright] at hz
      simpa using hz.symm
    · simp [hright]
  · simp [hleft]

theorem goodSeparatedProduct_coeff
    (series0 series1 series2 : GoodSeries)
    (value0 value1 value2 : ℕ → ℚ)
    (h0 : ∀ n, MvPowerSeries.coeff ℚ n series0 =
      if goodAxisOnly 0 n then value0 (n 0) else 0)
    (h1 : ∀ n, MvPowerSeries.coeff ℚ n series1 =
      if goodAxisOnly 1 n then value1 (n 1) else 0)
    (h2 : ∀ n, MvPowerSeries.coeff ℚ n series2 =
      if goodAxisOnly 2 n then value2 (n 2) else 0)
    (a b c : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b c)
      ((series0 * series1) * series2) = value0 a * value1 b * value2 c := by
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (goodIndex a b 0, Finsupp.single 2 c)]
  · rw [goodSeparatedProduct01_coeff series0 series1 value0 value1 h0 h1]
    rw [h2]
    simp [goodAxisOnly]
  · intro pair hpair hne
    rw [h2]
    by_cases hright : goodAxisOnly 2 pair.2
    · by_cases hleftTwo : pair.1 2 = 0
      · exfalso
        apply hne
        have hsum := Finset.mem_antidiagonal.mp hpair
        have hr0 : pair.2 0 = 0 := by
          unfold goodAxisOnly at hright
          rw [hright]
          simp
        have hr1 : pair.2 1 = 0 := by
          unfold goodAxisOnly at hright
          rw [hright]
          simp
        apply Prod.ext
        · rw [← goodIndex_coordinates pair.1]
          ext i
          fin_cases i
          · have hx := congrArg (fun n : GoodIndex => n 0) hsum
            simp [goodIndex, hr0] at hx ⊢
            omega
          · have hy := congrArg (fun n : GoodIndex => n 1) hsum
            simp [goodIndex, hr1] at hy ⊢
            omega
          · simp [hleftTwo]
        · unfold goodAxisOnly at hright
          rw [hright]
          congr 1
          have hz := congrArg (fun n : GoodIndex => n 2) hsum
          simp [goodIndex, hleftTwo] at hz
          omega
      · rw [goodSeparatedProduct01_coeff_zero_of_two_ne_zero
          series0 series1 value0 value1 h0 h1 pair.1 hleftTwo]
        simp
    · simp [hright]
  · intro hnotmem
    exfalso
    apply hnotmem
    rw [Finset.mem_antidiagonal]
    ext i
    fin_cases i <;> simp [goodIndex]

end FiniteDefects

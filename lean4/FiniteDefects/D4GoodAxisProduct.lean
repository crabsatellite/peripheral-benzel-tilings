import FiniteDefects.D4GoodAxisSeries

/-! # Separated coefficients of the three Good axis factors -/

namespace FiniteDefects

open Finset BigOperators Finsupp

theorem goodAxisProduct01_coeff (energy0 energy1 a b : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b 0)
      (goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1) =
      goodAxisCoefficient energy0 a * goodAxisCoefficient energy1 b := by
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single
    (Finsupp.single 0 a, Finsupp.single 1 b)]
  · simp [goodIndex, goodAxisOnly]
  · intro pair hpair hne
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
          have h0 := congrArg (fun n : GoodIndex => n 0) hsum
          simp [goodIndex, hr0] at h0
          omega
        · unfold goodAxisOnly at hright
          rw [hright]
          congr 1
          have h1 := congrArg (fun n : GoodIndex => n 1) hsum
          simp [goodIndex, hl1] at h1
          omega
      · simp [coeff_goodAxisSeries, hright]
    · simp [coeff_goodAxisSeries, hleft]
  · intro hnotmem
    exfalso
    apply hnotmem
    rw [Finset.mem_antidiagonal]
    ext i
    fin_cases i <;> simp [goodIndex]

theorem goodAxisProduct01_coeff_zero_of_two_ne_zero
    (energy0 energy1 : ℕ) (n : GoodIndex) (hne : n 2 ≠ 0) :
    MvPowerSeries.coeff ℚ n
      (goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hleft : goodAxisOnly 0 pair.1
  · by_cases hright : goodAxisOnly 1 pair.2
    · exfalso
      apply hne
      have hsum := Finset.mem_antidiagonal.mp hpair
      have h2 := congrArg (fun index : GoodIndex => index 2) hsum
      unfold goodAxisOnly at hleft hright
      rw [hleft, hright] at h2
      simpa using h2.symm
    · simp [coeff_goodAxisSeries, hright]
  · simp [coeff_goodAxisSeries, hleft]

theorem goodAxisProduct_coeff (energy0 energy1 energy2 a b c : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b c)
      ((goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1) *
        goodAxisSeries 2 energy2) =
      goodAxisCoefficient energy0 a * goodAxisCoefficient energy1 b *
        goodAxisCoefficient energy2 c := by
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single
    (goodIndex a b 0, Finsupp.single 2 c)]
  · rw [goodAxisProduct01_coeff]
    simp [goodAxisOnly]
  · intro pair hpair hne
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
          · have h0 := congrArg (fun n : GoodIndex => n 0) hsum
            simp [goodIndex, hr0] at h0 ⊢
            omega
          · have h1 := congrArg (fun n : GoodIndex => n 1) hsum
            simp [goodIndex, hr1] at h1 ⊢
            omega
          · simp [hleftTwo]
        · unfold goodAxisOnly at hright
          rw [hright]
          congr 1
          have h2 := congrArg (fun n : GoodIndex => n 2) hsum
          simp [goodIndex, hleftTwo] at h2
          omega
      · rw [goodAxisProduct01_coeff_zero_of_two_ne_zero
          energy0 energy1 pair.1 hleftTwo]
        simp
    · simp [coeff_goodAxisSeries, hright]
  · intro hnotmem
    exfalso
    apply hnotmem
    rw [Finset.mem_antidiagonal]
    ext i
    fin_cases i <;> simp [goodIndex]

end FiniteDefects

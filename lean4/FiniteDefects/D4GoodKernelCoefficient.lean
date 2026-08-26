import FiniteDefects.D4GoodAxisProduct

/-! # The Good determinant coefficient is the specialized binomial delta -/

namespace FiniteDefects

open Finset BigOperators Finsupp

def goodEnergy : GoodIndex → Fin 3 → ℕ
  | n, 0 => 2 * n 0 + n 2
  | n, 1 => n 0 + 2 * n 1
  | n, 2 => n 1 + 2 * n 2

@[simp] theorem goodEnergy_zero (a b c : ℕ) :
    goodEnergy (goodIndex a b c) 0 = 2 * a + c := by
  simp [goodEnergy]

@[simp] theorem goodEnergy_one (a b c : ℕ) :
    goodEnergy (goodIndex a b c) 1 = a + 2 * b := by
  simp [goodEnergy]

@[simp] theorem goodEnergy_two (a b c : ℕ) :
    goodEnergy (goodIndex a b c) 2 = b + 2 * c := by
  simp [goodEnergy]

theorem goodPhiPower_coordinates (a b c : ℕ) :
    goodPhiPower (goodIndex a b c) =
      goodOnePlus 0 ^ (2 * a + c) *
        goodOnePlus 1 ^ (a + 2 * b) *
          goodOnePlus 2 ^ (b + 2 * c) := by
  unfold goodPhiPower goodFamilyPower
  simp [Fin.prod_univ_succ, goodIndex, goodPhi]
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  calc
    goodOnePlus 0 ^ (2 * a) * goodOnePlus 1 ^ a *
          (goodOnePlus 1 ^ (2 * b) * goodOnePlus 2 ^ b *
            (goodOnePlus 2 ^ (2 * c) * goodOnePlus 0 ^ c)) =
        (goodOnePlus 0 ^ (2 * a) * goodOnePlus 0 ^ c) *
          (goodOnePlus 1 ^ a * goodOnePlus 1 ^ (2 * b)) *
            (goodOnePlus 2 ^ b * goodOnePlus 2 ^ (2 * c)) := by ring
    _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]

theorem goodPhiPower_mul_determinant_coordinates (a b c : ℕ) :
    goodPhiPower (goodIndex a b c) * goodDeterminant =
      goodNumerator *
        ((goodAxisSeries 0 (2 * a + c) *
          goodAxisSeries 1 (a + 2 * b)) *
            goodAxisSeries 2 (b + 2 * c)) := by
  rw [goodPhiPower_coordinates]
  unfold goodDeterminant
  rw [goodAxisSeries_eq, goodAxisSeries_eq, goodAxisSeries_eq]
  ring

theorem goodAxisCoefficient_upper (a c : ℕ) :
    goodAxisCoefficient (2 * a + c) a = d4GoodUpper (2 * a + c) a := by
  rcases a with _ | a <;> rcases c with _ | c <;>
    simp [goodAxisCoefficient, d4GoodUpper]

theorem goodAxisCoefficient_lower (a c : ℕ) :
    (if 1 ≤ a then goodAxisCoefficient (2 * a + c) (a - 1) else 0) =
      d4GoodLower (2 * a + c) a := by
  rcases a with _ | a <;> rcases c with _ | c <;>
    simp [goodAxisCoefficient, d4GoodLower]

theorem goodMonomial_axisProduct_coeff
    (energy0 energy1 energy2 sa sb sc a b c : ℕ) :
    let axes := (goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1) *
      goodAxisSeries 2 energy2
    MvPowerSeries.coeff ℚ (goodIndex a b c)
      (MvPowerSeries.monomial ℚ (goodIndex sa sb sc) 1 * axes) =
      if sa ≤ a ∧ sb ≤ b ∧ sc ≤ c then
        goodAxisCoefficient energy0 (a - sa) *
          goodAxisCoefficient energy1 (b - sb) *
            goodAxisCoefficient energy2 (c - sc) else 0 := by
  dsimp only
  rw [MvPowerSeries.coeff_monomial_mul]
  have hle : goodIndex sa sb sc ≤ goodIndex a b c ↔
      sa ≤ a ∧ sb ≤ b ∧ sc ≤ c := by
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> simp [h0, h1, h2]
  by_cases hcoords : sa ≤ a ∧ sb ≤ b ∧ sc ≤ c
  · have h := hle.mpr hcoords
    rw [if_pos h, if_pos hcoords]
    have hsub : goodIndex a b c - goodIndex sa sb sc =
        goodIndex (a - sa) (b - sb) (c - sc) := by
      ext i
      fin_cases i <;> simp [Finsupp.coe_tsub]
    rw [hsub, one_mul, goodAxisProduct_coeff]
  · have hnot : ¬goodIndex sa sb sc ≤ goodIndex a b c :=
      fun h => hcoords (hle.mp h)
    rw [if_neg hnot, if_neg hcoords]

theorem goodMonomial_axisProduct_coeff_flat
    (energy0 energy1 energy2 sa sb sc a b c : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b c)
      (MvPowerSeries.monomial ℚ (goodIndex sa sb sc) 1 *
          goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1 *
        goodAxisSeries 2 energy2) =
      if sa ≤ a ∧ sb ≤ b ∧ sc ≤ c then
        goodAxisCoefficient energy0 (a - sa) *
          goodAxisCoefficient energy1 (b - sb) *
            goodAxisCoefficient energy2 (c - sc) else 0 := by
  rw [show MvPowerSeries.monomial ℚ (goodIndex sa sb sc) 1 *
          goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1 *
          goodAxisSeries 2 energy2 =
      MvPowerSeries.monomial ℚ (goodIndex sa sb sc) 1 *
        ((goodAxisSeries 0 energy0 * goodAxisSeries 1 energy1) *
          goodAxisSeries 2 energy2) by ring]
  exact goodMonomial_axisProduct_coeff
    energy0 energy1 energy2 sa sb sc a b c

theorem goodNumerator_axis_coeff (a b c : ℕ) :
    let axes := (goodAxisSeries 0 (2 * a + c) *
      goodAxisSeries 1 (a + 2 * b)) *
        goodAxisSeries 2 (b + 2 * c)
    MvPowerSeries.coeff ℚ (goodIndex a b c) (goodNumerator * axes) =
      d4GoodKernelDelta a b c := by
  dsimp only
  let axes := (goodAxisSeries 0 (2 * a + c) *
      goodAxisSeries 1 (a + 2 * b)) *
        goodAxisSeries 2 (b + 2 * c)
  have hN : goodNumerator =
      MvPowerSeries.monomial ℚ (goodIndex 0 0 0) 1 -
        MvPowerSeries.monomial ℚ (goodIndex 1 0 0) 1 -
        MvPowerSeries.monomial ℚ (goodIndex 0 1 0) 1 -
        MvPowerSeries.monomial ℚ (goodIndex 0 0 1) 1 +
        MvPowerSeries.monomial ℚ (goodIndex 1 1 0) 1 +
        MvPowerSeries.monomial ℚ (goodIndex 1 0 1) 1 +
        MvPowerSeries.monomial ℚ (goodIndex 0 1 1) 1 -
        2 * MvPowerSeries.monomial ℚ (goodIndex 1 1 1) 1 := by
    unfold goodNumerator
    simp [MvPowerSeries.X, goodIndex,
      MvPowerSeries.monomial_mul_monomial]
  change MvPowerSeries.coeff ℚ (goodIndex a b c)
      (goodNumerator * axes) = d4GoodKernelDelta a b c
  rw [hN]
  simp only [sub_mul, add_mul, mul_assoc]
  simp only [map_add, map_sub]
  rw [show (2 : GoodSeries) = MvPowerSeries.C (Fin 3) ℚ 2 by rfl,
    MvPowerSeries.coeff_C_mul]
  dsimp [axes]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 0 0 0 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 1 0 0 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 0 1 0 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 0 0 1 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 1 1 0 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 1 0 1 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 0 1 1 a b c]
  rw [goodMonomial_axisProduct_coeff
    (2 * a + c) (a + 2 * b) (b + 2 * c) 1 1 1 a b c]
  simp only [Nat.zero_le, and_self, true_and, Nat.sub_zero]
  have hAu := goodAxisCoefficient_upper a c
  have hBu : goodAxisCoefficient (a + 2 * b) b =
      d4GoodUpper (a + 2 * b) b := by
    simpa [Nat.add_comm, Nat.mul_comm] using goodAxisCoefficient_upper b a
  have hCu : goodAxisCoefficient (b + 2 * c) c =
      d4GoodUpper (b + 2 * c) c := by
    simpa [Nat.add_comm, Nat.mul_comm] using goodAxisCoefficient_upper c b
  have hAl := goodAxisCoefficient_lower a c
  have hBl : (if 1 ≤ b then
      goodAxisCoefficient (a + 2 * b) (b - 1) else 0) =
      d4GoodLower (a + 2 * b) b := by
    simpa [Nat.add_comm, Nat.mul_comm] using goodAxisCoefficient_lower b a
  have hCl : (if 1 ≤ c then
      goodAxisCoefficient (b + 2 * c) (c - 1) else 0) =
      d4GoodLower (b + 2 * c) c := by
    simpa [Nat.add_comm, Nat.mul_comm] using goodAxisCoefficient_lower c b
  by_cases ha : 1 ≤ a <;> by_cases hb : 1 ≤ b <;> by_cases hc : 1 ≤ c
  all_goals
    simp only [ha, hb, hc, and_self, true_and, and_true, if_true, if_false] at hAl hBl hCl ⊢
    unfold d4GoodKernelDelta
    rw [hAu, hBu, hCu]
    rw [← hAl, ← hBl, ← hCl]
    ring

theorem goodKernelCoefficient (a b c : ℕ) :
    MvPowerSeries.coeff ℚ (goodIndex a b c)
      (goodPhiPower (goodIndex a b c) * goodDeterminant) =
      if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 0 := by
  rw [goodPhiPower_mul_determinant_coordinates]
  rw [goodNumerator_axis_coeff]
  exact d4GoodKernelDelta_eq a b c

theorem goodKernelCoefficient_index (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (goodPhiPower n * goodDeterminant) =
      if n = 0 then 1 else 0 := by
  rw [← goodIndex_coordinates n]
  rw [goodKernelCoefficient]
  congr 1
  apply propext
  constructor
  · rintro ⟨h0, h1, h2⟩
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  · intro h
    have h0 := congrArg (fun n : GoodIndex => n 0) h
    have h1 := congrArg (fun n : GoodIndex => n 1) h
    have h2 := congrArg (fun n : GoodIndex => n 2) h
    have h0' : n 0 = 0 := by simpa using h0
    have h1' : n 1 = 0 := by simpa using h1
    have h2' : n 2 = 0 := by simpa using h2
    exact ⟨h0', h1', h2'⟩

end FiniteDefects

import FiniteDefects.D4GoodSeparatedProduct
import FiniteDefects.D4GoodComponentMv

/-! # Good functionals of the three d=4 numerators -/

namespace FiniteDefects

open Finset BigOperators Finsupp

noncomputable def goodBallotAxis (i : Fin 3) (energy : ℕ) : GoodSeries :=
  (1 - MvPowerSeries.X i) * goodAxisSeries i (energy + 1)

def goodBallotValue (energy degree : ℕ) : ℚ :=
  (energy.choose degree : ℕ) -
    match degree with
    | 0 => 0
    | degree + 1 => (energy.choose degree : ℕ)

theorem coeff_goodBallotAxis (i : Fin 3) (energy : ℕ) (n : GoodIndex) :
    MvPowerSeries.coeff ℚ n (goodBallotAxis i energy) =
      if goodAxisOnly i n then goodBallotValue energy (n i) else 0 := by
  unfold goodBallotAxis
  rw [sub_mul, one_mul, map_sub, coeff_goodX_mul]
  by_cases haxis : goodAxisOnly i n
  · rw [coeff_goodAxisSeries, if_pos haxis]
    by_cases hzero : n i = 0
    · have hn : n = 0 := haxis.trans (by simp [hzero])
      subst n
      rw [if_pos (goodAxisOnly_zero i)]
      simp [goodBallotValue, goodAxisCoefficient, goodAxisOnly]
    · have hle : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        omega
      rw [if_pos hle]
      have haxisSub := (goodAxisOnly_sub_iff i n hle).2 haxis
      rw [coeff_goodAxisSeries, if_pos haxisSub]
      rw [goodAxisCoefficient_succ, goodAxisCoefficient_succ]
      rw [goodAxis_sub_coord]
      obtain ⟨degree, hdegree⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      rw [hdegree]
      rw [if_pos haxis]
      simp [goodBallotValue]
  · rw [coeff_goodAxisSeries, if_neg haxis, if_neg haxis]
    split_ifs with hle
    · rw [coeff_goodAxisSeries]
      rw [if_neg (fun hsub =>
        haxis ((goodAxisOnly_sub_iff i n hle).1 hsub))]
      ring
    · ring

theorem goodBallotValue_d4R (x y : ℕ) :
    goodBallotValue (x + 2 * y) y = (d4R x y : ℕ) := by
  rcases y with _ | y
  · simp [goodBallotValue, d4R, ballotNumber]
  · have hhalf : y < (x + 2 * (y + 1)) / 2 := by omega
    have hle := Nat.choose_le_succ_of_lt_half_left hhalf
    unfold goodBallotValue d4R ballotNumber
    simp only
    rw [Nat.cast_sub hle]

theorem goodDeterminant_inv_cancel :
    goodDeterminant⁻¹ * goodDeterminant = 1 := by
  apply MvPowerSeries.inv_mul_cancel
  simp

theorem goodFunctional_cancel_determinant (n : GoodIndex)
    (numerator : GoodSeries) :
    goodFunctional n (numerator * goodDeterminant⁻¹) =
      MvPowerSeries.coeff ℚ n (numerator * goodPhiPower n) := by
  unfold goodFunctional
  rw [show (numerator * goodDeterminant⁻¹ * goodPhiPower n) *
      goodDeterminant = numerator * goodPhiPower n *
        (goodDeterminant⁻¹ * goodDeterminant) by ring]
  rw [goodDeterminant_inv_cancel, mul_one]

theorem goodANumerator_phiPower (a b c : ℕ) :
    goodANumerator * goodPhiPower (goodIndex a b c) =
      (goodBallotAxis 0 (2 * a + c) * goodBallotAxis 1 (a + 2 * b)) *
        goodBallotAxis 2 (b + 2 * c) := by
  rw [goodPhiPower_coordinates]
  unfold goodANumerator goodBallotAxis
  rw [goodAxisSeries_succ_eq_pow, goodAxisSeries_succ_eq_pow,
    goodAxisSeries_succ_eq_pow]
  unfold goodOnePlus
  ring

theorem goodCNumerator_phiPower (a b c : ℕ) :
    goodCNumerator * goodPhiPower (goodIndex a b c) =
      (goodBallotAxis 0 (2 * a + c + 1) *
        goodBallotAxis 1 (a + 2 * b + 1)) *
          goodBallotAxis 2 (b + 2 * c + 1) := by
  rw [goodPhiPower_coordinates]
  unfold goodCNumerator goodBallotAxis
  rw [goodAxisSeries_succ_eq_pow, goodAxisSeries_succ_eq_pow,
    goodAxisSeries_succ_eq_pow]
  unfold goodOnePlus
  ring

theorem goodHNumerator_phiPower (a b c : ℕ) :
    goodHNumerator * goodPhiPower (goodIndex a b c) =
      (goodBallotAxis 0 (2 * a + c + 1) *
        goodBallotAxis 1 (a + 2 * b)) *
          goodBallotAxis 2 (b + 2 * c + 1) := by
  rw [goodPhiPower_coordinates]
  unfold goodHNumerator goodBallotAxis
  rw [goodAxisSeries_succ_eq_pow, goodAxisSeries_succ_eq_pow,
    goodAxisSeries_succ_eq_pow]
  unfold goodOnePlus
  ring

theorem goodFunctional_A (a b c : ℕ) :
    goodFunctional (goodIndex a b c) goodAFunction = d4AWeight
      { u := a, v := b, w := c, sum_eq := rfl } := by
  unfold goodAFunction
  rw [goodFunctional_cancel_determinant]
  rw [goodANumerator_phiPower]
  rw [goodSeparatedProduct_coeff
    (goodBallotAxis 0 (2 * a + c))
    (goodBallotAxis 1 (a + 2 * b))
    (goodBallotAxis 2 (b + 2 * c))
    (goodBallotValue (2 * a + c)) (goodBallotValue (a + 2 * b))
    (goodBallotValue (b + 2 * c))
    (coeff_goodBallotAxis 0 (2 * a + c))
    (coeff_goodBallotAxis 1 (a + 2 * b))
    (coeff_goodBallotAxis 2 (b + 2 * c))]
  have h0 : goodBallotValue (2 * a + c) a = (d4R c a : ℕ) := by
    simpa [Nat.add_comm, Nat.mul_comm] using goodBallotValue_d4R c a
  have h1 := goodBallotValue_d4R a b
  have h2 := goodBallotValue_d4R b c
  rw [h0, h1, h2]
  simp [d4AWeight]
  ring

theorem goodFunctional_C (a b c : ℕ) :
    goodFunctional (goodIndex a b c) goodCFunction = d4CWeight
      { u := a, v := b, w := c, sum_eq := rfl } := by
  unfold goodCFunction
  rw [goodFunctional_cancel_determinant]
  rw [goodCNumerator_phiPower]
  rw [goodSeparatedProduct_coeff
    (goodBallotAxis 0 (2 * a + c + 1))
    (goodBallotAxis 1 (a + 2 * b + 1))
    (goodBallotAxis 2 (b + 2 * c + 1))
    (goodBallotValue (2 * a + c + 1))
    (goodBallotValue (a + 2 * b + 1))
    (goodBallotValue (b + 2 * c + 1))
    (coeff_goodBallotAxis 0 (2 * a + c + 1))
    (coeff_goodBallotAxis 1 (a + 2 * b + 1))
    (coeff_goodBallotAxis 2 (b + 2 * c + 1))]
  have h0 : goodBallotValue (2 * a + c + 1) a = (d4R (c + 1) a : ℕ) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
      goodBallotValue_d4R (c + 1) a
  have h1 : goodBallotValue (a + 2 * b + 1) b = (d4R (a + 1) b : ℕ) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
      goodBallotValue_d4R (a + 1) b
  have h2 : goodBallotValue (b + 2 * c + 1) c = (d4R (b + 1) c : ℕ) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
      goodBallotValue_d4R (b + 1) c
  rw [h0, h1, h2]
  simp [d4CWeight]
  ring

theorem goodFunctional_H (a b c : ℕ) :
    goodFunctional (goodIndex a b c) goodHFunction = d4HWeight
      { u := a, v := b, w := c, sum_eq := rfl } := by
  unfold goodHFunction
  rw [goodFunctional_cancel_determinant]
  rw [goodHNumerator_phiPower]
  rw [goodSeparatedProduct_coeff
    (goodBallotAxis 0 (2 * a + c + 1))
    (goodBallotAxis 1 (a + 2 * b))
    (goodBallotAxis 2 (b + 2 * c + 1))
    (goodBallotValue (2 * a + c + 1))
    (goodBallotValue (a + 2 * b))
    (goodBallotValue (b + 2 * c + 1))
    (coeff_goodBallotAxis 0 (2 * a + c + 1))
    (coeff_goodBallotAxis 1 (a + 2 * b))
    (coeff_goodBallotAxis 2 (b + 2 * c + 1))]
  have h0 : goodBallotValue (2 * a + c + 1) a = (d4R (c + 1) a : ℕ) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
      goodBallotValue_d4R (c + 1) a
  have h1 := goodBallotValue_d4R a b
  have h2 : goodBallotValue (b + 2 * c + 1) c = (d4R (b + 1) c : ℕ) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
      goodBallotValue_d4R (b + 1) c
  rw [h0, h1, h2]
  simp [d4HWeight]
  ring

end FiniteDefects

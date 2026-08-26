import FiniteDefects.D4GoodDiagonalExpansion
import FiniteDefects.D4GoodComponentCoefficients

/-! # The three diagonal component generating functions -/

namespace FiniteDefects

open Finset BigOperators Finsupp

theorem goodAggregate_A (degree : ℕ) :
    goodAggregate (fun n => goodFunctional n goodAFunction) degree =
      (d4A0 degree : ℚ) := by
  letI := goodFiberFintype degree
  unfold goodAggregate d4A0
  rw [Nat.cast_sum]
  apply Fintype.sum_equiv (goodFiberEquivSimplex degree)
  intro n
  rw [← goodIndex_coordinates n.1]
  change goodFunctional (goodIndex (n.1 0) (n.1 1) (n.1 2))
    goodAFunction = _
  rw [goodFunctional_A]
  rfl

theorem goodAggregate_C (degree : ℕ) :
    goodAggregate (fun n => goodFunctional n goodCFunction) degree =
      (d4C degree : ℚ) := by
  letI := goodFiberFintype degree
  unfold goodAggregate d4C
  rw [Nat.cast_sum]
  apply Fintype.sum_equiv (goodFiberEquivSimplex degree)
  intro n
  rw [← goodIndex_coordinates n.1]
  change goodFunctional (goodIndex (n.1 0) (n.1 1) (n.1 2))
    goodCFunction = _
  rw [goodFunctional_C]
  rfl

theorem goodAggregate_H (degree : ℕ) :
    goodAggregate (fun n => goodFunctional n goodHFunction) degree =
      (d4H degree : ℚ) := by
  letI := goodFiberFintype degree
  unfold goodAggregate d4H
  rw [Nat.cast_sum]
  apply Fintype.sum_equiv (goodFiberEquivSimplex degree)
  intro n
  rw [← goodIndex_coordinates n.1]
  change goodFunctional (goodIndex (n.1 0) (n.1 1) (n.1 2))
    goodHFunction = _
  rw [goodFunctional_H]
  rfl

theorem goodAggregateSeries_A :
    goodAggregateSeries (fun n => goodFunctional n goodAFunction) =
      d4A0Series := by
  ext degree
  simp [goodAggregate_A]

theorem goodAggregateSeries_C :
    goodAggregateSeries (fun n => goodFunctional n goodCFunction) =
      d4CSeries := by
  ext degree
  simp [goodAggregate_C]

theorem goodAggregateSeries_H :
    goodAggregateSeries (fun n => goodFunctional n goodHFunction) =
      d4HSeries := by
  ext degree
  simp [goodAggregate_H]

noncomputable def goodU : PowerSeries ℚ := 1 + PowerSeries.X

noncomputable def goodCore : PowerSeries ℚ :=
  (1 - 2 * PowerSeries.X) *
    (1 - PowerSeries.X + PowerSeries.X ^ 2)

@[simp] theorem constantCoeff_goodU :
    PowerSeries.constantCoeff ℚ goodU = 1 := by
  simp [goodU]

@[simp] theorem constantCoeff_goodCore :
    PowerSeries.constantCoeff ℚ goodCore = 1 := by
  simp [goodCore]

theorem goodDiagonal_goodNumerator :
    goodDiagonal goodNumerator = goodCore := by
  change goodDiagonalRingHom goodNumerator = _
  unfold goodNumerator goodCore
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    goodDiagonalRingHom_X]
  ring

@[simp] theorem goodDiagonalRingHom_goodNumerator :
    goodDiagonalRingHom goodNumerator = goodCore :=
  goodDiagonal_goodNumerator

theorem goodDiagonal_goodDeterminant :
    goodDiagonal goodDeterminant = goodCore * (goodU ^ 3)⁻¹ := by
  change goodDiagonalRingHom goodDeterminant = _
  unfold goodDeterminant
  simp only [map_mul]
  rw [goodDiagonalRingHom_goodNumerator]
  rw [show goodDiagonalRingHom (goodOnePlus 0)⁻¹ = goodU⁻¹ by
    change goodDiagonal (goodOnePlus 0)⁻¹ = _
    rw [goodDiagonal_inv]
    · unfold goodU
      rw [goodDiagonal_goodOnePlus]
    · simp]
  rw [show goodDiagonalRingHom (goodOnePlus 1)⁻¹ = goodU⁻¹ by
    change goodDiagonal (goodOnePlus 1)⁻¹ = _
    rw [goodDiagonal_inv]
    · unfold goodU
      rw [goodDiagonal_goodOnePlus]
    · simp]
  rw [show goodDiagonalRingHom (goodOnePlus 2)⁻¹ = goodU⁻¹ by
    change goodDiagonal (goodOnePlus 2)⁻¹ = _
    rw [goodDiagonal_inv]
    · unfold goodU
      rw [goodDiagonal_goodOnePlus]
    · simp]
  unfold goodU
  rw [show (1 + PowerSeries.X : PowerSeries ℚ) ^ 3 =
      (1 + PowerSeries.X) * (1 + PowerSeries.X) *
        (1 + PowerSeries.X) by ring]
  rw [PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev]
  ring

theorem goodDiagonal_goodDeterminant_inv :
    goodDiagonal goodDeterminant⁻¹ = goodU ^ 3 * goodCore⁻¹ := by
  rw [goodDiagonal_inv]
  · rw [goodDiagonal_goodDeterminant]
    symm
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
    rw [show (goodU ^ 3 * goodCore⁻¹) *
          (goodCore * (goodU ^ 3)⁻¹) =
          (goodCore⁻¹ * goodCore) *
            (goodU ^ 3 * (goodU ^ 3)⁻¹) by ring]
    rw [PowerSeries.inv_mul_cancel, PowerSeries.mul_inv_cancel]
    · simp
    · simp
    · simp
  · simp

theorem goodDiagonal_goodANumerator :
    goodDiagonal goodANumerator = (1 - PowerSeries.X) ^ 3 := by
  change goodDiagonalRingHom goodANumerator = _
  unfold goodANumerator
  simp only [map_mul, map_sub, map_one, goodDiagonalRingHom_X]
  ring

theorem goodDiagonal_goodCNumerator :
    goodDiagonal goodCNumerator = (1 - PowerSeries.X ^ 2) ^ 3 := by
  change goodDiagonalRingHom goodCNumerator = _
  unfold goodCNumerator
  simp only [map_mul, map_sub, map_one, map_pow, goodDiagonalRingHom_X]
  ring

theorem goodDiagonal_goodHNumerator :
    goodDiagonal goodHNumerator =
      (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X) := by
  change goodDiagonalRingHom goodHNumerator = _
  unfold goodHNumerator
  simp only [map_mul, map_sub, map_one, map_pow, goodDiagonalRingHom_X]
  ring

theorem goodDiagonal_goodAFunction :
    goodDiagonal goodAFunction =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 3 * goodCore⁻¹ := by
  unfold goodAFunction
  rw [goodDiagonal_mul, goodDiagonal_goodANumerator,
    goodDiagonal_goodDeterminant_inv]
  ring

theorem goodDiagonal_goodCFunction :
    goodDiagonal goodCFunction =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 6 * goodCore⁻¹ := by
  unfold goodCFunction
  rw [goodDiagonal_mul, goodDiagonal_goodCNumerator,
    goodDiagonal_goodDeterminant_inv]
  unfold goodU
  ring

theorem goodDiagonal_goodHFunction :
    goodDiagonal goodHFunction =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 5 * goodCore⁻¹ := by
  unfold goodHFunction
  rw [goodDiagonal_mul, goodDiagonal_goodHNumerator,
    goodDiagonal_goodDeterminant_inv]
  unfold goodU
  ring

theorem d4A0_Good_equation :
    fpsCompose goodQ d4A0Series =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 3 * goodCore⁻¹ := by
  have h := congrArg goodDiagonal (goodExpansion_functional goodAFunction)
  rw [goodDiagonal_goodExpansion, goodAggregateSeries_A,
    goodDiagonal_goodAFunction] at h
  exact h

theorem d4C_Good_equation :
    fpsCompose goodQ d4CSeries =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 6 * goodCore⁻¹ := by
  have h := congrArg goodDiagonal (goodExpansion_functional goodCFunction)
  rw [goodDiagonal_goodExpansion, goodAggregateSeries_C,
    goodDiagonal_goodCFunction] at h
  exact h

theorem d4H_Good_equation :
    fpsCompose goodQ d4HSeries =
      (1 - PowerSeries.X) ^ 3 * goodU ^ 5 * goodCore⁻¹ := by
  have h := congrArg goodDiagonal (goodExpansion_functional goodHFunction)
  rw [goodDiagonal_goodExpansion, goodAggregateSeries_H,
    goodDiagonal_goodHFunction] at h
  exact h

end FiniteDefects

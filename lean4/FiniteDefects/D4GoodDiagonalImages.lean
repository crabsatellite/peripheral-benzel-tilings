import FiniteDefects.D4GoodDiagTrunc
import FiniteDefects.D4FPSComposition

/-! # Images of the Good variables under diagonal collapse -/

namespace FiniteDefects

open Finset BigOperators Finsupp

noncomputable def goodQ : PowerSeries ℚ :=
  PowerSeries.X * ((1 + PowerSeries.X : PowerSeries ℚ) ^ 3)⁻¹

@[simp] theorem constantCoeff_goodQ :
    PowerSeries.constantCoeff ℚ goodQ = 0 := by
  simp [goodQ]

theorem constantCoeff_goodDiagonal (f : GoodSeries) :
    PowerSeries.constantCoeff ℚ (goodDiagonal f) =
      MvPowerSeries.constantCoeff (Fin 3) ℚ f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  letI := goodFiberFintype 0
  rw [coeff_goodDiagonal]
  let origin : GoodFiber 0 := ⟨0, by simp [goodTotal]⟩
  have hsingle : ∀ n : GoodFiber 0, n = origin := by
    intro n
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have h := n.2
    rw [goodTotal_coordinates] at h
    fin_cases i <;> simp_all [origin]
  rw [Fintype.sum_eq_single origin]
  intro n hne
  exact (hne (hsingle n)).elim

theorem goodDiagonal_inv (f : GoodSeries)
    (hf : MvPowerSeries.constantCoeff (Fin 3) ℚ f ≠ 0) :
    goodDiagonal f⁻¹ = (goodDiagonal f)⁻¹ := by
  have hdiag : PowerSeries.constantCoeff ℚ (goodDiagonal f) ≠ 0 := by
    rw [constantCoeff_goodDiagonal]
    exact hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one hdiag]
  rw [← goodDiagonal_mul, MvPowerSeries.inv_mul_cancel f hf,
    goodDiagonal_one]

@[simp] theorem goodDiagonal_goodOnePlus (i : Fin 3) :
    goodDiagonal (goodOnePlus i) = 1 + PowerSeries.X := by
  simp [goodOnePlus]

@[simp] theorem goodDiagonalRingHom_X (i : Fin 3) :
    goodDiagonalRingHom (MvPowerSeries.X i) = PowerSeries.X :=
  goodDiagonal_X i

@[simp] theorem goodDiagonalRingHom_goodOnePlus (i : Fin 3) :
    goodDiagonalRingHom (goodOnePlus i) = 1 + PowerSeries.X :=
  goodDiagonal_goodOnePlus i

@[simp] theorem goodDiagonal_goodPhi (i : Fin 3) :
    goodDiagonal (goodPhi i) = (1 + PowerSeries.X) ^ 3 := by
  change goodDiagonalRingHom (goodPhi i) = _
  fin_cases i <;> simp [goodPhi] <;> ring

@[simp] theorem goodDiagonal_goodW (i : Fin 3) :
    goodDiagonal (goodW i) = goodQ := by
  unfold goodW goodQ
  rw [goodDiagonal_mul, goodDiagonal_X, goodDiagonal_inv,
    goodDiagonal_goodPhi]
  simp

@[simp] theorem goodDiagonalRingHom_goodW (i : Fin 3) :
    goodDiagonalRingHom (goodW i) = goodQ :=
  goodDiagonal_goodW i

theorem goodDiagonal_goodWPower (n : GoodIndex) :
    goodDiagonal (goodWPower n) = goodQ ^ goodTotal n := by
  change goodDiagonalRingHom (goodWPower n) = _
  unfold goodWPower goodFamilyPower
  rw [map_prod]
  simp only [map_pow, goodDiagonalRingHom_goodW]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rw [← pow_add, ← pow_add]
  rw [goodTotal_coordinates]
  change goodQ ^ (n 0 + (n 1 + n 2)) =
    goodQ ^ (n 0 + n 1 + n 2)
  congr 1
  omega

end FiniteDefects

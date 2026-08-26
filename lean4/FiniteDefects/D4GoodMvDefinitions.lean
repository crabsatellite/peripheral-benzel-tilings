import FiniteDefects.D4GoodKernelDelta
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # The exact three-variable Lagrange--Good carrier -/

namespace FiniteDefects

open Finset BigOperators Finsupp

abbrev GoodIndex := Fin 3 →₀ ℕ
abbrev GoodSeries := MvPowerSeries (Fin 3) ℚ

noncomputable def goodIndex (a b c : ℕ) : GoodIndex :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem goodIndex_zero (a b c : ℕ) : goodIndex a b c 0 = a := by
  simp [goodIndex]

@[simp] theorem goodIndex_one (a b c : ℕ) : goodIndex a b c 1 = b := by
  simp [goodIndex]

@[simp] theorem goodIndex_two (a b c : ℕ) : goodIndex a b c 2 = c := by
  simp [goodIndex]

theorem goodIndex_coordinates (n : GoodIndex) :
    goodIndex (n 0) (n 1) (n 2) = n := by
  ext i
  fin_cases i <;> simp

def goodTotal (n : GoodIndex) : ℕ := n 0 + n 1 + n 2

theorem goodTotal_coordinates (n : GoodIndex) :
    goodTotal n = n 0 + n 1 + n 2 := rfl

theorem goodTotal_add (left right : GoodIndex) :
    goodTotal (left + right) = goodTotal left + goodTotal right := by
  simp only [goodTotal_coordinates, Finsupp.coe_add, Pi.add_apply]
  omega

noncomputable def goodOnePlus (i : Fin 3) : GoodSeries :=
  1 + MvPowerSeries.X i

noncomputable def goodPhi : Fin 3 → GoodSeries
  | 0 => goodOnePlus 0 ^ 2 * goodOnePlus 1
  | 1 => goodOnePlus 1 ^ 2 * goodOnePlus 2
  | 2 => goodOnePlus 2 ^ 2 * goodOnePlus 0

noncomputable def goodNumerator : GoodSeries :=
  1 - MvPowerSeries.X 0 - MvPowerSeries.X 1 - MvPowerSeries.X 2 +
    MvPowerSeries.X 0 * MvPowerSeries.X 1 +
    MvPowerSeries.X 0 * MvPowerSeries.X 2 +
    MvPowerSeries.X 1 * MvPowerSeries.X 2 -
    2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2)

noncomputable def goodDeterminant : GoodSeries :=
  goodNumerator *
    (goodOnePlus 0)⁻¹ * (goodOnePlus 1)⁻¹ * (goodOnePlus 2)⁻¹

noncomputable def goodW (i : Fin 3) : GoodSeries :=
  MvPowerSeries.X i * (goodPhi i)⁻¹

noncomputable def goodXPower (n : GoodIndex) : GoodSeries :=
  ∏ i : Fin 3, MvPowerSeries.X i ^ n i

noncomputable def goodFamilyPower (family : Fin 3 → GoodSeries)
    (n : GoodIndex) : GoodSeries :=
  ∏ i : Fin 3, family i ^ n i

noncomputable def goodPhiPower (n : GoodIndex) : GoodSeries :=
  goodFamilyPower goodPhi n

noncomputable def goodWPower (n : GoodIndex) : GoodSeries :=
  goodFamilyPower goodW n

noncomputable def goodFunctional (n : GoodIndex) (f : GoodSeries) : ℚ :=
  MvPowerSeries.coeff ℚ n (f * goodPhiPower n * goodDeterminant)

def goodBox (m : GoodIndex) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range (m 0 + 1)).product
    ((Finset.range (m 1 + 1)).product (Finset.range (m 2 + 1)))

noncomputable def goodExpansion (coefficients : GoodIndex → ℚ) : GoodSeries :=
  fun m => ∑ p ∈ goodBox m,
    coefficients (goodIndex p.1 p.2.1 p.2.2) *
      MvPowerSeries.coeff ℚ m (goodWPower (goodIndex p.1 p.2.1 p.2.2))

@[simp] theorem constantCoeff_goodOnePlus (i : Fin 3) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodOnePlus i) = 1 := by
  simp [goodOnePlus]

@[simp] theorem constantCoeff_goodPhi (i : Fin 3) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodPhi i) = 1 := by
  fin_cases i <;> simp [goodPhi]

@[simp] theorem constantCoeff_goodNumerator :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodNumerator = 1 := by
  simp [goodNumerator]

@[simp] theorem constantCoeff_goodDeterminant :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodDeterminant = 1 := by
  simp [goodDeterminant]

@[simp] theorem constantCoeff_goodW (i : Fin 3) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodW i) = 0 := by
  simp [goodW]

@[simp] theorem constantCoeff_goodPhiPower (n : GoodIndex) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodPhiPower n) = 1 := by
  simp [goodPhiPower, goodFamilyPower]

@[simp] theorem constantCoeff_goodWPower (n : GoodIndex) :
    MvPowerSeries.constantCoeff (Fin 3) ℚ (goodWPower n) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [goodWPower, goodFamilyPower]
  · have hi : ∃ i : Fin 3, n i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    obtain ⟨i, hi⟩ := hi
    simp only [goodWPower, goodFamilyPower, map_prod, map_pow,
      constantCoeff_goodW]
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · exact (if_neg hn).symm
    · exact zero_pow hi

end FiniteDefects

import FiniteDefects.D4GoodMvDefinitions

/-! # The three exact multivariate numerators in the d=4 Good evaluation -/

namespace FiniteDefects

noncomputable def goodANumerator : GoodSeries :=
  (1 - MvPowerSeries.X 0) * (1 - MvPowerSeries.X 1) *
    (1 - MvPowerSeries.X 2)

noncomputable def goodCNumerator : GoodSeries :=
  (1 - MvPowerSeries.X 0 ^ 2) * (1 - MvPowerSeries.X 1 ^ 2) *
    (1 - MvPowerSeries.X 2 ^ 2)

noncomputable def goodHNumerator : GoodSeries :=
  (1 - MvPowerSeries.X 0 ^ 2) * (1 - MvPowerSeries.X 1) *
    (1 - MvPowerSeries.X 2 ^ 2)

noncomputable def goodAFunction : GoodSeries :=
  goodANumerator * goodDeterminant⁻¹

noncomputable def goodCFunction : GoodSeries :=
  goodCNumerator * goodDeterminant⁻¹

noncomputable def goodHFunction : GoodSeries :=
  goodHNumerator * goodDeterminant⁻¹

@[simp] theorem constantCoeff_goodANumerator :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodANumerator = 1 := by
  simp [goodANumerator]

@[simp] theorem constantCoeff_goodCNumerator :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodCNumerator = 1 := by
  simp [goodCNumerator]

@[simp] theorem constantCoeff_goodHNumerator :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodHNumerator = 1 := by
  simp [goodHNumerator]

@[simp] theorem constantCoeff_goodAFunction :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodAFunction = 1 := by
  simp [goodAFunction]

@[simp] theorem constantCoeff_goodCFunction :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodCFunction = 1 := by
  simp [goodCFunction]

@[simp] theorem constantCoeff_goodHFunction :
    MvPowerSeries.constantCoeff (Fin 3) ℚ goodHFunction = 1 := by
  simp [goodHFunction]

end FiniteDefects

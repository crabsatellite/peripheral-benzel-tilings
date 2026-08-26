import FiniteDefects.D4GoodFinalEvaluation

/-! # Exact interface for the all-coefficient d=4 generating function -/

namespace FiniteDefects

structure D4GeneratingFunctionEvidence : Prop where
  small_root_constant : PowerSeries.constantCoeff ℚ ternarySeries = 1
  small_root_equation :
    ternarySeries = 1 + PowerSeries.X * ternarySeries ^ 3
  small_root_unique : ∀ S : PowerSeries ℚ,
    PowerSeries.constantCoeff ℚ S = 1 →
    S = 1 + PowerSeries.X * S ^ 3 →
    S = ternarySeries
  exact_generating_function :
    d4TilingSeries =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹

end FiniteDefects

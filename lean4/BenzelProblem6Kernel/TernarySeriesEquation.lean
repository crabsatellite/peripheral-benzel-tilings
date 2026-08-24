import BenzelProblem6Kernel.TernarySmallRoot
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The formal ternary series `T = 1 + X T^3`
-/

namespace BenzelProblem6Kernel

open PowerSeries

noncomputable def ternarySeries : ℚ⟦X⟧ := 1 + ternarySmallRoot

theorem ternarySeries_equation :
    ternarySeries = 1 + X * ternarySeries ^ 3 := by
  calc
    ternarySeries = 1 + ternarySmallRoot := rfl
    _ = 1 + X * (1 + ternarySmallRoot) ^ 3 :=
      congrArg (fun series : ℚ⟦X⟧ => 1 + series)
        (by simpa [ternaryStep] using ternarySmallRoot_equation)
    _ = 1 + X * ternarySeries ^ 3 := rfl

theorem ternarySeries_constantCoeff :
    constantCoeff ℚ ternarySeries = 1 := by
  simp [ternarySeries, ternarySmallRoot_constantCoeff]

theorem ternarySeries_isUnit : IsUnit ternarySeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [ternarySeries_constantCoeff]

theorem goodSmallRoot_is_diagonal :
    goodSmallRoot.a = ternarySmallRoot ∧
      goodSmallRoot.b = ternarySmallRoot ∧
      goodSmallRoot.c = ternarySmallRoot := by
  exact ⟨rfl, rfl, rfl⟩

end BenzelProblem6Kernel

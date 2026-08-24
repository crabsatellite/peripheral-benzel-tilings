import BenzelProblem6Kernel.TernarySeriesEquation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Lagrange--Good Jacobian at the diagonal small root
-/

namespace BenzelProblem6Kernel

open PowerSeries Matrix

noncomputable def goodJacobianNumerator (T : ℚ⟦X⟧) :
    Matrix (Fin 3) (Fin 3) ℚ⟦X⟧ :=
  !![C ℚ 2 - T, 0, -(T - 1);
     -(T - 1), C ℚ 2 - T, 0;
     0, -(T - 1), C ℚ 2 - T]

theorem goodJacobianNumerator_det (T : ℚ⟦X⟧) :
    (goodJacobianNumerator T).det =
      (C ℚ 2 - T) ^ 3 - (T - 1) ^ 3 := by
  classical
  rw [Matrix.det_fin_three]
  simp [goodJacobianNumerator]
  ring

theorem goodJacobian_difference_factorization (T : ℚ⟦X⟧) :
    (C ℚ 2 - T) ^ 3 - (T - 1) ^ 3 =
      (C ℚ 3 - C ℚ 2 * T) *
        (T ^ 2 - C ℚ 3 * T + C ℚ 3) := by
  have h2 : C ℚ (2 : ℚ) = (2 : ℚ⟦X⟧) := by
    exact map_ofNat (C ℚ) 2
  have h3 : C ℚ (3 : ℚ) = (3 : ℚ⟦X⟧) := by
    exact map_ofNat (C ℚ) 3
  rw [h2, h3]
  ring

theorem goodJacobian_at_ternaryRoot :
    (goodJacobianNumerator ternarySeries).det =
      (C ℚ 3 - C ℚ 2 * ternarySeries) *
        (ternarySeries ^ 2 - C ℚ 3 * ternarySeries + C ℚ 3) := by
  rw [goodJacobianNumerator_det,
    goodJacobian_difference_factorization]

theorem goodNumerator_at_ternaryRoot :
    (1 + goodSmallRoot.a) ^ 2 *
      (1 + goodSmallRoot.b) ^ 2 *
      (1 + goodSmallRoot.c) ^ 2 = ternarySeries ^ 6 := by
  simp [goodSmallRoot, ternarySeries]
  ring

theorem goodBallotNumerator_at_ternaryRoot :
    (1 - goodSmallRoot.a) * (1 - goodSmallRoot.b) *
      (1 - goodSmallRoot.c) =
        (C ℚ 2 - ternarySeries) ^ 3 := by
  simp only [goodSmallRoot, ternarySeries]
  have h2 : C ℚ (2 : ℚ) = (2 : ℚ⟦X⟧) := by
    exact map_ofNat (C ℚ) 2
  rw [h2]
  ring

end BenzelProblem6Kernel

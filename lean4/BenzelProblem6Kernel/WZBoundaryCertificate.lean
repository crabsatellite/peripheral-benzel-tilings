import BenzelProblem6Kernel.WZPolynomialCertificate
import Mathlib.Tactic.Linarith

/-!
# Diagonal boundary of the WZ certificate

When `x+y=m+1`, the two outgoing fluxes lie on the `z=-1` edge of the
telescoping extension.  This identity proves that their sum cancels the new
`z=0` layer of the level-`m+1` simplex pointwise.
-/

namespace BenzelProblem6Kernel

theorem wz_boundary_polynomial_certificate (m x y : ℚ)
    (hboundary : x + y = m + 1) :
    3 * (m + 4) * wzLinearDenominator x y *
          wzLeadingCoefficient m * wzKernelPolynomial (m + 1) x y *
          ((2 * y + 2) * (x + 1) * (x + 2)) +
        (m + 6) * (m + 7) *
          (wzB₀ m x y * wzXPolynomial m x y +
            wzB₁ m x y * wzYPolynomial m x y) = 0 := by
  simp only [wzLinearDenominator, wzLeadingCoefficient,
    wzKernelPolynomial, wzB₀, wzB₁, wzXPolynomial, wzYPolynomial]
  have hy : y = m + 1 - x := by linarith
  rw [hy]
  ring

end BenzelProblem6Kernel

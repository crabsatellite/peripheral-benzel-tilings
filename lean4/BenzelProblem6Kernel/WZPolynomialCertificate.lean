import BenzelProblem6Kernel.PathModelRationalKernel
import Mathlib.Tactic.Ring

/-!
# Polynomial core of the two-dimensional WZ certificate

The two displayed polynomials were obtained by exact rational linear algebra.
The theorem at the end is the complete certificate identity after all three
linear certificate denominators have been cleared.  Lean rechecks the identity
by normalization; the search program is not trusted.
-/

namespace BenzelProblem6Kernel

def wzXPolynomial (m x y : ℚ) : ℚ :=
  m ^ 5 * (-24 * x - 78 * y - 24) +
  m ^ 4 * (24 * x ^ 2 + 147 * x * y - 492 * x + 237 * y ^ 2 -
    1260 * y - 516) +
  m ^ 3 * (-60 * x ^ 2 * y + 420 * x ^ 2 - 258 * x * y ^ 2 +
    2244 * x * y - 3972 * x - 240 * y ^ 3 + 2964 * y ^ 2 -
    8118 * y - 4392) +
  m ^ 2 * (54 * x ^ 2 * y ^ 2 - 834 * x ^ 2 * y + 2712 * x ^ 2 +
    135 * x * y ^ 3 - 2715 * x * y ^ 2 + 12885 * x * y -
    15780 * x + 81 * y ^ 4 - 2139 * y ^ 3 + 14145 * y ^ 2 -
    25752 * y - 18492) +
  m * (486 * x ^ 2 * y ^ 2 - 3846 * x ^ 2 * y + 7644 * x ^ 2 +
    945 * x * y ^ 3 - 9471 * x * y ^ 2 + 32820 * x * y -
    30852 * x + 459 * y ^ 4 - 6069 * y ^ 3 + 31326 * y ^ 2 -
    39072 * y - 38496) +
  (1080 * x ^ 2 * y ^ 2 - 5880 * x ^ 2 * y + 7920 * x ^ 2 +
    1458 * x * y ^ 3 - 11334 * x * y ^ 2 + 30888 * x * y -
    23760 * x + 378 * y ^ 4 - 6114 * y ^ 3 + 27036 * y ^ 2 -
    21552 * y - 31680)

def wzYPolynomial (m x y : ℚ) : ℚ :=
  m ^ 5 * (-33 * x - 33 * y - 66) +
  m ^ 4 * (57 * x ^ 2 + 138 * x * y - 537 * x + 60 * y ^ 2 -
    486 * y - 1212) +
  m ^ 3 * (-24 * x ^ 3 - 168 * x ^ 2 * y + 978 * x ^ 2 -
    204 * x * y ^ 2 + 1854 * x * y - 3207 * x - 27 * y ^ 3 +
    735 * y ^ 2 - 2895 * y - 8946) +
  m ^ 2 * (54 * x ^ 3 * y - 402 * x ^ 3 + 135 * x ^ 2 * y ^ 2 -
    1869 * x ^ 2 * y + 6129 * x ^ 2 + 81 * x * y ^ 3 -
    1968 * x * y ^ 2 + 9399 * x * y - 7869 * x - 261 * y ^ 3 +
    3261 * y ^ 2 - 8946 * y - 33024) +
  m * (486 * x ^ 3 * y - 2154 * x ^ 3 + 945 * x ^ 2 * y ^ 2 -
    6915 * x ^ 2 * y + 16464 * x ^ 2 + 459 * x * y ^ 3 -
    6204 * x * y ^ 2 + 21537 * x * y - 4230 * x - 738 * y ^ 3 +
    6402 * y ^ 2 - 14424 * y - 60360) +
  (1080 * x ^ 3 * y - 3720 * x ^ 3 + 1458 * x ^ 2 * y ^ 2 -
    8670 * x ^ 2 * y + 15792 * x ^ 2 + 378 * x * y ^ 3 -
    6816 * x * y ^ 2 + 18822 * x * y + 7416 * x - 504 * y ^ 3 +
    5112 * y ^ 2 - 9216 * y - 42912)

def wzKernelPolynomial (m x y : ℚ) : ℚ :=
  -(m + 6) * (-m * x - m * y - 3 * m + x ^ 2 + x * y + y ^ 2 - 9)

def wzLeadingCoefficient (m : ℚ) : ℚ :=
  2 * (m + 1) * (m + 5) * (m + 6) * (2 * m + 11)

def wzTrailingCoefficient (m : ℚ) : ℚ :=
  3 * (m + 3) * (m + 7) * (3 * m + 10) * (3 * m + 11)

def wzRatioZero (m x y : ℚ) : ℚ :=
  (m - x + 4) * (m - y + 4) * (m - x - y + 1)

def wzRatioOne (m x y : ℚ) : ℚ :=
  (2 * m - x - 2 * y + 4) * (2 * m - x - 2 * y + 3) *
    (m - x + y + 3)

def wzCPolynomial (m x y : ℚ) : ℚ :=
  -wzTrailingCoefficient m * wzKernelPolynomial m x y * wzRatioZero m x y +
    wzLeadingCoefficient m * wzKernelPolynomial (m + 1) x y * wzRatioOne m x y

def wzA₀ (m x y : ℚ) : ℚ :=
  (m - x + 4) * (2 * x + y + 3) * (2 * x + y + 4) *
    (m - x - y + 1)

def wzB₀ (m x y : ℚ) : ℚ :=
  x * (x + y + 3) * (2 * m - x - 2 * y + 3) * (m - x + y + 3)

def wzA₁ (m x y : ℚ) : ℚ :=
  (m - y + 4) * (2 * x + y + 3) * (m - x + y + 3) *
    (m - x - y + 1)

def wzB₁ (m x y : ℚ) : ℚ :=
  y * (x + y + 3) * (2 * m - x - 2 * y + 4) *
    (2 * m - x - 2 * y + 3)

def wzLinearDenominator (x y : ℚ) : ℚ := 2 * x + y + 2

theorem wz_polynomial_certificate (m x y : ℚ) :
    (m + 6) * (m + 7) *
        (wzA₀ m x y * wzXPolynomial m (x + 1) y *
            wzLinearDenominator x y * (wzLinearDenominator x y + 1) -
          wzB₀ m x y * wzXPolynomial m x y *
            (wzLinearDenominator x y + 1) *
            (wzLinearDenominator x y + 2) +
          wzA₁ m x y * wzYPolynomial m x (y + 1) *
            wzLinearDenominator x y * (wzLinearDenominator x y + 2) -
          wzB₁ m x y * wzYPolynomial m x y *
            (wzLinearDenominator x y + 1) *
            (wzLinearDenominator x y + 2)) =
      3 * (m + 4) * wzCPolynomial m x y *
        wzLinearDenominator x y * (wzLinearDenominator x y + 1) *
        (wzLinearDenominator x y + 2) := by
  simp only [wzXPolynomial, wzYPolynomial, wzKernelPolynomial,
    wzLeadingCoefficient, wzTrailingCoefficient, wzRatioZero, wzRatioOne,
    wzCPolynomial, wzA₀, wzB₀, wzA₁, wzB₁, wzLinearDenominator]
  ring

end BenzelProblem6Kernel

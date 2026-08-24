import BenzelProblem6Kernel.WZFluxMatching

/-!
# Boundary flux and the new simplex layer

The WZ extension has a formal `z=-1` diagonal.  We represent that diagonal by
an ordinary factorial expression with `(z+1)! = 0!`.  The checked boundary
polynomial then cancels it pointwise against the `z=0` layer at level `m+1`.
-/

namespace BenzelProblem6Kernel

def wzBoundaryCommonFactor (x y : ℕ) : ℚ :=
  factorialQ (2 * x + y + 2) * factorialQ (2 * y + 1) * factorialQ x /
    (factorialQ x * factorialQ y * factorialQ 0 *
      factorialQ (x + y + 3) * factorialQ (y + 3) * factorialQ (x + 3))

def wzBoundaryRatio (x y : ℕ) : ℚ :=
  ((2 * y + 2 : ℕ) : ℚ) * (x + 1) * (x + 2)

def wzBoundaryIncomingX (m x y : ℕ) : ℚ :=
  wzBoundaryCommonFactor x y * wzB₀ m x y * wzPreX m x y /
    wzLinearDenominator x y

def wzBoundaryIncomingY (m x y : ℕ) : ℚ :=
  wzBoundaryCommonFactor x y * wzB₁ m x y * wzPreY m x y /
    wzLinearDenominator x y

theorem wzBoundaryPre_identity (m x y : ℚ)
    (hboundary : x + y = m + 1)
    (hm4 : m + 4 ≠ 0)
    (hD : wzLinearDenominator x y ≠ 0) :
    wzLeadingCoefficient m * wzKernelPolynomial (m + 1) x y *
          ((2 * y + 2) * (x + 1) * (x + 2)) +
        wzB₀ m x y * wzPreX m x y / wzLinearDenominator x y +
        wzB₁ m x y * wzPreY m x y / wzLinearDenominator x y = 0 := by
  have hcert := wz_boundary_polynomial_certificate m x y hboundary
  calc
    wzLeadingCoefficient m * wzKernelPolynomial (m + 1) x y *
          ((2 * y + 2) * (x + 1) * (x + 2)) +
        wzB₀ m x y * wzPreX m x y / wzLinearDenominator x y +
        wzB₁ m x y * wzPreY m x y / wzLinearDenominator x y =
      (3 * (m + 4) * wzLinearDenominator x y *
            wzLeadingCoefficient m * wzKernelPolynomial (m + 1) x y *
            ((2 * y + 2) * (x + 1) * (x + 2)) +
          (m + 6) * (m + 7) *
            (wzB₀ m x y * wzXPolynomial m x y +
              wzB₁ m x y * wzYPolynomial m x y)) /
        (3 * (m + 4) * wzLinearDenominator x y) := by
      simp only [wzPreX, wzPreY]
      field_simp [hm4, hD]
      ring
    _ = 0 := by rw [hcert]; simp

set_option maxHeartbeats 500000 in
theorem rationalKernelTerm_boundary_transport
    (m x y : ℕ) (hboundary : m + 1 = x + y) :
    rationalKernelTerm x y 0 =
      wzBoundaryCommonFactor x y * wzKernelPolynomial (m + 1) x y *
        wzBoundaryRatio x y := by
  let top : ℚ :=
    factorialQ (2 * x + y + 2) * factorialQ (2 * y + 1) * factorialQ x
  let den : ℚ :=
    factorialQ x * factorialQ y * factorialQ 0 *
      factorialQ (x + y + 3) * factorialQ (y + 3) * factorialQ (x + 3)
  have hN2 := factorialQ_succ (2 * y + 1)
  have hNx := factorialQ_add_two x
  have hleft :
      rationalKernelTerm x y 0 =
        kernelPolynomial x y 0 * (top * wzBoundaryRatio x y) / den := by
    dsimp [rationalKernelTerm, top, den, wzBoundaryRatio]
    rw [show 2 * y + 0 + 2 = (2 * y + 1) + 1 by omega, hN2]
    rw [show 2 * 0 + x + 2 = x + 2 by omega, hNx]
    norm_num [factorialQ]
    ring
  have hcommon : wzBoundaryCommonFactor x y = top / den := by
    rfl
  have hkernel :
      kernelPolynomial x y 0 = wzKernelPolynomial (m + 1) x y := by
    have hq : (m : ℚ) + 1 = (x : ℚ) + y := by
      exact_mod_cast hboundary
    simp only [kernelPolynomial, wzKernelPolynomial]
    push_cast
    rw [hq]
    ring
  have hden : den ≠ 0 := by
    dsimp [den, factorialQ]
    positivity
  rw [hleft, hcommon, ← hkernel]
  field_simp only [hden]
  ring

theorem wz_boundary_cancellation
    (m x y : ℕ) (hboundary : m + 1 = x + y) :
    wzLeadingCoefficient m * rationalKernelTerm x y 0 +
        wzBoundaryIncomingX m x y + wzBoundaryIncomingY m x y = 0 := by
  rw [rationalKernelTerm_boundary_transport m x y hboundary]
  have hboundaryQ : (x : ℚ) + y = (m : ℚ) + 1 := by
    exact_mod_cast hboundary.symm
  have hm4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have hD : wzLinearDenominator (x : ℚ) y ≠ 0 := by
    simp [wzLinearDenominator]
    positivity
  have hpre := wzBoundaryPre_identity (m : ℚ) x y hboundaryQ hm4 hD
  simp only [wzBoundaryIncomingX, wzBoundaryIncomingY]
  change
    wzLeadingCoefficient (m : ℚ) *
          (wzBoundaryCommonFactor x y *
            wzKernelPolynomial ((m : ℚ) + 1) x y * wzBoundaryRatio x y) +
        wzBoundaryCommonFactor x y * wzB₀ (m : ℚ) x y * wzPreX m x y /
            wzLinearDenominator x y +
        wzBoundaryCommonFactor x y * wzB₁ (m : ℚ) x y * wzPreY m x y /
            wzLinearDenominator x y = 0
  push_cast at hpre ⊢
  rw [show wzBoundaryRatio x y =
      ((2 * (y : ℚ) + 2) * ((x : ℚ) + 1) * ((x : ℚ) + 2)) by
    simp [wzBoundaryRatio]]
  calc
    wzLeadingCoefficient ↑m *
          (wzBoundaryCommonFactor x y * wzKernelPolynomial (↑m + 1) ↑x ↑y *
            ((2 * ↑y + 2) * (↑x + 1) * (↑x + 2))) +
        wzBoundaryCommonFactor x y * wzB₀ ↑m ↑x ↑y * wzPreX ↑m ↑x ↑y /
            wzLinearDenominator ↑x ↑y +
        wzBoundaryCommonFactor x y * wzB₁ ↑m ↑x ↑y * wzPreY ↑m ↑x ↑y /
            wzLinearDenominator ↑x ↑y =
      wzBoundaryCommonFactor x y *
        (wzLeadingCoefficient ↑m * wzKernelPolynomial (↑m + 1) ↑x ↑y *
            ((2 * ↑y + 2) * (↑x + 1) * (↑x + 2)) +
          wzB₀ ↑m ↑x ↑y * wzPreX ↑m ↑x ↑y / wzLinearDenominator ↑x ↑y +
          wzB₁ ↑m ↑x ↑y * wzPreY ↑m ↑x ↑y / wzLinearDenominator ↑x ↑y) := by
        ring
    _ = 0 := by rw [hpre]; ring

end BenzelProblem6Kernel

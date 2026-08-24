import BenzelProblem6Kernel.ChiralityGeneratingSeries
import BenzelProblem6Kernel.IndependentArmAlgebra

/-!
# Coefficients of the specialized three-variable constant terms

After the three geometric series are expanded, the coefficient of
`t^(x+y+z)` has Laurent monomial `a^-x b^-y c^-z`.  The remaining factors in
`a`, `b`, and `c` separate, giving the three exact binomial coefficients below.
The negative chirality has the additional factor `(1-a)(1-b)(1-c)`.
-/

namespace BenzelProblem6Kernel

def positiveGoodConstantTermCoefficient (x y z : ℕ) : ℕ :=
  (2 * x + y + 2).choose x *
    (2 * y + z + 2).choose y *
    (2 * z + x + 2).choose z

def ballotLaurentCoefficient (degree exponent : ℕ) : ℕ :=
  degree.choose exponent - choosePred degree exponent

def negativeGoodConstantTermCoefficient (x y z : ℕ) : ℕ :=
  ballotLaurentCoefficient (2 * x + y + 2) x *
    ballotLaurentCoefficient (2 * y + z + 2) y *
    ballotLaurentCoefficient (2 * z + x + 2) z

theorem positiveGoodConstantTermCoefficient_eq (x y z : ℕ) :
    positiveGoodConstantTermCoefficient x y z =
      positiveChiralityCount x y z := rfl

theorem ballotLaurentCoefficient_eq_ballotNumber (degree exponent : ℕ) :
    ballotLaurentCoefficient degree exponent =
      ballotNumber degree exponent := by
  cases exponent <;>
    simp [ballotLaurentCoefficient, ballotNumber, choosePred]

theorem choosePred_le_chirality (minority adjacent : ℕ) :
    choosePred (2 * minority + adjacent + 2) minority ≤
      (2 * minority + adjacent + 2).choose minority := by
  cases minority with
  | zero => simp [choosePred]
  | succ minority =>
      simp only [choosePred]
      have htop : 2 * minority + (adjacent + 2) + 2 =
          2 * (minority + 1) + adjacent + 2 := by omega
      simpa only [htop] using
        choose_le_choose_succ_for_arm minority (adjacent + 2)

theorem negativeGoodConstantTermCoefficient_eq (x y z : ℕ) :
    negativeGoodConstantTermCoefficient x y z =
      negativeChiralityCount x y z := by
  simp only [negativeGoodConstantTermCoefficient,
    ballotLaurentCoefficient_eq_ballotNumber,
    negativeChiralityCount]

noncomputable def positiveGoodConstantTermLevel (degree : ℕ) : ℕ :=
  ∑ sink : SimplexPoint degree,
    positiveGoodConstantTermCoefficient sink.u sink.v sink.w

noncomputable def negativeGoodConstantTermLevel (degree : ℕ) : ℕ :=
  ∑ sink : SimplexPoint degree,
    negativeGoodConstantTermCoefficient sink.u sink.v sink.w

theorem positiveGoodConstantTermLevel_eq (degree : ℕ) :
    positiveGoodConstantTermLevel degree = positiveLevelCount degree := by
  simp only [positiveGoodConstantTermLevel, positiveLevelCount,
    positiveGoodConstantTermCoefficient_eq]

theorem negativeGoodConstantTermLevel_eq (degree : ℕ) :
    negativeGoodConstantTermLevel degree = negativeLevelCount degree := by
  simp only [negativeGoodConstantTermLevel, negativeLevelCount,
    negativeGoodConstantTermCoefficient_eq]

theorem positiveGoodConstantTerm_series_coefficient (degree : ℕ) :
    PowerSeries.coeff ℚ degree positiveChiralityGeneratingSeries =
      (positiveGoodConstantTermLevel degree : ℚ) := by
  rw [coeff_positiveChiralityGeneratingSeries,
    positiveGoodConstantTermLevel_eq]

theorem negativeGoodConstantTerm_series_coefficient (degree : ℕ) :
    PowerSeries.coeff ℚ degree negativeChiralityGeneratingSeries =
      (negativeGoodConstantTermLevel degree : ℚ) := by
  rw [coeff_negativeChiralityGeneratingSeries,
    negativeGoodConstantTermLevel_eq]

end BenzelProblem6Kernel

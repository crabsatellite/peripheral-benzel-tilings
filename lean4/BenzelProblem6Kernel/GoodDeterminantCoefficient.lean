import BenzelProblem6Kernel.SpecializedGoodConstantTerm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The coefficient core of Good's determinant identity

For the cyclic system, after the three denominator factors of the logarithmic
Jacobian are cleared, its numerator is
`(1-a)(1-b)(1-c)-abc`.  The theorem below proves pointwise that the coefficient
of `a^x b^y c^z` in `phi_a^x phi_b^y phi_c^z det J` is one at the origin and
zero everywhere else.  This is the cancellation at the heart of Good's proof.
-/

namespace BenzelProblem6Kernel

def goodReducedTop (majority adjacent : ℕ) : ℕ :=
  (2 * majority + adjacent).pred

def goodMainCoefficient (majority adjacent : ℕ) : ℚ :=
  (goodReducedTop majority adjacent).choose majority

def goodPreviousCoefficient (majority adjacent : ℕ) : ℚ :=
  choosePred (goodReducedTop majority adjacent) majority

def goodDifferenceCoefficient (majority adjacent : ℕ) : ℚ :=
  goodMainCoefficient majority adjacent -
    goodPreviousCoefficient majority adjacent

def goodDeterminantCoefficient (x y z : ℕ) : ℚ :=
  goodDifferenceCoefficient x y *
      goodDifferenceCoefficient y z *
      goodDifferenceCoefficient z x -
    goodPreviousCoefficient x y *
      goodPreviousCoefficient y z *
      goodPreviousCoefficient z x

theorem goodPreviousCoefficient_zero (adjacent : ℕ) :
    goodPreviousCoefficient 0 adjacent = 0 := by
  simp [goodPreviousCoefficient, choosePred]

theorem goodMainCoefficient_zero (adjacent : ℕ) :
    goodMainCoefficient 0 adjacent = 1 := by
  simp [goodMainCoefficient, goodReducedTop]

theorem goodDifferenceCoefficient_zero (adjacent : ℕ) :
    goodDifferenceCoefficient 0 adjacent = 1 := by
  rw [goodDifferenceCoefficient, goodMainCoefficient_zero,
    goodPreviousCoefficient_zero]
  ring

theorem goodDifferenceCoefficient_succ_zero (majority : ℕ) :
    goodDifferenceCoefficient (majority + 1) 0 = 0 := by
  simp only [goodDifferenceCoefficient, goodMainCoefficient,
    goodPreviousCoefficient, goodReducedTop, choosePred]
  have htop : 2 * (majority + 1) + 0 = (2 * majority + 1) + 1 := by
    omega
  rw [htop, Nat.pred_succ]
  rw [Nat.choose_symm_half]
  ring

theorem goodDifference_mul_majority
    (majority adjacent : ℕ) :
    (majority + 1 : ℚ) *
        goodDifferenceCoefficient (majority + 1) (adjacent + 1) =
      (adjacent + 1 : ℚ) *
        goodPreviousCoefficient (majority + 1) (adjacent + 1) := by
  let top := 2 * majority + adjacent + 2
  have hchoose := Nat.choose_succ_right_eq top majority
  have hsub : top - majority = majority + adjacent + 2 := by
    dsimp [top]
    omega
  rw [hsub] at hchoose
  have hchooseQ :
      ((top.choose (majority + 1) : ℕ) : ℚ) * (majority + 1) =
        ((top.choose majority : ℕ) : ℚ) * (majority + adjacent + 2) := by
    exact_mod_cast hchoose
  have htop :
      goodReducedTop (majority + 1) (adjacent + 1) = top := by
    dsimp [goodReducedTop, top]
    omega
  rw [goodDifferenceCoefficient, goodMainCoefficient,
    goodPreviousCoefficient, htop]
  simp only [choosePred]
  linear_combination hchooseQ

theorem goodDeterminantCoefficient_origin :
    goodDeterminantCoefficient 0 0 0 = 1 := by
  simp [goodDeterminantCoefficient, goodDifferenceCoefficient_zero,
    goodPreviousCoefficient_zero]

theorem goodDeterminantCoefficient_zero_of_positive
    (x y z : ℕ) (hpositive : 0 < x + y + z) :
    goodDeterminantCoefficient x y z = 0 := by
  rcases x with _ | x
  · rcases y with _ | y
    · rcases z with _ | z
      · omega
      · simp [goodDeterminantCoefficient,
          goodDifferenceCoefficient_zero,
          goodPreviousCoefficient_zero,
          goodDifferenceCoefficient_succ_zero]
    · rcases z with _ | z
      · simp [goodDeterminantCoefficient,
          goodDifferenceCoefficient_zero,
          goodPreviousCoefficient_zero,
          goodDifferenceCoefficient_succ_zero]
      · simp [goodDeterminantCoefficient,
          goodDifferenceCoefficient_zero,
          goodPreviousCoefficient_zero,
          goodDifferenceCoefficient_succ_zero]
  · rcases y with _ | y
    · simp [goodDeterminantCoefficient,
        goodDifferenceCoefficient_zero,
        goodPreviousCoefficient_zero,
        goodDifferenceCoefficient_succ_zero]
    · rcases z with _ | z
      · simp [goodDeterminantCoefficient,
          goodDifferenceCoefficient_zero,
          goodPreviousCoefficient_zero,
          goodDifferenceCoefficient_succ_zero]
      · have hA := goodDifference_mul_majority x y
        have hB := goodDifference_mul_majority y z
        have hC := goodDifference_mul_majority z x
        have hx : (x + 1 : ℚ) ≠ 0 := by positivity
        have hy : (y + 1 : ℚ) ≠ 0 := by positivity
        have hz : (z + 1 : ℚ) ≠ 0 := by positivity
        have hA' :
            goodDifferenceCoefficient (x + 1) (y + 1) =
              (y + 1 : ℚ) / (x + 1) *
                goodPreviousCoefficient (x + 1) (y + 1) := by
          field_simp [hx]
          nlinarith
        have hB' :
            goodDifferenceCoefficient (y + 1) (z + 1) =
              (z + 1 : ℚ) / (y + 1) *
                goodPreviousCoefficient (y + 1) (z + 1) := by
          field_simp [hy]
          nlinarith
        have hC' :
            goodDifferenceCoefficient (z + 1) (x + 1) =
              (x + 1 : ℚ) / (z + 1) *
                goodPreviousCoefficient (z + 1) (x + 1) := by
          field_simp [hz]
          nlinarith
        rw [goodDeterminantCoefficient, hA', hB', hC']
        field_simp [hx, hy, hz]
        ring

theorem goodDeterminantCoefficient_delta (x y z : ℕ) :
    goodDeterminantCoefficient x y z =
      if x = 0 ∧ y = 0 ∧ z = 0 then 1 else 0 := by
  split_ifs with hzero
  · rcases hzero with ⟨rfl, rfl, rfl⟩
    exact goodDeterminantCoefficient_origin
  · apply goodDeterminantCoefficient_zero_of_positive
    omega

end BenzelProblem6Kernel

import BenzelProblem6Kernel.PathModelCarrier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Rational factorial kernel for the fixed-sink summand

The WZ certificate is most compact after the positive and negative chirality
terms are combined over a common factorial denominator.  This file proves
that the resulting rational kernel is exactly the cast of the already defined
fixed-sink count; it does not introduce a replacement counting object.
-/

namespace BenzelProblem6Kernel

def factorialQ (n : ℕ) : ℚ := (n.factorial : ℚ)

def kernelPolynomial (x y z : ℕ) : ℚ :=
  ((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3) +
    ((x + 3 : ℕ) : ℚ) * (y + 3) * (z + 3)

def rationalKernelTerm (x y z : ℕ) : ℚ :=
  kernelPolynomial x y z *
    factorialQ (2 * x + y + 2) *
    factorialQ (2 * y + z + 2) *
    factorialQ (2 * z + x + 2) /
    (factorialQ x * factorialQ y * factorialQ z *
      factorialQ (x + y + 3) * factorialQ (y + z + 3) *
      factorialQ (z + x + 3))

theorem factorialQ_ne_zero (n : ℕ) : factorialQ n ≠ 0 := by
  unfold factorialQ
  exact_mod_cast n.factorial_ne_zero

theorem factorialQ_pos (n : ℕ) : 0 < factorialQ n := by
  unfold factorialQ
  exact_mod_cast Nat.factorial_pos n

theorem choose_cast_eq_factorial_ratio (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) = factorialQ n / (factorialQ k * factorialQ (n - k)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hq :
      (n.choose k : ℚ) * factorialQ k * factorialQ (n - k) =
        factorialQ n := by
    unfold factorialQ
    exact_mod_cast h
  field_simp [factorialQ_ne_zero]
  nlinarith

theorem ballotNumber_mul_adjacent_denominator (x y : ℕ) :
    (ballotNumber (2 * x + y + 2) x : ℚ) * (x + y + 3) =
      ((2 * x + y + 2).choose x : ℚ) * (y + 3) := by
  rcases x with _ | k
  · simp [ballotNumber]
  · have hchoose := Nat.choose_succ_right_eq (2 * (k + 1) + y + 2) k
    rw [show 2 * (k + 1) + y + 2 - k = k + y + 4 by omega] at hchoose
    have hchooseQ :
        ((2 * (k + 1) + y + 2).choose (k + 1) : ℚ) * (k + 1) =
          ((2 * (k + 1) + y + 2).choose k : ℚ) * (k + y + 4) := by
      exact_mod_cast hchoose
    have hle :
        (2 * (k + 1) + y + 2).choose k ≤
          (2 * (k + 1) + y + 2).choose (k + 1) := by
      apply Nat.le_of_mul_le_mul_right _ (by omega : 0 < k + 1)
      rw [hchoose]
      exact Nat.mul_le_mul_left
        ((2 * (k + 1) + y + 2).choose k) (by omega)
    simp only [ballotNumber]
    rw [Nat.cast_sub hle]
    push_cast
    nlinarith

theorem negativeChiralityCount_ratio (x y z : ℕ) :
    (negativeChiralityCount x y z : ℚ) *
        (((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3)) =
      (positiveChiralityCount x y z : ℚ) *
        (((x + 3 : ℕ) : ℚ) * (y + 3) * (z + 3)) := by
  have hxy := ballotNumber_mul_adjacent_denominator x y
  have hyz := ballotNumber_mul_adjacent_denominator y z
  have hzx := ballotNumber_mul_adjacent_denominator z x
  simp only [negativeChiralityCount, positiveChiralityCount]
  push_cast
  calc
    ((ballotNumber (2 * x + y + 2) x : ℚ) *
        (ballotNumber (2 * y + z + 2) y : ℚ) *
        (ballotNumber (2 * z + x + 2) z : ℚ)) *
        ((x + y + 3 : ℚ) * (y + z + 3) * (z + x + 3)) =
      ((ballotNumber (2 * x + y + 2) x : ℚ) * (x + y + 3)) *
        ((ballotNumber (2 * y + z + 2) y : ℚ) * (y + z + 3)) *
        ((ballotNumber (2 * z + x + 2) z : ℚ) * (z + x + 3)) := by ring
    _ = (((2 * x + y + 2).choose x : ℚ) * (y + 3)) *
        (((2 * y + z + 2).choose y : ℚ) * (z + 3)) *
        (((2 * z + x + 2).choose z : ℚ) * (x + 3)) := by
      rw [hxy, hyz, hzx]
    _ = (((2 * x + y + 2).choose x : ℚ) *
        ((2 * y + z + 2).choose y : ℚ) *
        ((2 * z + x + 2).choose z : ℚ)) *
        ((x + 3) * (y + 3) * (z + 3)) := by ring

theorem fixedSinkCount_eq_rationalKernelTerm (x y z : ℕ) :
    (fixedSinkCount x y z : ℚ) = rationalKernelTerm x y z := by
  have hratio := negativeChiralityCount_ratio x y z
  have hxy := choose_cast_eq_factorial_ratio (2 * x + y + 2) x (by omega)
  have hyz := choose_cast_eq_factorial_ratio (2 * y + z + 2) y (by omega)
  have hzx := choose_cast_eq_factorial_ratio (2 * z + x + 2) z (by omega)
  have hsubxy : 2 * x + y + 2 - x = x + y + 2 := by omega
  have hsubyz : 2 * y + z + 2 - y = y + z + 2 := by omega
  have hsubzx : 2 * z + x + 2 - z = z + x + 2 := by omega
  rw [hsubxy] at hxy
  rw [hsubyz] at hyz
  rw [hsubzx] at hzx
  have hfacxy : factorialQ (x + y + 3) =
      (x + y + 3) * factorialQ (x + y + 2) := by
    rw [show x + y + 3 = (x + y + 2) + 1 by omega]
    simp only [factorialQ, Nat.factorial_succ]
    push_cast
    ring
  have hfacyz : factorialQ (y + z + 3) =
      (y + z + 3) * factorialQ (y + z + 2) := by
    rw [show y + z + 3 = (y + z + 2) + 1 by omega]
    simp only [factorialQ, Nat.factorial_succ]
    push_cast
    ring
  have hfaczx : factorialQ (z + x + 3) =
      (z + x + 3) * factorialQ (z + x + 2) := by
    rw [show z + x + 3 = (z + x + 2) + 1 by omega]
    simp only [factorialQ, Nat.factorial_succ]
    push_cast
    ring
  let smallDen : ℚ :=
    factorialQ x * factorialQ (x + y + 2) *
      (factorialQ y * factorialQ (y + z + 2)) *
      (factorialQ z * factorialQ (z + x + 2))
  let topFac : ℚ :=
    factorialQ (2 * x + y + 2) *
      factorialQ (2 * y + z + 2) *
      factorialQ (2 * z + x + 2)
  let phaseDen : ℚ :=
    ((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3)
  let phaseNum : ℚ :=
    ((x + 3 : ℕ) : ℚ) * (y + 3) * (z + 3)
  have hposFac :
      (positiveChiralityCount x y z : ℚ) * smallDen = topFac := by
    simp only [positiveChiralityCount]
    push_cast
    dsimp [smallDen, topFac]
    rw [hxy, hyz, hzx]
    field_simp [factorialQ_ne_zero]
  have hsmall : smallDen ≠ 0 := by
    dsimp [smallDen]
    have hx := factorialQ_pos x
    have hxy' := factorialQ_pos (x + y + 2)
    have hy := factorialQ_pos y
    have hyz' := factorialQ_pos (y + z + 2)
    have hz := factorialQ_pos z
    have hzx' := factorialQ_pos (z + x + 2)
    positivity
  have hphase : phaseDen ≠ 0 := by
    dsimp [phaseDen]
    positivity
  have hratio' :
      (negativeChiralityCount x y z : ℚ) * phaseDen =
        (positiveChiralityCount x y z : ℚ) * phaseNum := by
    simpa [phaseDen, phaseNum] using hratio
  simp only [fixedSinkCount]
  push_cast
  rw [rationalKernelTerm, kernelPolynomial, hfacxy, hfacyz, hfaczx]
  have hnum :
      (((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3) +
          ((x + 3 : ℕ) : ℚ) * (y + 3) * (z + 3)) *
          factorialQ (2 * x + y + 2) *
          factorialQ (2 * y + z + 2) *
          factorialQ (2 * z + x + 2) =
        (phaseDen + phaseNum) * topFac := by
    dsimp [phaseDen, phaseNum, topFac]
    ring
  have hden :
      factorialQ x * factorialQ y * factorialQ z *
          (((x : ℚ) + y + 3) * factorialQ (x + y + 2)) *
          (((y : ℚ) + z + 3) * factorialQ (y + z + 2)) *
          (((z : ℚ) + x + 3) * factorialQ (z + x + 2)) =
        smallDen * phaseDen := by
    dsimp [smallDen, phaseDen]
    push_cast
    ring
  rw [hnum, hden]
  rw [← hposFac]
  field_simp [hsmall, hphase]
  linear_combination smallDen * hratio'

end BenzelProblem6Kernel

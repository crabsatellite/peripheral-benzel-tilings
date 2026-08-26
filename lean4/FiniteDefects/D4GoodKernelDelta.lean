import FiniteDefects.D4GoodFinalAlgebra
import Mathlib.Data.Nat.Choose.Basic

/-! # The specialized three-variable Good determinant delta -/

namespace FiniteDefects

def d4GoodUpper (energy degree : ℕ) : ℚ :=
  ((energy - 1).choose degree : ℕ)

def d4GoodLower (energy degree : ℕ) : ℚ :=
  match degree with
  | 0 => 0
  | degree + 1 => ((energy - 1).choose degree : ℕ)

def d4GoodKernelDelta (a b c : ℕ) : ℚ :=
  let A := d4GoodUpper (2 * a + c) a
  let A' := d4GoodLower (2 * a + c) a
  let B := d4GoodUpper (a + 2 * b) b
  let B' := d4GoodLower (a + 2 * b) b
  let C := d4GoodUpper (b + 2 * c) c
  let C' := d4GoodLower (b + 2 * c) c
  A * B * C - A' * B * C - A * B' * C - A * B * C' +
    A' * B' * C + A' * B * C' + A * B' * C' - 2 * A' * B' * C'

theorem d4Good_choose_lower_relation (a c : ℕ) (ha : 0 < a) :
    d4GoodLower (2 * a + c) a * (a + c) =
      d4GoodUpper (2 * a + c) a * a := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  simp only [d4GoodLower, d4GoodUpper, Nat.cast_mul, Nat.cast_add]
  norm_cast
  have h := Nat.choose_succ_right_eq (2 * (a + 1) + c - 1) a
  calc
    (2 * (a + 1) + c - 1).choose a * (a + 1 + c) =
        (2 * (a + 1) + c - 1).choose a *
          (2 * (a + 1) + c - 1 - a) := by congr 1; omega
    _ = (2 * (a + 1) + c - 1).choose (a + 1) * (a + 1) := h.symm

theorem d4GoodKernelDelta_all_positive (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    d4GoodKernelDelta a b c = 0 := by
  let A := d4GoodUpper (2 * a + c) a
  let A' := d4GoodLower (2 * a + c) a
  let B := d4GoodUpper (a + 2 * b) b
  let B' := d4GoodLower (a + 2 * b) b
  let C := d4GoodUpper (b + 2 * c) c
  let C' := d4GoodLower (b + 2 * c) c
  have hA : A' * (a + c : ℚ) = A * a := by
    simpa [A, A'] using d4Good_choose_lower_relation a c ha
  have hB : B' * (a + b : ℚ) = B * b := by
    have h := d4Good_choose_lower_relation b a hb
    dsimp [B, B']
    convert h using 1 <;> ring
  have hC : C' * (b + c : ℚ) = C * c := by
    have h := d4Good_choose_lower_relation c b hc
    dsimp [C, C']
    convert h using 1 <;> ring
  have hac : (a + c : ℚ) ≠ 0 := by positivity
  have hab : (a + b : ℚ) ≠ 0 := by positivity
  have hbc : (b + c : ℚ) ≠ 0 := by positivity
  have hA' : A' = A * a / (a + c : ℚ) := by
    apply (eq_div_iff hac).2
    exact hA
  have hB' : B' = B * b / (a + b : ℚ) := by
    apply (eq_div_iff hab).2
    exact hB
  have hC' : C' = C * c / (b + c : ℚ) := by
    apply (eq_div_iff hbc).2
    exact hC
  unfold d4GoodKernelDelta
  change A * B * C - A' * B * C - A * B' * C - A * B * C' +
      A' * B' * C + A' * B * C' + A * B' * C' -
        2 * A' * B' * C' = 0
  rw [hA', hB', hC']
  field_simp
  ring

theorem d4Good_choose_half_succ (n : ℕ) :
    (2 * (n + 1) - 1).choose (n + 1) =
      (2 * (n + 1) - 1).choose n := by
  have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [h]
  exact Nat.choose_symm_half n

theorem d4GoodKernelDelta_eq (a b c : ℕ) :
    d4GoodKernelDelta a b c = if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 0 := by
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c
  · norm_num [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
  · have hsym := d4Good_choose_half_succ c
    have hsymQ :
        (((2 * (c + 1) - 1).choose (c + 1) : ℕ) : ℚ) =
          ((2 * (c + 1) - 1).choose c : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · have hsym := d4Good_choose_half_succ b
    have hsymQ :
        (((2 * (b + 1) - 1).choose (b + 1) : ℕ) : ℚ) =
          ((2 * (b + 1) - 1).choose b : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · have hsym := d4Good_choose_half_succ b
    have hsymQ :
        (((2 * (b + 1) - 1).choose (b + 1) : ℕ) : ℚ) =
          ((2 * (b + 1) - 1).choose b : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · have hsym := d4Good_choose_half_succ a
    have hsymQ :
        (((2 * (a + 1) - 1).choose (a + 1) : ℕ) : ℚ) =
          ((2 * (a + 1) - 1).choose a : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · have hsym := d4Good_choose_half_succ c
    have hsymQ :
        (((2 * (c + 1) - 1).choose (c + 1) : ℕ) : ℚ) =
          ((2 * (c + 1) - 1).choose c : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · have hsym := d4Good_choose_half_succ a
    have hsymQ :
        (((2 * (a + 1) - 1).choose (a + 1) : ℕ) : ℚ) =
          ((2 * (a + 1) - 1).choose a : ℕ) := by exact_mod_cast hsym
    simp [d4GoodKernelDelta, d4GoodUpper, d4GoodLower]
    rw [hsymQ]
    ring
  · exact d4GoodKernelDelta_all_positive (a + 1) (b + 1) (c + 1)
      (by omega) (by omega) (by omega) |>.trans (if_neg (by simp)).symm

end FiniteDefects

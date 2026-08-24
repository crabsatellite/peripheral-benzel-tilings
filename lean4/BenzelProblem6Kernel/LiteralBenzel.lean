import BenzelProblem6Kernel.OwnerCoordinates

/-!
# Literal peripheral benzel boundary
-/

namespace BenzelProblem6Kernel

def inPeripheralBenzel (n : ℕ) (cell : Cell) : Prop :=
  let i := cell.1
  let j := cell.2
  let k : ℤ := 1 - i - j
  let lower : ℤ := 1 - n
  let upper : ℤ := 2 * n - 4
  lower ≤ j - i ∧ j - i ≤ upper ∧
  lower ≤ k - j ∧ k - j ≤ upper ∧
  lower ≤ i - k ∧ i - k ≤ upper

def ownerCell {t : ℕ} (p : SimplexPoint t) : MicroLabel → Cell
  | .zero => (ownerQ p, ownerR p)
  | .one => (ownerQ p + 1, ownerR p)
  | .two => (ownerQ p, ownerR p + 1)

theorem owner_cell_zero_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .zero
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t ∧
    k - j = 3 * (p.v : ℤ) - t + 1 ∧
    i - k = 3 * (p.w : ℤ) - t - 1 := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

theorem owner_cell_one_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .one
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t - 1 ∧
    k - j = 3 * (p.v : ℤ) - t ∧
    i - k = 3 * (p.w : ℤ) - t + 1 := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

theorem owner_cell_two_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .two
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t + 1 ∧
    k - j = 3 * (p.v : ℤ) - t - 1 ∧
    i - k = 3 * (p.w : ℤ) - t := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

theorem owner_zero_mem_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    inPeripheralBenzel n (ownerCell p .zero) ↔ p.v < n - 2 := by
  have hsum : p.u + p.v + p.w = n - 2 := p.sum_eq
  rcases owner_cell_zero_differences p with ⟨h₀, h₁, h₂⟩
  dsimp [inPeripheralBenzel]
  rw [h₀, h₁, h₂]
  omega

theorem owner_one_mem_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    inPeripheralBenzel n (ownerCell p .one) ↔ p.w < n - 2 := by
  have hsum : p.u + p.v + p.w = n - 2 := p.sum_eq
  rcases owner_cell_one_differences p with ⟨h₀, h₁, h₂⟩
  dsimp [inPeripheralBenzel]
  rw [h₀, h₁, h₂]
  omega

theorem owner_two_mem_iff {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    inPeripheralBenzel n (ownerCell p .two) ↔ p.u < n - 2 := by
  have hsum : p.u + p.v + p.w = n - 2 := p.sum_eq
  rcases owner_cell_two_differences p with ⟨h₀, h₁, h₂⟩
  dsimp [inPeripheralBenzel]
  rw [h₀, h₁, h₂]
  omega

end BenzelProblem6Kernel

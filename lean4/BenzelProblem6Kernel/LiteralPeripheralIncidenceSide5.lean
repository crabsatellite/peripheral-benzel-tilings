import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₅_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₅) ∈ literalPeripheralIncidences m ↔
      cell = ((m : ℤ) + 3, 1) ∨
      cell = ((m : ℤ) + 3, 0) ∨
        ∃ r : ℕ, r < m + 3 ∧
          (cell = ((m : ℤ) - r + 3, -(r : ℤ) - 1) ∨
            (r ≠ 0 ∧
              cell = (-((m : ℤ)) + 2 * r - 3,
                (m : ℤ) - r + 4))) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]
  aesop

theorem isInsidePeripheralEdge_side₅_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₅ ↔
      (cell, .side₅) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₅_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed₀ : i = (m : ℤ) + 3 ∧ j = 1
    · exact Or.inl (Prod.ext hfixed₀.1 hfixed₀.2)
    · by_cases hfixed₁ : i = (m : ℤ) + 3 ∧ j = 0
      · exact Or.inr (Or.inl (Prod.ext hfixed₁.1 hfixed₁.2))
      · right; right
        rcases show
            j - i = -((m : ℤ)) - 4 ∨
              i + 2 * j = (m : ℤ) + 5 by omega with
          hfirst | hsecond
        · let r : ℕ := Int.toNat (-(j + 1))
          have hrnonneg : 0 ≤ -(j + 1) := by omega
          have hrcast : (r : ℤ) = -(j + 1) := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
            omega
          refine ⟨r, by omega, Or.inl ?_⟩
          exact Prod.ext (by omega) (by omega)
        · let r : ℕ := Int.toNat ((m : ℤ) - j + 4)
          have hrnonneg : 0 ≤ (m : ℤ) - j + 4 := by omega
          have hrcast : (r : ℤ) = (m : ℤ) - j + 4 := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
          refine ⟨r, by omega, Or.inr ⟨by omega, ?_⟩⟩
          exact Prod.ext (by omega) (by omega)
  · rintro (hfixed₀ | hfixed₁ | ⟨r, hr, hleft | ⟨hrne, hright⟩⟩)
    · have hi := congrArg Prod.fst hfixed₀
      have hj := congrArg Prod.snd hfixed₀
      dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
        neighboringCell]
      omega
    · have hi := congrArg Prod.fst hfixed₁
      have hj := congrArg Prod.snd hfixed₁
      dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
        neighboringCell]
      omega
    · have hi := congrArg Prod.fst hleft
      have hj := congrArg Prod.snd hleft
      dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
        neighboringCell]
      push_cast
      omega
    · have hi := congrArg Prod.fst hright
      have hj := congrArg Prod.snd hright
      dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
        neighboringCell]
      push_cast
      omega

end BenzelProblem6Kernel

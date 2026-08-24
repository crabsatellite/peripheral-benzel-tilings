import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₁_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₁) ∈ literalPeripheralIncidences m ↔
      cell = (-((m : ℤ)) - 3, (m : ℤ) + 3) ∨
      cell = (-((m : ℤ)) - 2, (m : ℤ) + 3) ∨
        ∃ r : ℕ, r < m + 3 ∧
          ((r ≠ 0 ∧
              cell = (-(r : ℤ), -((m : ℤ)) + 2 * r - 3)) ∨
            cell = (-((m : ℤ)) + 2 * r - 1,
              (m : ℤ) - r + 3)) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]
  aesop

theorem isInsidePeripheralEdge_side₁_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₁ ↔
      (cell, .side₁) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₁_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed₀ :
        i = -((m : ℤ)) - 3 ∧ j = (m : ℤ) + 3
    · exact Or.inl (Prod.ext hfixed₀.1 hfixed₀.2)
    · by_cases hfixed₁ :
          i = -((m : ℤ)) - 2 ∧ j = (m : ℤ) + 3
      · exact Or.inr (Or.inl (Prod.ext hfixed₁.1 hfixed₁.2))
      · right; right
        by_cases hnegative : i + j ≤ -1
        · let r : ℕ := Int.toNat (-i)
          have hrnonneg : 0 ≤ -i := by omega
          have hrcast : (r : ℤ) = -i := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
          refine ⟨r, by omega, Or.inl ⟨by omega, ?_⟩⟩
          exact Prod.ext (by omega) (by omega)
        · let r : ℕ := Int.toNat ((m : ℤ) - j + 3)
          have hrnonneg : 0 ≤ (m : ℤ) - j + 3 := by omega
          have hrcast : (r : ℤ) = (m : ℤ) - j + 3 := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
          refine ⟨r, by omega, Or.inr ?_⟩
          exact Prod.ext (by omega) (by omega)
  · rintro (hfixed₀ | hfixed₁ | ⟨r, hr, ⟨hrne, hleft⟩ | hright⟩)
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

import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₃_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₃) ∈ literalPeripheralIncidences m ↔
      cell = (1, -((m : ℤ)) - 3) ∨
      cell = (0, -((m : ℤ)) - 2) ∨
        ∃ r : ℕ, r < m + 3 ∧
          ((r ≠ 0 ∧
              cell = ((m : ℤ) - r + 4, -(r : ℤ))) ∨
            cell = (-(r : ℤ) - 1,
              -((m : ℤ)) + 2 * r - 1)) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]
  aesop

theorem isInsidePeripheralEdge_side₃_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₃ ↔
      (cell, .side₃) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₃_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed₀ : i = 1 ∧ j = -((m : ℤ)) - 3
    · exact Or.inl (Prod.ext hfixed₀.1 hfixed₀.2)
    · by_cases hfixed₁ : i = 0 ∧ j = -((m : ℤ)) - 2
      · exact Or.inr (Or.inl (Prod.ext hfixed₁.1 hfixed₁.2))
      · right; right
        rcases show
            j - i = -((m : ℤ)) - 4 ∨
              2 * i + j = -((m : ℤ)) - 3 by omega with
          hfirst | hsecond
        · let r : ℕ := Int.toNat (-j)
          have hrnonneg : 0 ≤ -j := by omega
          have hrcast : (r : ℤ) = -j := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
          refine ⟨r, by omega, Or.inl ⟨by omega, ?_⟩⟩
          exact Prod.ext (by omega) (by omega)
        · let r : ℕ := Int.toNat (-(i + 1))
          have hrnonneg : 0 ≤ -(i + 1) := by omega
          have hrcast : (r : ℤ) = -(i + 1) := by
            simp [r, Int.toNat_of_nonneg hrnonneg]
            omega
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

import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₄_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₄) ∈ literalPeripheralIncidences m ↔
      cell = ((m : ℤ) + 3, 1) ∨
        ∃ r : ℕ, r < m + 3 ∧
          (cell = ((m : ℤ) - r + 3, -(r : ℤ)) ∨
            cell = ((m : ℤ) - r + 3, -(r : ℤ) - 1)) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]

theorem isInsidePeripheralEdge_side₄_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₄ ↔
      (cell, .side₄) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₄_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed : i = (m : ℤ) + 3 ∧ j = 1
    · exact Or.inl (Prod.ext hfixed.1 hfixed.2)
    · right
      let r : ℕ := Int.toNat ((m : ℤ) - i + 3)
      have hrnonneg : 0 ≤ (m : ℤ) - i + 3 := by omega
      have hrcast : (r : ℤ) = (m : ℤ) - i + 3 := by
        simp [r, Int.toNat_of_nonneg hrnonneg]
      refine ⟨r, by omega, ?_⟩
      rcases show j = -(r : ℤ) ∨ j = -(r : ℤ) - 1 by omega with
        hleft | hright
      · exact Or.inl (Prod.ext (by omega) hleft)
      · exact Or.inr (Prod.ext (by omega) hright)
  · rintro (hfixed | ⟨r, hr, hleft | hright⟩)
    · have hi := congrArg Prod.fst hfixed
      have hj := congrArg Prod.snd hfixed
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

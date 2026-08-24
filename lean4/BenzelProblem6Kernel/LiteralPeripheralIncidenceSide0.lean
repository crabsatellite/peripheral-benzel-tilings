import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₀_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₀) ∈ literalPeripheralIncidences m ↔
      cell = (-((m : ℤ)) - 3, (m : ℤ) + 3) ∨
        ∃ r : ℕ, r < m + 3 ∧
          (cell = (-((m : ℤ)) + 2 * r - 2,
              (m : ℤ) - r + 3) ∨
            cell = (-((m : ℤ)) + 2 * r - 1,
              (m : ℤ) - r + 3)) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]

theorem isInsidePeripheralEdge_side₀_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₀ ↔
      (cell, .side₀) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₀_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed :
        i = -((m : ℤ)) - 3 ∧ j = (m : ℤ) + 3
    · exact Or.inl (Prod.ext hfixed.1 hfixed.2)
    · right
      let r : ℕ := Int.toNat ((m : ℤ) - j + 3)
      have hrnonneg : 0 ≤ (m : ℤ) - j + 3 := by omega
      have hrcast : (r : ℤ) = (m : ℤ) - j + 3 := by
        simp [r, Int.toNat_of_nonneg hrnonneg]
      refine ⟨r, by omega, ?_⟩
      rcases show
          i = -((m : ℤ)) + 2 * (r : ℤ) - 2 ∨
            i = -((m : ℤ)) + 2 * (r : ℤ) - 1 by omega with
        hleft | hright
      · exact Or.inl (Prod.ext hleft (by omega))
      · exact Or.inr (Prod.ext hright (by omega))
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

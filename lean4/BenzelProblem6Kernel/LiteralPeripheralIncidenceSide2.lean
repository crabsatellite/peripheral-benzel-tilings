import BenzelProblem6Kernel.LiteralPeripheralIncidences

namespace BenzelProblem6Kernel

theorem mem_literalPeripheralIncidences_side₂_iff
    (m : ℕ) (cell : Cell) :
    (cell, .side₂) ∈ literalPeripheralIncidences m ↔
      cell = (1, -((m : ℤ)) - 3) ∨
        ∃ r : ℕ, r < m + 3 ∧
          (cell = (-(r : ℤ), -((m : ℤ)) + 2 * r - 2) ∨
            cell = (-(r : ℤ) - 1,
              -((m : ℤ)) + 2 * r - 1)) := by
  simp [literalPeripheralIncidences, peripheralFixed₀,
    peripheralLong₁, peripheralLong₁Entry,
    peripheralFixed₂, peripheralLong₃, peripheralLong₃Entry,
    peripheralFixed₄, peripheralLong₅, peripheralLong₅Entry,
    List.mem_flatMap]

theorem isInsidePeripheralEdge_side₂_iff_mem
    (m : ℕ) (cell : Cell) :
    IsInsidePeripheralEdge m cell .side₂ ↔
      (cell, .side₂) ∈ literalPeripheralIncidences m := by
  rcases cell with ⟨i, j⟩
  rw [mem_literalPeripheralIncidences_side₂_iff]
  constructor
  · intro hedge
    dsimp [IsInsidePeripheralEdge, inPeripheralBenzel,
      neighboringCell] at hedge
    by_cases hfixed : i = 1 ∧ j = -((m : ℤ)) - 3
    · exact Or.inl (Prod.ext hfixed.1 hfixed.2)
    · right
      rcases show
          j + (m : ℤ) + 2 * i = -2 ∨
            j + (m : ℤ) + 2 * i = -3 by omega with
        hfirst | hsecond
      · let r : ℕ := Int.toNat (-i)
        have hrnonneg : 0 ≤ -i := by omega
        have hrcast : (r : ℤ) = -i := by
          simp [r, Int.toNat_of_nonneg hrnonneg]
        exact ⟨r, by omega, Or.inl (Prod.ext (by omega) (by omega))⟩
      · let r : ℕ := Int.toNat (-(i + 1))
        have hrnonneg : 0 ≤ -(i + 1) := by omega
        have hrcast : (r : ℤ) = -(i + 1) := by
          simp [r, Int.toNat_of_nonneg hrnonneg]
          omega
        exact ⟨r, by omega, Or.inr (Prod.ext (by omega) (by omega))⟩
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

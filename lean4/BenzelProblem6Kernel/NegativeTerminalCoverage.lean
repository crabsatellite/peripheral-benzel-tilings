import BenzelProblem6Kernel.WordBoneIncidence

/-!
# Coverage supplied by the three negative-chirality terminal bones
-/

namespace BenzelProblem6Kernel

theorem negativeLabelZeroTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z)
    (label : MicroLabel) (hne : label ≠ .zero) :
    let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelZeroPrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (negativeLabelZeroTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [negativeLabelZeroTerminalBone] using
    reverseBonePlacement_covers_source
      (labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .zero .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelZero_terminal_step x y z path)
      (by
        simpa using labelZeroPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .zero)
      label (by simpa using hne)

theorem negativeLabelZeroTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z) :
    PlacementCovers (negativeLabelZeroTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .zero,
        sinkPoint_ownerCell_mem x y z .zero⟩ := by
  simpa [negativeLabelZeroTerminalBone] using
    reverseBonePlacement_covers_target
      (labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .zero .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelZero_terminal_step x y z path)
      (by
        simpa using labelZeroPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .zero)

theorem negativeLabelOneTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x)
    (label : MicroLabel) (hne : label ≠ .one) :
    let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelOnePrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (negativeLabelOneTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [negativeLabelOneTerminalBone] using
    reverseBonePlacement_covers_source
      (labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .one .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelOne_terminal_step x y z path)
      (by
        simpa using labelOnePrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .one)
      label (by simpa using hne)

theorem negativeLabelOneTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x) :
    PlacementCovers (negativeLabelOneTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .one,
        sinkPoint_ownerCell_mem x y z .one⟩ := by
  simpa [negativeLabelOneTerminalBone] using
    reverseBonePlacement_covers_target
      (labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .one .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelOne_terminal_step x y z path)
      (by
        simpa using labelOnePrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .one)

theorem negativeLabelTwoTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y)
    (label : MicroLabel) (hne : label ≠ .two) :
    let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelTwoPrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (negativeLabelTwoTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [negativeLabelTwoTerminalBone] using
    reverseBonePlacement_covers_source
      (labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .two .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelTwo_terminal_step x y z path)
      (by
        simpa using labelTwoPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .two)
      label (by simpa using hne)

theorem negativeLabelTwoTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y) :
    PlacementCovers (negativeLabelTwoTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .two,
        sinkPoint_ownerCell_mem x y z .two⟩ := by
  simpa [negativeLabelTwoTerminalBone] using
    reverseBonePlacement_covers_target
      (labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .two .minority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        negative_labelTwo_terminal_step x y z path)
      (by
        simpa using labelTwoPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .two)

end BenzelProblem6Kernel

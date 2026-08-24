import BenzelProblem6Kernel.WordBoneIncidence

/-!
# Coverage supplied by the three positive-chirality terminal bones
-/

namespace BenzelProblem6Kernel

theorem positiveLabelZeroTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1))
    (label : MicroLabel) (hne : label ≠ .zero) :
    let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelZeroPrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (positiveLabelZeroTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [positiveLabelZeroTerminalBone] using
    reverseBonePlacement_covers_source
      (labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .zero .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelZero_terminal_step x y z path)
      (by
        simpa using labelZeroPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .zero)
      label (by simpa using hne)

theorem positiveLabelZeroTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1)) :
    PlacementCovers (positiveLabelZeroTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .zero,
        sinkPoint_ownerCell_mem x y z .zero⟩ := by
  simpa [positiveLabelZeroTerminalBone] using
    reverseBonePlacement_covers_target
      (labelZeroPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .zero .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelZero_terminal_step x y z path)
      (by
        simpa using labelZeroPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .zero)

theorem positiveLabelOneTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1))
    (label : MicroLabel) (hne : label ≠ .one) :
    let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelOnePrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (positiveLabelOneTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [positiveLabelOneTerminalBone] using
    reverseBonePlacement_covers_source
      (labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .one .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelOne_terminal_step x y z path)
      (by
        simpa using labelOnePrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .one)
      label (by simpa using hne)

theorem positiveLabelOneTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1)) :
    PlacementCovers (positiveLabelOneTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .one,
        sinkPoint_ownerCell_mem x y z .one⟩ := by
  simpa [positiveLabelOneTerminalBone] using
    reverseBonePlacement_covers_target
      (labelOnePrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .one .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelOne_terminal_step x y z path)
      (by
        simpa using labelOnePrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .one)

theorem positiveLabelTwoTerminal_covers_source (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1))
    (label : MicroLabel) (hne : label ≠ .two) :
    let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    let hmem : inPeripheralBenzel (x + y + z + 5)
        (ownerCell source label) :=
      labelTwoPrefix_source_cells_mem_of_prefix (m := x + y + z)
        path (recursiveBallotWord path) List.prefix_rfl
        (by omega) (by omega) label hne
    PlacementCovers (positiveLabelTwoTerminalBone x y z path)
      ⟨ownerCell source label, hmem⟩ := by
  dsimp
  simpa [positiveLabelTwoTerminalBone] using
    reverseBonePlacement_covers_source
      (labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .two .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelTwo_terminal_step x y z path)
      (by
        simpa using labelTwoPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .two)
      label (by simpa using hne)

theorem positiveLabelTwoTerminal_covers_sink (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1)) :
    PlacementCovers (positiveLabelTwoTerminalBone x y z path)
      ⟨ownerCell (sinkPoint x y z) .two,
        sinkPoint_ownerCell_mem x y z .two⟩ := by
  simpa [positiveLabelTwoTerminalBone] using
    reverseBonePlacement_covers_target
      (labelTwoPrefixSimplexPoint (t := x + y + z + 3)
        path (recursiveBallotWord path) List.prefix_rfl (by omega))
      (sinkPoint x y z) (goodBoneClassOfMove .two .majority)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelTwo_terminal_step x y z path)
      (by
        simpa using labelTwoPrefix_source_cells_mem_of_prefix
          (m := x + y + z) path (recursiveBallotWord path) List.prefix_rfl
            (by omega) (by omega))
      (by simpa using sinkPoint_ownerCell_mem x y z .two)

end BenzelProblem6Kernel

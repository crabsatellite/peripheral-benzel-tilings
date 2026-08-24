import BenzelProblem6Kernel.SimplexOwnerStepConverse

/-!
# Reconstructing the six terminal bones joining the arms to their sink
-/

namespace BenzelProblem6Kernel

theorem labelZeroPrefix_source_cells_mem_of_prefix {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .zero →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelZeroPrefixSimplexPoint (t := m + 3)
          path pre hp (by omega)) label) := by
  intro label hne
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · exact (hne rfl).elim
  · rw [owner_one_mem_iff (by omega)]
    have hcoord :
        ((labelZeroPrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).w : ℤ) = minorityCount pre := by
      simpa only [labelZeroPrefixPoint] using
        (labelZeroPrefixSimplexPoint_w (t := m + 3)
          path pre hp (by omega))
    omega
  · rw [owner_two_mem_iff (by omega)]
    have hcoord :
        ((labelZeroPrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).u : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelZeroPrefixPoint] using
        (labelZeroPrefixSimplexPoint_u (t := m + 3)
          path pre hp (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hp
    omega

theorem labelOnePrefix_source_cells_mem_of_prefix {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .one →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelOnePrefixSimplexPoint (t := m + 3)
          path pre hp (by omega)) label) := by
  intro label hne
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · rw [owner_zero_mem_iff (by omega)]
    have hcoord :
        ((labelOnePrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).v : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelOnePrefixPoint] using
        (labelOnePrefixSimplexPoint_v (t := m + 3)
          path pre hp (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hp
    omega
  · exact (hne rfl).elim
  · rw [owner_two_mem_iff (by omega)]
    have hcoord :
        ((labelOnePrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).u : ℤ) = minorityCount pre := by
      simpa only [labelOnePrefixPoint] using
        (labelOnePrefixSimplexPoint_u (t := m + 3)
          path pre hp (by omega))
    omega

theorem labelTwoPrefix_source_cells_mem_of_prefix {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .two →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelTwoPrefixSimplexPoint (t := m + 3)
          path pre hp (by omega)) label) := by
  intro label hne
  have hmajor := majorityCount_prefix_le hp
  have hminor := minorityCount_prefix_le hp
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · rw [owner_zero_mem_iff (by omega)]
    have hcoord :
        ((labelTwoPrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).v : ℤ) = minorityCount pre := by
      simpa only [labelTwoPrefixPoint] using
        (labelTwoPrefixSimplexPoint_v (t := m + 3)
          path pre hp (by omega))
    omega
  · rw [owner_one_mem_iff (by omega)]
    have hcoord :
        ((labelTwoPrefixSimplexPoint (t := m + 3) path pre hp
          (by omega)).w : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelTwoPrefixPoint] using
        (labelTwoPrefixSimplexPoint_w (t := m + 3)
          path pre hp (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hp
    omega
  · exact (hne rfl).elim

theorem sinkPoint_ownerCell_mem (x y z : ℕ) (label : MicroLabel) :
    inPeripheralBenzel (x + y + z + 5)
      (ownerCell (sinkPoint x y z) label) := by
  rcases label with _ | _ | _
  · rw [owner_zero_mem_iff (by omega)]
    simp [sinkPoint]
    omega
  · rw [owner_one_mem_iff (by omega)]
    simp [sinkPoint]
    omega
  · rw [owner_two_mem_iff (by omega)]
    simp [sinkPoint]
    omega

theorem positive_labelZero_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1)) :
    let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepC =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepC_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelZeroPrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelZeroPrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelZeroPrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelZeroPrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

theorem negative_labelZero_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z) :
    let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepA =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepA_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelZeroPrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelZeroPrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelZeroPrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelZeroPrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

theorem positive_labelOne_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1)) :
    let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepB =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepB_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelOnePrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelOnePrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelOnePrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelOnePrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

theorem negative_labelOne_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x) :
    let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepC =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepC_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelOnePrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelOnePrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelOnePrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelOnePrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

theorem positive_labelTwo_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1)) :
    let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepA =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepA_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelTwoPrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelTwoPrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelTwoPrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelTwoPrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

theorem negative_labelTwo_terminal_step (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y) :
    let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
      path (recursiveBallotWord path) List.prefix_rfl (by omega)
    addCell (ownerQ source, ownerR source) stepB =
      (ownerQ (sinkPoint x y z), ownerR (sinkPoint x y z)) := by
  dsimp
  apply owner_stepB_of_simplex_coordinates
  have hmajor := recursiveBallotWord_majority path
  have hminor := recursiveBallotWord_minority path
  have hu := labelTwoPrefixSimplexPoint_u (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hv := labelTwoPrefixSimplexPoint_v (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  have hw := labelTwoPrefixSimplexPoint_w (t := x + y + z + 3)
    path (recursiveBallotWord path) List.prefix_rfl (by omega)
  simp only [labelTwoPrefixPoint] at hu hv hw
  simp [sinkPoint]
  omega

noncomputable def positiveLabelZeroTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (x + z + 1) (z + 1)) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

noncomputable def negativeLabelZeroTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (x + z + 2) z) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

noncomputable def positiveLabelOneTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (x + y + 1) (x + 1)) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

noncomputable def negativeLabelOneTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (x + y + 2) x) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

noncomputable def positiveLabelTwoTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (y + z + 1) (y + 1)) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

noncomputable def negativeLabelTwoTerminalBone (x y z : ℕ)
    (path : RecursiveBallot (y + z + 2) y) :
    LiteralPlacement (x + y + z) :=
  reverseBonePlacement
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

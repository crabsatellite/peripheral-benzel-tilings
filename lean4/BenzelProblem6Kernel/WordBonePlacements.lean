import BenzelProblem6Kernel.WordPrefixEdges

/-!
# Finite lists of reconstructed bones along a complete arm word
-/

namespace BenzelProblem6Kernel

noncomputable def labelZeroWordBonePlacements {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    List (LiteralPlacement m) :=
  (wordPrefixEdges (recursiveBallotWord path)).attach.map fun datum =>
    labelZeroPrefixBonePlacement path datum.1.1 datum.1.2
      (wordPrefixEdges_target_prefix _ datum.1 datum.2) hup hdown

noncomputable def labelOneWordBonePlacements {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    List (LiteralPlacement m) :=
  (wordPrefixEdges (recursiveBallotWord path)).attach.map fun datum =>
    labelOnePrefixBonePlacement path datum.1.1 datum.1.2
      (wordPrefixEdges_target_prefix _ datum.1 datum.2) hup hdown

noncomputable def labelTwoWordBonePlacements {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    List (LiteralPlacement m) :=
  (wordPrefixEdges (recursiveBallotWord path)).attach.map fun datum =>
    labelTwoPrefixBonePlacement path datum.1.1 datum.1.2
      (wordPrefixEdges_target_prefix _ datum.1 datum.2) hup hdown

@[simp] theorem labelZeroWordBonePlacements_length {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    (labelZeroWordBonePlacements path hup hdown).length = up + down := by
  simp [labelZeroWordBonePlacements, recursiveBallotWord_length]

@[simp] theorem labelOneWordBonePlacements_length {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    (labelOneWordBonePlacements path hup hdown).length = up + down := by
  simp [labelOneWordBonePlacements, recursiveBallotWord_length]

@[simp] theorem labelTwoWordBonePlacements_length {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3) :
    (labelTwoWordBonePlacements path hup hdown).length = up + down := by
  simp [labelTwoWordBonePlacements, recursiveBallotWord_length]

theorem mem_labelZeroWordBonePlacements_iff {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (placement : LiteralPlacement m) :
    placement ∈ labelZeroWordBonePlacements path hup hdown ↔
      ∃ (pre : List BallotMove) (move : BallotMove)
        (hp : pre ++ [move] <+: recursiveBallotWord path),
        placement = labelZeroPrefixBonePlacement path pre move hp hup hdown := by
  constructor
  · intro hmem
    simp only [labelZeroWordBonePlacements, List.mem_map] at hmem
    obtain ⟨datum, hdatum, rfl⟩ := hmem
    exact ⟨datum.1.1, datum.1.2,
      wordPrefixEdges_target_prefix _ datum.1 datum.2, rfl⟩
  · rintro ⟨pre, move, hp, rfl⟩
    have hpair : (pre, move) ∈ wordPrefixEdges (recursiveBallotWord path) := by
      rcases hp with ⟨suffix, hword⟩
      apply wordPrefixEdges_mem_of_decomposition
        (recursiveBallotWord path) pre suffix move
      simpa [List.append_assoc] using hword.symm
    simp only [labelZeroWordBonePlacements, List.mem_map]
    refine ⟨⟨(pre, move), hpair⟩, ?_, ?_⟩
    · simp
    · rfl

theorem mem_labelOneWordBonePlacements_iff {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (placement : LiteralPlacement m) :
    placement ∈ labelOneWordBonePlacements path hup hdown ↔
      ∃ (pre : List BallotMove) (move : BallotMove)
        (hp : pre ++ [move] <+: recursiveBallotWord path),
        placement = labelOnePrefixBonePlacement path pre move hp hup hdown := by
  constructor
  · intro hmem
    simp only [labelOneWordBonePlacements, List.mem_map] at hmem
    obtain ⟨datum, hdatum, rfl⟩ := hmem
    exact ⟨datum.1.1, datum.1.2,
      wordPrefixEdges_target_prefix _ datum.1 datum.2, rfl⟩
  · rintro ⟨pre, move, hp, rfl⟩
    have hpair : (pre, move) ∈ wordPrefixEdges (recursiveBallotWord path) := by
      rcases hp with ⟨suffix, hword⟩
      apply wordPrefixEdges_mem_of_decomposition
        (recursiveBallotWord path) pre suffix move
      simpa [List.append_assoc] using hword.symm
    simp only [labelOneWordBonePlacements, List.mem_map]
    refine ⟨⟨(pre, move), hpair⟩, ?_, ?_⟩
    · simp
    · rfl

theorem mem_labelTwoWordBonePlacements_iff {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (placement : LiteralPlacement m) :
    placement ∈ labelTwoWordBonePlacements path hup hdown ↔
      ∃ (pre : List BallotMove) (move : BallotMove)
        (hp : pre ++ [move] <+: recursiveBallotWord path),
        placement = labelTwoPrefixBonePlacement path pre move hp hup hdown := by
  constructor
  · intro hmem
    simp only [labelTwoWordBonePlacements, List.mem_map] at hmem
    obtain ⟨datum, hdatum, rfl⟩ := hmem
    exact ⟨datum.1.1, datum.1.2,
      wordPrefixEdges_target_prefix _ datum.1 datum.2, rfl⟩
  · rintro ⟨pre, move, hp, rfl⟩
    have hpair : (pre, move) ∈ wordPrefixEdges (recursiveBallotWord path) := by
      rcases hp with ⟨suffix, hword⟩
      apply wordPrefixEdges_mem_of_decomposition
        (recursiveBallotWord path) pre suffix move
      simpa [List.append_assoc] using hword.symm
    simp only [labelTwoWordBonePlacements, List.mem_map]
    refine ⟨⟨(pre, move), hpair⟩, ?_, ?_⟩
    · simp
    · rfl

end BenzelProblem6Kernel

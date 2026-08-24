import BenzelProblem6Kernel.PrefixPointInjectivity

/-!
# Incoming and outgoing reconstructed bones at word-prefix vertices
-/

namespace BenzelProblem6Kernel

theorem exists_next_of_prefix_ne {α : Type} {pre word : List α}
    (hp : pre <+: word) (hne : pre ≠ word) :
    ∃ move suffix, word = pre ++ move :: suffix := by
  rcases hp with ⟨tail, rfl⟩
  cases tail with
  | nil => exact (hne (by simp)).elim
  | cons move suffix => exact ⟨move, suffix, rfl⟩

theorem exists_init_last {α : Type} {word : List α} (hne : word ≠ []) :
    ∃ init last, word = init ++ [last] := by
  induction word with
  | nil => exact (hne rfl).elim
  | cons head tail ih =>
      by_cases htail : tail = []
      · subst tail
        exact ⟨[], head, rfl⟩
      · obtain ⟨init, last, hlast⟩ := ih htail
        exact ⟨head :: init, last, by simp [hlast]⟩

theorem labelZeroWord_outgoing_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ recursiveBallotWord path)
    (label : MicroLabel) (hlabel : label ≠ .zero) :
    let source := labelZeroPrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell source label) :=
      labelZeroPrefix_source_cells_mem_of_prefix path pre hp hup hdown
        label hlabel
    ∃ placement ∈ labelZeroWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell source label, hmem⟩ := by
  dsimp
  obtain ⟨move, suffix, hword⟩ := exists_next_of_prefix_ne hp hne
  have hpEdge : pre ++ [move] <+: recursiveBallotWord path := by
    rw [hword]
    simp
  let placement := labelZeroPrefixBonePlacement path pre move hpEdge hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelZeroWordBonePlacements_iff path hup hdown placement).2
    exact ⟨pre, move, hpEdge, rfl⟩
  · simpa [placement, labelZeroPrefixBonePlacement] using
      reverseBonePlacement_covers_source
        (labelZeroPrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hpEdge) (by omega))
        (labelZeroPrefixSimplexPoint (t := m + 3) path (pre ++ [move])
          hpEdge (by omega))
        (goodBoneClassOfMove .zero move)
        (labelZeroPrefix_owner_step path pre move hpEdge (by omega))
        (by
          intro candidate hc
          apply labelZeroPrefix_source_cells_mem path pre move hpEdge
            hup hdown candidate
          simpa using hc)
        (by simpa using labelZeroPrefix_target_cell_mem path pre move hpEdge hup)
        label (by simpa using hlabel)

theorem labelZeroWord_incoming_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ []) :
    let target := labelZeroPrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell target .zero) := by
      obtain ⟨init, move, hpre⟩ := exists_init_last hne
      subst pre
      exact labelZeroPrefix_target_cell_mem path init move hp hup
    ∃ placement ∈ labelZeroWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell target .zero, hmem⟩ := by
  dsimp
  obtain ⟨init, move, hpre⟩ := exists_init_last hne
  subst pre
  let placement := labelZeroPrefixBonePlacement path init move hp hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelZeroWordBonePlacements_iff path hup hdown placement).2
    exact ⟨init, move, hp, rfl⟩
  · simpa [placement, labelZeroPrefixBonePlacement] using
      reverseBonePlacement_covers_target
        (labelZeroPrefixSimplexPoint (t := m + 3) path init
          ((List.prefix_append init [move]).trans hp) (by omega))
        (labelZeroPrefixSimplexPoint (t := m + 3) path (init ++ [move])
          hp (by omega))
        (goodBoneClassOfMove .zero move)
        (labelZeroPrefix_owner_step path init move hp (by omega))
        (by
          intro candidate hc
          apply labelZeroPrefix_source_cells_mem path init move hp
            hup hdown candidate
          simpa using hc)
        (by simpa using labelZeroPrefix_target_cell_mem path init move hp hup)

theorem labelOneWord_outgoing_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ recursiveBallotWord path)
    (label : MicroLabel) (hlabel : label ≠ .one) :
    let source := labelOnePrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell source label) :=
      labelOnePrefix_source_cells_mem_of_prefix path pre hp hup hdown
        label hlabel
    ∃ placement ∈ labelOneWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell source label, hmem⟩ := by
  dsimp
  obtain ⟨move, suffix, hword⟩ := exists_next_of_prefix_ne hp hne
  have hpEdge : pre ++ [move] <+: recursiveBallotWord path := by
    rw [hword]
    simp
  let placement := labelOnePrefixBonePlacement path pre move hpEdge hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelOneWordBonePlacements_iff path hup hdown placement).2
    exact ⟨pre, move, hpEdge, rfl⟩
  · simpa [placement, labelOnePrefixBonePlacement] using
      reverseBonePlacement_covers_source
        (labelOnePrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hpEdge) (by omega))
        (labelOnePrefixSimplexPoint (t := m + 3) path (pre ++ [move])
          hpEdge (by omega))
        (goodBoneClassOfMove .one move)
        (labelOnePrefix_owner_step path pre move hpEdge (by omega))
        (by
          intro candidate hc
          apply labelOnePrefix_source_cells_mem path pre move hpEdge
            hup hdown candidate
          simpa using hc)
        (by simpa using labelOnePrefix_target_cell_mem path pre move hpEdge hup)
        label (by simpa using hlabel)

theorem labelOneWord_incoming_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ []) :
    let target := labelOnePrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell target .one) := by
      obtain ⟨init, move, hpre⟩ := exists_init_last hne
      subst pre
      exact labelOnePrefix_target_cell_mem path init move hp hup
    ∃ placement ∈ labelOneWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell target .one, hmem⟩ := by
  dsimp
  obtain ⟨init, move, hpre⟩ := exists_init_last hne
  subst pre
  let placement := labelOnePrefixBonePlacement path init move hp hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelOneWordBonePlacements_iff path hup hdown placement).2
    exact ⟨init, move, hp, rfl⟩
  · simpa [placement, labelOnePrefixBonePlacement] using
      reverseBonePlacement_covers_target
        (labelOnePrefixSimplexPoint (t := m + 3) path init
          ((List.prefix_append init [move]).trans hp) (by omega))
        (labelOnePrefixSimplexPoint (t := m + 3) path (init ++ [move])
          hp (by omega))
        (goodBoneClassOfMove .one move)
        (labelOnePrefix_owner_step path init move hp (by omega))
        (by
          intro candidate hc
          apply labelOnePrefix_source_cells_mem path init move hp
            hup hdown candidate
          simpa using hc)
        (by simpa using labelOnePrefix_target_cell_mem path init move hp hup)

theorem labelTwoWord_outgoing_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ recursiveBallotWord path)
    (label : MicroLabel) (hlabel : label ≠ .two) :
    let source := labelTwoPrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell source label) :=
      labelTwoPrefix_source_cells_mem_of_prefix path pre hp hup hdown
        label hlabel
    ∃ placement ∈ labelTwoWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell source label, hmem⟩ := by
  dsimp
  obtain ⟨move, suffix, hword⟩ := exists_next_of_prefix_ne hp hne
  have hpEdge : pre ++ [move] <+: recursiveBallotWord path := by
    rw [hword]
    simp
  let placement := labelTwoPrefixBonePlacement path pre move hpEdge hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelTwoWordBonePlacements_iff path hup hdown placement).2
    exact ⟨pre, move, hpEdge, rfl⟩
  · simpa [placement, labelTwoPrefixBonePlacement] using
      reverseBonePlacement_covers_source
        (labelTwoPrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hpEdge) (by omega))
        (labelTwoPrefixSimplexPoint (t := m + 3) path (pre ++ [move])
          hpEdge (by omega))
        (goodBoneClassOfMove .two move)
        (labelTwoPrefix_owner_step path pre move hpEdge (by omega))
        (by
          intro candidate hc
          apply labelTwoPrefix_source_cells_mem path pre move hpEdge
            hup hdown candidate
          simpa using hc)
        (by simpa using labelTwoPrefix_target_cell_mem path pre move hpEdge hup)
        label (by simpa using hlabel)

theorem labelTwoWord_incoming_covers {up down m : ℕ}
    (path : RecursiveBallot up down)
    (hup : up < m + 3) (hdown : down < m + 3)
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord path)
    (hne : pre ≠ []) :
    let target := labelTwoPrefixSimplexPoint (t := m + 3)
      path pre hp (by omega)
    let hmem : inPeripheralBenzel (m + 5) (ownerCell target .two) := by
      obtain ⟨init, move, hpre⟩ := exists_init_last hne
      subst pre
      exact labelTwoPrefix_target_cell_mem path init move hp hup
    ∃ placement ∈ labelTwoWordBonePlacements path hup hdown,
      PlacementCovers placement ⟨ownerCell target .two, hmem⟩ := by
  dsimp
  obtain ⟨init, move, hpre⟩ := exists_init_last hne
  subst pre
  let placement := labelTwoPrefixBonePlacement path init move hp hup hdown
  refine ⟨placement, ?_, ?_⟩
  · apply (mem_labelTwoWordBonePlacements_iff path hup hdown placement).2
    exact ⟨init, move, hp, rfl⟩
  · simpa [placement, labelTwoPrefixBonePlacement] using
      reverseBonePlacement_covers_target
        (labelTwoPrefixSimplexPoint (t := m + 3) path init
          ((List.prefix_append init [move]).trans hp) (by omega))
        (labelTwoPrefixSimplexPoint (t := m + 3) path (init ++ [move])
          hp (by omega))
        (goodBoneClassOfMove .two move)
        (labelTwoPrefix_owner_step path init move hp (by omega))
        (by
          intro candidate hc
          apply labelTwoPrefix_source_cells_mem path init move hp
            hup hdown candidate
          simpa using hc)
        (by simpa using labelTwoPrefix_target_cell_mem path init move hp hup)

end BenzelProblem6Kernel

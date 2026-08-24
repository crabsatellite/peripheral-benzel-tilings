import BenzelProblem6Kernel.LiteralPathPlacementList

/-!
# Reconstructed arm-word bones already belong to the source tiling
-/

namespace BenzelProblem6Kernel

theorem labelZeroWordPlacements_subset_tiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceZero (m + 3))
    (hlabel : last.boneClass.label = .zero)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    ∀ placement ∈ labelZeroWordBonePlacements ballot hup hdown,
      placement ∈ tiling.1 := by
  classical
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by
        simpa [hprefixWord]
      have hsourcePrefix : first.source = labelZeroPrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceZero, labelZeroPrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelZeroPrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelZero_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      let pathFinset := path.placementList.toFinset
      let wordFinset := (labelZeroWordBonePlacements ballot hup hdown).toFinset
      have hsubset : pathFinset ⊆ wordFinset := by
        intro placement hplacement
        simp only [pathFinset, wordFinset, List.mem_toFinset] at hplacement ⊢
        exact hscan.2 placement hplacement
      have hpathCard : pathFinset.card =
          (recursiveBallotWord ballot).length := by
        dsimp [pathFinset]
        rw [List.toFinset_card_of_nodup
          (path.placementList_nodup hstone tiling),
          path.placementList_length, ← hprefixWord]
      have hwordCard : wordFinset.card ≤
          (recursiveBallotWord ballot).length := by
        dsimp [wordFinset]
        calc
          (labelZeroWordBonePlacements ballot hup hdown).toFinset.card ≤
              (labelZeroWordBonePlacements ballot hup hdown).length :=
            List.toFinset_card_le _
          _ = up + down := labelZeroWordBonePlacements_length ballot hup hdown
          _ = (recursiveBallotWord ballot).length :=
            (recursiveBallotWord_length ballot).symm
      have heq : pathFinset = wordFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      intro placement hplacement
      have hpathMem : placement ∈ path.placementList := by
        have : placement ∈ wordFinset := by
          simpa [wordFinset] using hplacement
        rw [← heq] at this
        simpa [pathFinset] using this
      exact path.placementList_mem_tiling hstone tiling hpathMem

theorem labelOneWordPlacements_subset_tiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceOne (m + 3))
    (hlabel : last.boneClass.label = .one)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    ∀ placement ∈ labelOneWordBonePlacements ballot hup hdown,
      placement ∈ tiling.1 := by
  classical
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by
        simpa [hprefixWord]
      have hsourcePrefix : first.source = labelOnePrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceOne, labelOnePrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelOnePrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelOne_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      let pathFinset := path.placementList.toFinset
      let wordFinset := (labelOneWordBonePlacements ballot hup hdown).toFinset
      have hsubset : pathFinset ⊆ wordFinset := by
        intro placement hplacement
        simp only [pathFinset, wordFinset, List.mem_toFinset] at hplacement ⊢
        exact hscan.2 placement hplacement
      have hpathCard : pathFinset.card =
          (recursiveBallotWord ballot).length := by
        dsimp [pathFinset]
        rw [List.toFinset_card_of_nodup
          (path.placementList_nodup hstone tiling),
          path.placementList_length, ← hprefixWord]
      have hwordCard : wordFinset.card ≤
          (recursiveBallotWord ballot).length := by
        dsimp [wordFinset]
        calc
          (labelOneWordBonePlacements ballot hup hdown).toFinset.card ≤
              (labelOneWordBonePlacements ballot hup hdown).length :=
            List.toFinset_card_le _
          _ = up + down := labelOneWordBonePlacements_length ballot hup hdown
          _ = (recursiveBallotWord ballot).length :=
            (recursiveBallotWord_length ballot).symm
      have heq : pathFinset = wordFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      intro placement hplacement
      have hpathMem : placement ∈ path.placementList := by
        have : placement ∈ wordFinset := by
          simpa [wordFinset] using hplacement
        rw [← heq] at this
        simpa [pathFinset] using this
      exact path.placementList_mem_tiling hstone tiling hpathMem

theorem labelTwoWordPlacements_subset_tiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .two)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    ∀ placement ∈ labelTwoWordBonePlacements ballot hup hdown,
      placement ∈ tiling.1 := by
  classical
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by
        simpa [hprefixWord]
      have hsourcePrefix : first.source = labelTwoPrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceTwo, labelTwoPrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelTwoPrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelTwo_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      let pathFinset := path.placementList.toFinset
      let wordFinset := (labelTwoWordBonePlacements ballot hup hdown).toFinset
      have hsubset : pathFinset ⊆ wordFinset := by
        intro placement hplacement
        simp only [pathFinset, wordFinset, List.mem_toFinset] at hplacement ⊢
        exact hscan.2 placement hplacement
      have hpathCard : pathFinset.card =
          (recursiveBallotWord ballot).length := by
        dsimp [pathFinset]
        rw [List.toFinset_card_of_nodup
          (path.placementList_nodup hstone tiling),
          path.placementList_length, ← hprefixWord]
      have hwordCard : wordFinset.card ≤
          (recursiveBallotWord ballot).length := by
        dsimp [wordFinset]
        calc
          (labelTwoWordBonePlacements ballot hup hdown).toFinset.card ≤
              (labelTwoWordBonePlacements ballot hup hdown).length :=
            List.toFinset_card_le _
          _ = up + down := labelTwoWordBonePlacements_length ballot hup hdown
          _ = (recursiveBallotWord ballot).length :=
            (recursiveBallotWord_length ballot).symm
      have heq : pathFinset = wordFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      intro placement hplacement
      have hpathMem : placement ∈ path.placementList := by
        have : placement ∈ wordFinset := by
          simpa [wordFinset] using hplacement
        rw [← heq] at this
        simpa [pathFinset] using this
      exact path.placementList_mem_tiling hstone tiling hpathMem

theorem labelZero_last_source_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceZero (m + 3))
    (hlabel : last.boneClass.label = .zero)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    last.source = labelZeroPrefixSimplexPoint (t := m + 3) ballot
      (recursiveBallotWord ballot) List.prefix_rfl (by omega) := by
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by simpa [hprefixWord]
      have hsourcePrefix : first.source = labelZeroPrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceZero, labelZeroPrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelZeroPrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelZero_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      rw [← hmeet, hscan.1]
      apply simplexPointToInt_injective
      rw [simplexPointToInt_labelZeroPrefixSimplexPoint,
        simplexPointToInt_labelZeroPrefixSimplexPoint]
      exact congrArg (labelZeroPrefixPoint (m + 3)) hprefixWord.symm

theorem labelOne_last_source_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceOne (m + 3))
    (hlabel : last.boneClass.label = .one)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    last.source = labelOnePrefixSimplexPoint (t := m + 3) ballot
      (recursiveBallotWord ballot) List.prefix_rfl (by omega) := by
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by simpa [hprefixWord]
      have hsourcePrefix : first.source = labelOnePrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceOne, labelOnePrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelOnePrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelOne_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      rw [← hmeet, hscan.1]
      apply simplexPointToInt_injective
      rw [simplexPointToInt_labelOnePrefixSimplexPoint,
        simplexPointToInt_labelOnePrefixSimplexPoint]
      exact congrArg (labelOnePrefixPoint (m + 3)) hprefixWord.symm

theorem labelTwo_last_source_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .two)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ []) :
    last.source = labelTwoPrefixSimplexPoint (t := m + 3) ballot
      (recursiveBallotWord ballot) List.prefix_rfl (by omega) := by
  cases path with
  | single hedge =>
      have hempty : LiteralEdgePathData.armWord
          (first := first) (last := first)
          (LiteralEdgePathData.single first hedge) = [] := by
        simp [LiteralEdgePathData.armWord, LiteralEdgePathData.ballotWord]
      exact (hne (hword.trans hempty)) |>.elim
  | @snoc previous next path hnext hmeet hsame =>
      have hprefixWord : recursiveBallotWord ballot =
          LiteralEdgePathData.ballotWord first previous path := by
        simpa [LiteralEdgePathData.armWord,
          LiteralEdgePathData.ballotWord] using hword
      have hpFull : [] ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot := by simpa [hprefixWord]
      have hsourcePrefix : first.source = labelTwoPrefixSimplexPoint
          (t := m + 3) ballot []
          ((List.prefix_append []
            (LiteralEdgePathData.ballotWord first previous path)).trans hpFull)
          (by omega) := by
        rw [hsource]
        apply simplexPoint_ext <;>
          simp [sourceTwo, labelTwoPrefixSimplexPoint,
            IntSimplex.toSimplexPoint, labelTwoPrefixPoint,
            majorityCount, minorityCount] <;> omega
      have hscan := labelTwo_path_replays_from_prefix tiling ballot path []
        hpFull hup hdown (hsame.trans hlabel) hsourcePrefix
      rw [← hmeet, hscan.1]
      apply simplexPointToInt_injective
      rw [simplexPointToInt_labelTwoPrefixSimplexPoint,
        simplexPointToInt_labelTwoPrefixSimplexPoint]
      exact congrArg (labelTwoPrefixPoint (m + 3)) hprefixWord.symm

theorem labelZero_terminal_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceZero (m + 3))
    (hlabel : last.boneClass.label = .zero)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ [])
    (terminalMove : BallotMove)
    (hmove : last.boneClass.ballotMove = terminalMove)
    (target : SimplexPoint (m + 3))
    (hstep : addCell
      (ownerQ (labelZeroPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)),
       ownerR (labelZeroPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)))
      (goodBoneClassOfMove .zero terminalMove).step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label,
      label ≠ (goodBoneClassOfMove .zero terminalMove).label →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelZeroPrefixSimplexPoint (t := m + 3) ballot
          (recursiveBallotWord ballot) List.prefix_rfl (by omega)) label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target (goodBoneClassOfMove .zero terminalMove).label)) :
    reverseBonePlacement
      (labelZeroPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega))
      target (goodBoneClassOfMove .zero terminalMove) hstep
        hsourceMem htargetMem = last.placement := by
  have hlastSource := labelZero_last_source_replays hstone tiling ballot path
    hup hdown hsource hlabel hword hne
  have hclass : goodBoneClassOfMove .zero terminalMove = last.boneClass := by
    rw [← hmove, ← hlabel]
    exact goodBoneClassOfMove_unique last.boneClass
  exact reverseBonePlacement_eq_edge_of_source_class last _ target _ hstep
    hsourceMem htargetMem hlastSource.symm hclass

theorem labelOne_terminal_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceOne (m + 3))
    (hlabel : last.boneClass.label = .one)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ [])
    (terminalMove : BallotMove)
    (hmove : last.boneClass.ballotMove = terminalMove)
    (target : SimplexPoint (m + 3))
    (hstep : addCell
      (ownerQ (labelOnePrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)),
       ownerR (labelOnePrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)))
      (goodBoneClassOfMove .one terminalMove).step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label,
      label ≠ (goodBoneClassOfMove .one terminalMove).label →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelOnePrefixSimplexPoint (t := m + 3) ballot
          (recursiveBallotWord ballot) List.prefix_rfl (by omega)) label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target (goodBoneClassOfMove .one terminalMove).label)) :
    reverseBonePlacement
      (labelOnePrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega))
      target (goodBoneClassOfMove .one terminalMove) hstep
        hsourceMem htargetMem = last.placement := by
  have hlastSource := labelOne_last_source_replays hstone tiling ballot path
    hup hdown hsource hlabel hword hne
  have hclass : goodBoneClassOfMove .one terminalMove = last.boneClass := by
    rw [← hmove, ← hlabel]
    exact goodBoneClassOfMove_unique last.boneClass
  exact reverseBonePlacement_eq_edge_of_source_class last _ target _ hstep
    hsourceMem htargetMem hlastSource.symm hclass

theorem labelTwo_terminal_replays
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hsource : first.source = sourceTwo (m + 3))
    (hlabel : last.boneClass.label = .two)
    (hword : recursiveBallotWord ballot = path.armWord)
    (hne : recursiveBallotWord ballot ≠ [])
    (terminalMove : BallotMove)
    (hmove : last.boneClass.ballotMove = terminalMove)
    (target : SimplexPoint (m + 3))
    (hstep : addCell
      (ownerQ (labelTwoPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)),
       ownerR (labelTwoPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega)))
      (goodBoneClassOfMove .two terminalMove).step =
      (ownerQ target, ownerR target))
    (hsourceMem : ∀ label,
      label ≠ (goodBoneClassOfMove .two terminalMove).label →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelTwoPrefixSimplexPoint (t := m + 3) ballot
          (recursiveBallotWord ballot) List.prefix_rfl (by omega)) label))
    (htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target (goodBoneClassOfMove .two terminalMove).label)) :
    reverseBonePlacement
      (labelTwoPrefixSimplexPoint (t := m + 3) ballot
        (recursiveBallotWord ballot) List.prefix_rfl (by omega))
      target (goodBoneClassOfMove .two terminalMove) hstep
        hsourceMem htargetMem = last.placement := by
  have hlastSource := labelTwo_last_source_replays hstone tiling ballot path
    hup hdown hsource hlabel hword hne
  have hclass : goodBoneClassOfMove .two terminalMove = last.boneClass := by
    rw [← hmove, ← hlabel]
    exact goodBoneClassOfMove_unique last.boneClass
  exact reverseBonePlacement_eq_edge_of_source_class last _ target _ hstep
    hsourceMem htargetMem hlastSource.symm hclass

end BenzelProblem6Kernel

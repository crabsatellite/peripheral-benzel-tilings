import BenzelProblem6Kernel.ReconstructedBoneSubset

/-!
# Every reconstructed arm-prefix owner is active in the source tiling
-/

namespace BenzelProblem6Kernel

theorem labelZero_prefix_owner_active
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
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord ballot) :
    labelZeroPrefixSimplexPoint (t := m + 3) ballot pre hp (by omega) ∈
      activeOwnerFinset hstone tiling := by
  by_cases hfull : pre = recursiveBallotWord ballot
  · subst pre
    have hlastSource := labelZero_last_source_replays hstone tiling ballot path
      hup hdown hsource hlabel hword hne
    rw [← hlastSource]
    exact edge_source_mem_active hstone tiling last path.last_mem
  · obtain ⟨move, suffix, hdecomp⟩ := exists_next_of_prefix_ne hp hfull
    have hpEdge : pre ++ [move] <+: recursiveBallotWord ballot := by
      rw [hdecomp]
      simp
    let placement := labelZeroPrefixBonePlacement ballot pre move hpEdge hup hdown
    have hplacement : placement ∈ tiling.1 := by
      apply labelZeroWordPlacements_subset_tiling hstone tiling ballot path
        hup hdown hsource hlabel hword hne placement
      apply (mem_labelZeroWordBonePlacements_iff ballot hup hdown placement).2
      exact ⟨pre, move, hpEdge, rfl⟩
    let edge := labelZeroPrefixBoneEdgeOfTiling hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hedge := labelZeroPrefixBoneEdge_mem hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hactive := edge_source_mem_active hstone tiling edge hedge
    have hsourceEdge := labelZeroPrefixBoneEdge_source hstone tiling ballot
      pre move hpEdge hup hdown hplacement
    rw [hsourceEdge] at hactive
    simpa using hactive

theorem labelOne_prefix_owner_active
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
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord ballot) :
    labelOnePrefixSimplexPoint (t := m + 3) ballot pre hp (by omega) ∈
      activeOwnerFinset hstone tiling := by
  by_cases hfull : pre = recursiveBallotWord ballot
  · subst pre
    have hlastSource := labelOne_last_source_replays hstone tiling ballot path
      hup hdown hsource hlabel hword hne
    rw [← hlastSource]
    exact edge_source_mem_active hstone tiling last path.last_mem
  · obtain ⟨move, suffix, hdecomp⟩ := exists_next_of_prefix_ne hp hfull
    have hpEdge : pre ++ [move] <+: recursiveBallotWord ballot := by
      rw [hdecomp]
      simp
    let placement := labelOnePrefixBonePlacement ballot pre move hpEdge hup hdown
    have hplacement : placement ∈ tiling.1 := by
      apply labelOneWordPlacements_subset_tiling hstone tiling ballot path
        hup hdown hsource hlabel hword hne placement
      apply (mem_labelOneWordBonePlacements_iff ballot hup hdown placement).2
      exact ⟨pre, move, hpEdge, rfl⟩
    let edge := labelOnePrefixBoneEdgeOfTiling hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hedge := labelOnePrefixBoneEdge_mem hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hactive := edge_source_mem_active hstone tiling edge hedge
    have hsourceEdge := labelOnePrefixBoneEdge_source hstone tiling ballot
      pre move hpEdge hup hdown hplacement
    rw [hsourceEdge] at hactive
    simpa using hactive

theorem labelTwo_prefix_owner_active
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
    (pre : List BallotMove) (hp : pre <+: recursiveBallotWord ballot) :
    labelTwoPrefixSimplexPoint (t := m + 3) ballot pre hp (by omega) ∈
      activeOwnerFinset hstone tiling := by
  by_cases hfull : pre = recursiveBallotWord ballot
  · subst pre
    have hlastSource := labelTwo_last_source_replays hstone tiling ballot path
      hup hdown hsource hlabel hword hne
    rw [← hlastSource]
    exact edge_source_mem_active hstone tiling last path.last_mem
  · obtain ⟨move, suffix, hdecomp⟩ := exists_next_of_prefix_ne hp hfull
    have hpEdge : pre ++ [move] <+: recursiveBallotWord ballot := by
      rw [hdecomp]
      simp
    let placement := labelTwoPrefixBonePlacement ballot pre move hpEdge hup hdown
    have hplacement : placement ∈ tiling.1 := by
      apply labelTwoWordPlacements_subset_tiling hstone tiling ballot path
        hup hdown hsource hlabel hword hne placement
      apply (mem_labelTwoWordBonePlacements_iff ballot hup hdown placement).2
      exact ⟨pre, move, hpEdge, rfl⟩
    let edge := labelTwoPrefixBoneEdgeOfTiling hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hedge := labelTwoPrefixBoneEdge_mem hstone tiling ballot pre move
      hpEdge hup hdown hplacement
    have hactive := edge_source_mem_active hstone tiling edge hedge
    have hsourceEdge := labelTwoPrefixBoneEdge_source hstone tiling ballot
      pre move hpEdge hup hdown hplacement
    rw [hsourceEdge] at hactive
    simpa using hactive

end BenzelProblem6Kernel

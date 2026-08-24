import BenzelProblem6Kernel.ReconstructedOwnerSubset
import BenzelProblem6Kernel.ReverseStoneCoverage

/-!
# A positive extracted Y reconstructs its entire source literal tiling
-/

namespace BenzelProblem6Kernel

theorem positiveYOwnerFinset_subset_active_of_data
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (tiling : LiteralTiling (x + y + z))
    (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone tiling)
    (hsink : data.sink = sinkPoint x y z)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    positiveYOwnerFinset x y z arms ⊆ activeOwnerFinset hstone tiling := by
  classical
  intro point hpoint
  simp only [positiveYOwnerFinset, List.mem_toFinset,
    positiveYOwnerList, List.mem_append, List.mem_singleton] at hpoint
  rcases hpoint with ((hzero | hone) | htwo) | hsinkPoint
  · obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelZeroPrefixOwnerList_iff arms.1 (by omega) point).1 hzero
    exact labelZero_prefix_owner_active hstone tiling arms.1 data.zeroPath
      (by omega) (by omega) data.zero_source data.zero_label hzeroWord
      (positiveLabelZeroWord_nonempty x y z arms) pre hp
  · obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelOnePrefixOwnerList_iff arms.2.1 (by omega) point).1 hone
    exact labelOne_prefix_owner_active hstone tiling arms.2.1 data.onePath
      (by omega) (by omega) data.one_source data.one_label honeWord
      (positiveLabelOneWord_nonempty x y z arms) pre hp
  · obtain ⟨pre, hp, rfl⟩ :=
      (mem_labelTwoPrefixOwnerList_iff arms.2.2 (by omega) point).1 htwo
    exact labelTwo_prefix_owner_active hstone tiling arms.2.2 data.twoPath
      (by omega) (by omega) data.two_source data.two_label htwoWord
      (positiveLabelTwoWord_nonempty x y z arms) pre hp
  · subst point
    rw [← hsink]
    exact data.sink_active

theorem positiveYOwnerFinset_eq_active_of_data
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (tiling : LiteralTiling (x + y + z))
    (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone tiling)
    (hsink : data.sink = sinkPoint x y z)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    positiveYOwnerFinset x y z arms = activeOwnerFinset hstone tiling := by
  apply Finset.eq_of_subset_of_card_le
    (positiveYOwnerFinset_subset_active_of_data hstone x y z tiling arms data
      hsink hzeroWord honeWord htwoWord)
  rw [positiveYOwnerFinset_card, activeOwnerFinset_card]

theorem positiveYBonePlacements_subset_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (tiling : LiteralTiling (x + y + z))
    (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone tiling)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    ∀ placement ∈ positiveYBonePlacements x y z arms,
      placement ∈ tiling.1 := by
  intro placement hplacement
  simp only [positiveYBonePlacements, List.mem_append,
    List.mem_singleton] at hplacement
  rcases hplacement with (((((hzero | hzeroTerminal) | hone) |
    honeTerminal) | htwo) | htwoTerminal)
  · exact labelZeroWordPlacements_subset_tiling hstone tiling arms.1
      data.zeroPath (by omega) (by omega) data.zero_source data.zero_label
      hzeroWord (positiveLabelZeroWord_nonempty x y z arms) placement hzero
  · subst placement
    have hmove : data.zeroLast.boneClass.ballotMove = .majority :=
      goodBoneClass_ballotMove_majority_iff data.zeroLast.boneClass |>.2
        (Or.inl ⟨data.zero_label, hpos.1⟩)
    have hreplay := labelZero_terminal_replays hstone tiling arms.1
      data.zeroPath (by omega) (by omega) data.zero_source data.zero_label
      hzeroWord (positiveLabelZeroWord_nonempty x y z arms) .majority hmove
      (sinkPoint x y z)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelZero_terminal_step x y z arms.1)
      (by simpa using (labelZeroPrefix_source_cells_mem_of_prefix
        (m := x + y + z) arms.1 (recursiveBallotWord arms.1)
          List.prefix_rfl (by omega) (by omega)))
      (by simpa using sinkPoint_ownerCell_mem x y z .zero)
    have hterminalEq : positiveLabelZeroTerminalBone x y z arms.1 =
        data.zeroLast.placement := by
      unfold positiveLabelZeroTerminalBone
      exact hreplay
    rw [hterminalEq]
    exact (mem_literalDirectedEdges_placement hstone tiling data.zeroLast
      data.zeroPath.last_mem).1
  · exact labelOneWordPlacements_subset_tiling hstone tiling arms.2.1
      data.onePath (by omega) (by omega) data.one_source data.one_label
      honeWord (positiveLabelOneWord_nonempty x y z arms) placement hone
  · subst placement
    have hmove : data.oneLast.boneClass.ballotMove = .majority :=
      goodBoneClass_ballotMove_majority_iff data.oneLast.boneClass |>.2
        (Or.inr (Or.inl ⟨data.one_label, hpos.2.1⟩))
    have hreplay := labelOne_terminal_replays hstone tiling arms.2.1
      data.onePath (by omega) (by omega) data.one_source data.one_label
      honeWord (positiveLabelOneWord_nonempty x y z arms) .majority hmove
      (sinkPoint x y z)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelOne_terminal_step x y z arms.2.1)
      (by simpa using (labelOnePrefix_source_cells_mem_of_prefix
        (m := x + y + z) arms.2.1 (recursiveBallotWord arms.2.1)
          List.prefix_rfl (by omega) (by omega)))
      (by simpa using sinkPoint_ownerCell_mem x y z .one)
    have hterminalEq : positiveLabelOneTerminalBone x y z arms.2.1 =
        data.oneLast.placement := by
      unfold positiveLabelOneTerminalBone
      exact hreplay
    rw [hterminalEq]
    exact (mem_literalDirectedEdges_placement hstone tiling data.oneLast
      data.onePath.last_mem).1
  · exact labelTwoWordPlacements_subset_tiling hstone tiling arms.2.2
      data.twoPath (by omega) (by omega) data.two_source data.two_label
      htwoWord (positiveLabelTwoWord_nonempty x y z arms) placement htwo
  · subst placement
    have hmove : data.twoLast.boneClass.ballotMove = .majority :=
      goodBoneClass_ballotMove_majority_iff data.twoLast.boneClass |>.2
        (Or.inr (Or.inr ⟨data.two_label, hpos.2.2⟩))
    have hreplay := labelTwo_terminal_replays hstone tiling arms.2.2
      data.twoPath (by omega) (by omega) data.two_source data.two_label
      htwoWord (positiveLabelTwoWord_nonempty x y z arms) .majority hmove
      (sinkPoint x y z)
      (by simpa [goodBoneClassOfMove, GoodBoneClass.step] using
        positive_labelTwo_terminal_step x y z arms.2.2)
      (by simpa using (labelTwoPrefix_source_cells_mem_of_prefix
        (m := x + y + z) arms.2.2 (recursiveBallotWord arms.2.2)
          List.prefix_rfl (by omega) (by omega)))
      (by simpa using sinkPoint_ownerCell_mem x y z .two)
    have hterminalEq : positiveLabelTwoTerminalBone x y z arms.2.2 =
        data.twoLast.placement := by
      unfold positiveLabelTwoTerminalBone
      exact hreplay
    rw [hterminalEq]
    exact (mem_literalDirectedEdges_placement hstone tiling data.twoLast
      data.twoPath.last_mem).1

theorem positiveYStonePlacements_subset_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (tiling : LiteralTiling (x + y + z))
    (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone tiling)
    (hsink : data.sink = sinkPoint x y z)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    positiveYStonePlacements x y z arms ⊆ tiling.1 := by
  classical
  intro reconstructed hreconstructed
  simp only [positiveYStonePlacements, Finset.mem_image] at hreconstructed
  obtain ⟨owner, _, hreconstructed⟩ := hreconstructed
  have hownerSpec := owner.2
  have hownerFull := positiveYStoneOwners_full x y z arms owner.1 owner.2
  have hnotArm : ¬PositiveYArmOwner x y z arms owner.1 := by
    have h := hownerSpec
    simp only [positiveYStoneOwners, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    exact h.2
  have hnotYOwner : owner.1 ∉ positiveYOwnerFinset x y z arms := by
    intro hmem
    exact hnotArm (positiveYArmOwner_of_mem_ownerFinset x y z arms owner.1 hmem)
  have hownerEq := positiveYOwnerFinset_eq_active_of_data hstone x y z
    tiling arms data hsink hzeroWord honeWord htwoWord
  have hnotActive : owner.1 ∉ activeOwnerFinset hstone tiling := by
    rwa [← hownerEq]
  have hstoneOwner : owner.1 ∈ stoneOwnerFinset hstone tiling := by
    simpa [activeOwnerFinset] using hnotActive
  simp only [stoneOwnerFinset, Finset.mem_map, Finset.mem_attach] at hstoneOwner
  obtain ⟨placement, _, hplacementOwner⟩ := hstoneOwner
  have hownerValue : stoneOwner hstone tiling placement = owner.1 := by
    simpa using hplacementOwner
  have heq := reverseStonePlacement_eq_stoneOwner hstone tiling placement owner.1
    hownerValue hownerFull.1 hownerFull.2.1 hownerFull.2.2
  have hreconstructedEq : reconstructed = placement.1 :=
    hreconstructed.symm.trans heq
  rw [hreconstructedEq]
  have hp := placement.2
  simp only [stonePlacementFinset, Finset.mem_filter] at hp
  exact hp.1

theorem positiveYLiteralTiling_eq_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (tiling : LiteralTiling (x + y + z))
    (arms : PositiveArmTriple x y z)
    (data : LiteralYPathData hstone tiling)
    (hsink : data.sink = sinkPoint x y z)
    (hpos : data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA)
    (hzeroWord : recursiveBallotWord arms.1 = data.zeroPath.armWord)
    (honeWord : recursiveBallotWord arms.2.1 = data.onePath.armWord)
    (htwoWord : recursiveBallotWord arms.2.2 = data.twoPath.armWord) :
    positiveYLiteralTiling x y z arms = tiling := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro placement hplacement
    simp only [positiveYLiteralTiling, positiveYChosenPlacements,
      Finset.mem_union, List.mem_toFinset] at hplacement
    rcases hplacement with hbone | hstonePlacement
    · exact positiveYBonePlacements_subset_source hstone x y z tiling arms
        data hpos hzeroWord honeWord htwoWord placement hbone
    · exact positiveYStonePlacements_subset_source hstone x y z tiling arms
        data hsink hzeroWord honeWord htwoWord hstonePlacement
  · rw [literal_tiling_card (positiveYLiteralTiling x y z arms),
      literal_tiling_card tiling]

end BenzelProblem6Kernel

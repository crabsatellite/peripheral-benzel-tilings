import BenzelProblem6Kernel.PositiveTerminalCoverage

/-!
# Every peripheral benzel cell is covered by the reconstructed positive Y
-/

namespace BenzelProblem6Kernel

theorem intSimplex_ext {left right : IntSimplex}
    (hu : left.u = right.u) (hv : left.v = right.v)
    (hw : left.w = right.w) : left = right := by
  cases left
  cases right
  simp_all

theorem simplexPointToInt_labelZeroPrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    simplexPointToInt (labelZeroPrefixSimplexPoint path pre hp hup) =
      labelZeroPrefixPoint t pre := by
  apply intSimplex_ext <;> simp [simplexPointToInt]

theorem simplexPointToInt_labelOnePrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    simplexPointToInt (labelOnePrefixSimplexPoint path pre hp hup) =
      labelOnePrefixPoint t pre := by
  apply intSimplex_ext <;> simp [simplexPointToInt]

theorem simplexPointToInt_labelTwoPrefixSimplexPoint {up down t : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (hp : pre <+: recursiveBallotWord path) (hup : up ≤ t) :
    simplexPointToInt (labelTwoPrefixSimplexPoint path pre hp hup) =
      labelTwoPrefixPoint t pre := by
  apply intSimplex_ext <;> simp [simplexPointToInt]

theorem positiveYArmOwner_sourceZero (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    PositiveYArmOwner x y z arms (sourceZero (x + y + z + 3)) := by
  left
  right
  exact ⟨[], by simp, by simp [simplexPointToInt, sourceZero,
    labelZeroPrefixPoint, majorityCount, minorityCount]⟩

theorem positiveYArmOwner_sourceOne (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    PositiveYArmOwner x y z arms (sourceOne (x + y + z + 3)) := by
  right
  left
  right
  exact ⟨[], by simp, by simp [simplexPointToInt, sourceOne,
    labelOnePrefixPoint, majorityCount, minorityCount]⟩

theorem positiveYArmOwner_sourceTwo (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    PositiveYArmOwner x y z arms (sourceTwo (x + y + z + 3)) := by
  right
  right
  right
  exact ⟨[], by simp, by simp [simplexPointToInt, sourceTwo,
    labelTwoPrefixPoint, majorityCount, minorityCount]⟩

theorem full_of_not_positiveYArmOwner (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3))
    (hnot : ¬PositiveYArmOwner x y z arms point) :
    IsFullSimplexOwner point := by
  rcases simplex_corner_or_full (t := x + y + z + 3) (by omega) point with
    hzero | hone | htwo | hfull
  · exact (hnot (hzero ▸ positiveYArmOwner_sourceZero x y z arms)).elim
  · exact (hnot (hone ▸ positiveYArmOwner_sourceOne x y z arms)).elim
  · exact (hnot (htwo ▸ positiveYArmOwner_sourceTwo x y z arms)).elim
  · exact hfull

theorem mem_positiveYChosen_of_zeroWord (x y z : ℕ)
    (arms : PositiveArmTriple x y z) (placement : LiteralPlacement (x + y + z))
    (hmem : placement ∈ labelZeroWordBonePlacements (m := x + y + z)
      arms.1 (by omega) (by omega)) :
    placement ∈ positiveYChosenPlacements x y z arms := by
  classical
  simp only [positiveYChosenPlacements, Finset.mem_union, List.mem_toFinset]
  left
  simp [positiveYBonePlacements, hmem]

theorem mem_positiveYChosen_of_oneWord (x y z : ℕ)
    (arms : PositiveArmTriple x y z) (placement : LiteralPlacement (x + y + z))
    (hmem : placement ∈ labelOneWordBonePlacements (m := x + y + z)
      arms.2.1 (by omega) (by omega)) :
    placement ∈ positiveYChosenPlacements x y z arms := by
  classical
  simp only [positiveYChosenPlacements, Finset.mem_union, List.mem_toFinset]
  left
  simp [positiveYBonePlacements, hmem]

theorem mem_positiveYChosen_of_twoWord (x y z : ℕ)
    (arms : PositiveArmTriple x y z) (placement : LiteralPlacement (x + y + z))
    (hmem : placement ∈ labelTwoWordBonePlacements (m := x + y + z)
      arms.2.2 (by omega) (by omega)) :
    placement ∈ positiveYChosenPlacements x y z arms := by
  classical
  simp only [positiveYChosenPlacements, Finset.mem_union, List.mem_toFinset]
  left
  simp [positiveYBonePlacements, hmem]

theorem mem_positiveYChosen_zeroTerminal (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    positiveLabelZeroTerminalBone x y z arms.1 ∈
      positiveYChosenPlacements x y z arms := by
  classical
  simp [positiveYChosenPlacements, positiveYBonePlacements]

theorem mem_positiveYChosen_oneTerminal (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    positiveLabelOneTerminalBone x y z arms.2.1 ∈
      positiveYChosenPlacements x y z arms := by
  classical
  simp [positiveYChosenPlacements, positiveYBonePlacements]

theorem mem_positiveYChosen_twoTerminal (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    positiveLabelTwoTerminalBone x y z arms.2.2 ∈
      positiveYChosenPlacements x y z arms := by
  classical
  simp [positiveYChosenPlacements, positiveYBonePlacements]

theorem positiveY_sink_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z) (label : MicroLabel) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement
        ⟨ownerCell (sinkPoint x y z) label,
          sinkPoint_ownerCell_mem x y z label⟩ := by
  rcases label with _ | _ | _
  · exact ⟨positiveLabelZeroTerminalBone x y z arms.1,
      mem_positiveYChosen_zeroTerminal x y z arms,
      positiveLabelZeroTerminal_covers_sink x y z arms.1⟩
  · exact ⟨positiveLabelOneTerminalBone x y z arms.2.1,
      mem_positiveYChosen_oneTerminal x y z arms,
      positiveLabelOneTerminal_covers_sink x y z arms.2.1⟩
  · exact ⟨positiveLabelTwoTerminalBone x y z arms.2.2,
      mem_positiveYChosen_twoTerminal x y z arms,
      positiveLabelTwoTerminal_covers_sink x y z arms.2.2⟩

theorem positiveY_zeroArm_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) (label : MicroLabel)
    (hcell : inPeripheralBenzel (x + y + z + 5) (ownerCell point label))
    (hpoint : PositiveLabelZeroPoint x y z arms.1 (simplexPointToInt point))
    (hnotSink : point ≠ sinkPoint x y z) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement ⟨ownerCell point label, hcell⟩ := by
  rcases hpoint with hsink | ⟨pre, hp, heq⟩
  · exact (hnotSink ((simplexPointToInt_eq_intSink_iff x y z point).1 hsink)).elim
  let prefixPoint := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
    arms.1 pre hp (by omega)
  have hpointEq : point = prefixPoint := by
    apply simplexPointToInt_injective
    rw [heq]
    exact (simplexPointToInt_labelZeroPrefixSimplexPoint arms.1 pre hp
      (by omega)).symm
  subst point
  by_cases hlabel : label = .zero
  · subst label
    have hpre : pre ≠ [] := by
      intro hempty
      subst pre
      rw [owner_zero_mem_iff (by omega)] at hcell
      have hv :
          ((labelZeroPrefixSimplexPoint (t := x + y + z + 3)
            arms.1 [] (by simpa using hp) (by omega)).v : ℤ) =
            x + y + z + 3 := by
        simpa only [labelZeroPrefixPoint, majorityCount, minorityCount,
          List.count_nil, Nat.cast_zero, sub_zero] using
          (labelZeroPrefixSimplexPoint_v (t := x + y + z + 3)
            arms.1 [] (by simpa using hp) (by omega))
      dsimp [prefixPoint] at hcell
      omega
    obtain ⟨placement, hword, hcover⟩ :=
      labelZeroWord_incoming_covers arms.1 (m := x + y + z)
        (by omega) (by omega) pre hp hpre
    exact ⟨placement, mem_positiveYChosen_of_zeroWord x y z arms placement hword,
      by simpa using hcover⟩
  · by_cases hfull : pre = recursiveBallotWord arms.1
    · subst pre
      exact ⟨positiveLabelZeroTerminalBone x y z arms.1,
        mem_positiveYChosen_zeroTerminal x y z arms,
        by
          dsimp [prefixPoint]
          simpa using (positiveLabelZeroTerminal_covers_source
            x y z arms.1 label hlabel)⟩
    · obtain ⟨placement, hword, hcover⟩ :=
        labelZeroWord_outgoing_covers arms.1 (m := x + y + z)
          (by omega) (by omega) pre hp hfull label hlabel
      exact ⟨placement, mem_positiveYChosen_of_zeroWord x y z arms placement hword,
        by simpa using hcover⟩

theorem positiveY_oneArm_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) (label : MicroLabel)
    (hcell : inPeripheralBenzel (x + y + z + 5) (ownerCell point label))
    (hpoint : PositiveLabelOnePoint x y z arms.2.1 (simplexPointToInt point))
    (hnotSink : point ≠ sinkPoint x y z) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement ⟨ownerCell point label, hcell⟩ := by
  rcases hpoint with hsink | ⟨pre, hp, heq⟩
  · exact (hnotSink ((simplexPointToInt_eq_intSink_iff x y z point).1 hsink)).elim
  let prefixPoint := labelOnePrefixSimplexPoint (t := x + y + z + 3)
    arms.2.1 pre hp (by omega)
  have hpointEq : point = prefixPoint := by
    apply simplexPointToInt_injective
    rw [heq]
    exact (simplexPointToInt_labelOnePrefixSimplexPoint arms.2.1 pre hp
      (by omega)).symm
  subst point
  by_cases hlabel : label = .one
  · subst label
    have hpre : pre ≠ [] := by
      intro hempty
      subst pre
      rw [owner_one_mem_iff (by omega)] at hcell
      have hw :
          ((labelOnePrefixSimplexPoint (t := x + y + z + 3)
            arms.2.1 [] (by simpa using hp) (by omega)).w : ℤ) =
            x + y + z + 3 := by
        simpa only [labelOnePrefixPoint, majorityCount, minorityCount,
          List.count_nil, Nat.cast_zero, sub_zero] using
          (labelOnePrefixSimplexPoint_w (t := x + y + z + 3)
            arms.2.1 [] (by simpa using hp) (by omega))
      dsimp [prefixPoint] at hcell
      omega
    obtain ⟨placement, hword, hcover⟩ :=
      labelOneWord_incoming_covers arms.2.1 (m := x + y + z)
        (by omega) (by omega) pre hp hpre
    exact ⟨placement, mem_positiveYChosen_of_oneWord x y z arms placement hword,
      by simpa using hcover⟩
  · by_cases hfull : pre = recursiveBallotWord arms.2.1
    · subst pre
      exact ⟨positiveLabelOneTerminalBone x y z arms.2.1,
        mem_positiveYChosen_oneTerminal x y z arms,
        by
          dsimp [prefixPoint]
          simpa using (positiveLabelOneTerminal_covers_source
            x y z arms.2.1 label hlabel)⟩
    · obtain ⟨placement, hword, hcover⟩ :=
        labelOneWord_outgoing_covers arms.2.1 (m := x + y + z)
          (by omega) (by omega) pre hp hfull label hlabel
      exact ⟨placement, mem_positiveYChosen_of_oneWord x y z arms placement hword,
        by simpa using hcover⟩

theorem positiveY_twoArm_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) (label : MicroLabel)
    (hcell : inPeripheralBenzel (x + y + z + 5) (ownerCell point label))
    (hpoint : PositiveLabelTwoPoint x y z arms.2.2 (simplexPointToInt point))
    (hnotSink : point ≠ sinkPoint x y z) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement ⟨ownerCell point label, hcell⟩ := by
  rcases hpoint with hsink | ⟨pre, hp, heq⟩
  · exact (hnotSink ((simplexPointToInt_eq_intSink_iff x y z point).1 hsink)).elim
  let prefixPoint := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
    arms.2.2 pre hp (by omega)
  have hpointEq : point = prefixPoint := by
    apply simplexPointToInt_injective
    rw [heq]
    exact (simplexPointToInt_labelTwoPrefixSimplexPoint arms.2.2 pre hp
      (by omega)).symm
  subst point
  by_cases hlabel : label = .two
  · subst label
    have hpre : pre ≠ [] := by
      intro hempty
      subst pre
      rw [owner_two_mem_iff (by omega)] at hcell
      have hu :
          ((labelTwoPrefixSimplexPoint (t := x + y + z + 3)
            arms.2.2 [] (by simpa using hp) (by omega)).u : ℤ) =
            x + y + z + 3 := by
        simpa only [labelTwoPrefixPoint, majorityCount, minorityCount,
          List.count_nil, Nat.cast_zero, sub_zero] using
          (labelTwoPrefixSimplexPoint_u (t := x + y + z + 3)
            arms.2.2 [] (by simpa using hp) (by omega))
      dsimp [prefixPoint] at hcell
      omega
    obtain ⟨placement, hword, hcover⟩ :=
      labelTwoWord_incoming_covers arms.2.2 (m := x + y + z)
        (by omega) (by omega) pre hp hpre
    exact ⟨placement, mem_positiveYChosen_of_twoWord x y z arms placement hword,
      by simpa using hcover⟩
  · by_cases hfull : pre = recursiveBallotWord arms.2.2
    · subst pre
      exact ⟨positiveLabelTwoTerminalBone x y z arms.2.2,
        mem_positiveYChosen_twoTerminal x y z arms,
        by
          dsimp [prefixPoint]
          simpa using (positiveLabelTwoTerminal_covers_source
            x y z arms.2.2 label hlabel)⟩
    · obtain ⟨placement, hword, hcover⟩ :=
        labelTwoWord_outgoing_covers arms.2.2 (m := x + y + z)
          (by omega) (by omega) pre hp hfull label hlabel
      exact ⟨placement, mem_positiveYChosen_of_twoWord x y z arms placement hword,
        by simpa using hcover⟩

theorem positiveY_owner_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (point : SimplexPoint (x + y + z + 3)) (label : MicroLabel)
    (hcell : inPeripheralBenzel (x + y + z + 5) (ownerCell point label)) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement ⟨ownerCell point label, hcell⟩ := by
  by_cases hsink : point = sinkPoint x y z
  · subst point
    simpa using positiveY_sink_has_cover x y z arms label
  by_cases harm : PositiveYArmOwner x y z arms point
  · rcases harm with hzero | hone | htwo
    · exact positiveY_zeroArm_has_cover x y z arms point label hcell hzero hsink
    · exact positiveY_oneArm_has_cover x y z arms point label hcell hone hsink
    · exact positiveY_twoArm_has_cover x y z arms point label hcell htwo hsink
  · have hfull := full_of_not_positiveYArmOwner x y z arms point harm
    have howner : point ∈ positiveYStoneOwners x y z arms := by
      classical
      simp [positiveYStoneOwners, hfull, harm]
    let placement := reverseStonePlacement point hfull.1 hfull.2.1 hfull.2.2
    have hstone : placement ∈ positiveYStonePlacements x y z arms := by
      classical
      simp only [positiveYStonePlacements, Finset.mem_image]
      exact ⟨⟨point, howner⟩, by simp, rfl⟩
    refine ⟨placement, ?_, ?_⟩
    · simp [positiveYChosenPlacements, hstone]
    · simpa [placement] using
        reverseStonePlacement_covers_label point hfull.1 hfull.2.1
          hfull.2.2 label

theorem positiveY_cell_has_cover (x y z : ℕ)
    (arms : PositiveArmTriple x y z)
    (cell : BenzelCell (x + y + z + 5)) :
    ∃ placement ∈ positiveYChosenPlacements x y z arms,
      PlacementCovers placement cell := by
  let rawPoint := chosenOwner (n := x + y + z + 5) (by omega) cell
  let label := chosenLabel (n := x + y + z + 5) (by omega) cell
  have hlevel : x + y + z + 5 - 2 = x + y + z + 3 := by omega
  let point : SimplexPoint (x + y + z + 3) :=
    _root_.cast (congrArg SimplexPoint hlevel) rawPoint
  have hpointU : point.u = rawPoint.u := by
    cases hlevel
    rfl
  have hpointV : point.v = rawPoint.v := by
    cases hlevel
    rfl
  have hpointW : point.w = rawPoint.w := by
    cases hlevel
    rfl
  have hspec : ownerCell rawPoint label = cell.1 := by
    simpa [rawPoint, label] using
      chosenOwnerLabel_spec (n := x + y + z + 5) (by omega) cell
  have hownerCell : ownerCell point label = cell.1 := by
    rw [← hspec]
    rcases label <;>
      simp [ownerCell, ownerQ, ownerR, hpointU, hpointV, hpointW,
        point, rawPoint]
  have hmem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell point label) := by
    rw [hownerCell]
    exact cell.2
  obtain ⟨placement, hchosen, hcover⟩ :=
    positiveY_owner_has_cover x y z arms point label hmem
  refine ⟨placement, hchosen, ?_⟩
  change cell.1 ∈ placement.cells
  change ownerCell point label ∈ placement.cells at hcover
  rwa [hownerCell] at hcover

end BenzelProblem6Kernel

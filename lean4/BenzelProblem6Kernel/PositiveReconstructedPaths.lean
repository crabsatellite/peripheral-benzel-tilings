import BenzelProblem6Kernel.WordEdgePathBuilder

/-!
# Explicit data-valued paths in a reconstructed positive-chirality tiling
-/

namespace BenzelProblem6Kernel

noncomputable def positiveLabelZeroEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    WordEdgeSystem hstone (positiveYLiteralTiling x y z arms)
      (recursiveBallotWord arms.1) .zero where
  edge pre move hp :=
    labelZeroPrefixBoneEdgeOfTiling hstone
      (positiveYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega)
      (by
        apply mem_positiveYChosen_of_zeroWord x y z arms
        apply (mem_labelZeroWordBonePlacements_iff arms.1
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelZeroPrefixBoneEdge_mem hstone
    (positiveYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelZeroPrefixBoneEdge_label hstone
    (positiveYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelZeroPrefixBoneEdge_move hstone
    (positiveYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelZeroPrefixBoneEdge_target,
      labelZeroPrefixBoneEdge_source]
    subst pre₁
    rfl

theorem positiveLabelZeroWord_nonempty (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    recursiveBallotWord arms.1 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.1
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_positiveLabelZeroWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (positiveYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (positiveYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.1 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (positiveLabelZeroEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelZeroWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def positiveLabelZeroTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
    arms.1 (recursiveBallotWord arms.1) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .zero .majority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using positive_labelZero_terminal_step x y z arms.1
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelZeroPrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.1 (recursiveBallotWord arms.1)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .zero
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = positiveLabelZeroTerminalBone x y z arms.1 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (positiveYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_positiveYChosen_zeroTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (positiveYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem positiveLabelZeroTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    positiveLabelZeroTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (positiveYLiteralTiling x y z arms) := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem positiveLabelZeroTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelZeroTerminalEdge hstone x y z arms).source =
      labelZeroPrefixSimplexPoint (t := x + y + z + 3) arms.1
        (recursiveBallotWord arms.1) List.prefix_rfl (by omega) := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem positiveLabelZeroTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelZeroTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem positiveLabelZeroTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelZeroTerminalEdge hstone x y z arms).boneClass.label =
      .zero := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelZeroTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelZeroTerminalEdge hstone x y z arms).boneClass.step =
      stepC := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelZeroTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelZeroTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .majority := by
  unfold positiveLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_positiveLabelZeroFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (positiveYLiteralTiling x y z arms)
          first (positiveLabelZeroTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (positiveLabelZeroTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.1 ++ [.majority] ∧
        first.source = sourceZero (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (positiveLabelZeroEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelZeroWord_nonempty x y z arms)
  let terminal := positiveLabelZeroTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, positiveLabelZeroTerminalEdge_source]
    simp only [positiveLabelZeroEdgeSystem]
    rw [
      labelZeroPrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelZeroPrefixSimplexPoint,
      simplexPointToInt_labelZeroPrefixSimplexPoint]
    exact congrArg (labelZeroPrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, positiveLabelZeroTerminalEdge_label]
    simp only [positiveLabelZeroEdgeSystem]
    rw [
      labelZeroPrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (positiveLabelZeroTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      positiveLabelZeroTerminalEdge_move]
  · rw [hfirst]
    simp only [positiveLabelZeroEdgeSystem]
    rw [labelZeroPrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceZero, labelZeroPrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelZeroPrefixPoint,
        majorityCount, minorityCount] <;> omega

noncomputable def positiveLabelOneEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    WordEdgeSystem hstone (positiveYLiteralTiling x y z arms)
      (recursiveBallotWord arms.2.1) .one where
  edge pre move hp :=
    labelOnePrefixBoneEdgeOfTiling hstone
      (positiveYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega)
      (by
        apply mem_positiveYChosen_of_oneWord x y z arms
        apply (mem_labelOneWordBonePlacements_iff arms.2.1
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelOnePrefixBoneEdge_mem hstone
    (positiveYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelOnePrefixBoneEdge_label hstone
    (positiveYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelOnePrefixBoneEdge_move hstone
    (positiveYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelOnePrefixBoneEdge_target,
      labelOnePrefixBoneEdge_source]
    subst pre₁
    rfl

theorem positiveLabelOneWord_nonempty (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    recursiveBallotWord arms.2.1 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.2.1
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_positiveLabelOneWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (positiveYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (positiveYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.2.1 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (positiveLabelOneEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelOneWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def positiveLabelOneTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
    arms.2.1 (recursiveBallotWord arms.2.1) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .one .majority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using positive_labelOne_terminal_step x y z arms.2.1
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelOnePrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.2.1 (recursiveBallotWord arms.2.1)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .one
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = positiveLabelOneTerminalBone x y z arms.2.1 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (positiveYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_positiveYChosen_oneTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (positiveYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem positiveLabelOneTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    positiveLabelOneTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (positiveYLiteralTiling x y z arms) := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem positiveLabelOneTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelOneTerminalEdge hstone x y z arms).source =
      labelOnePrefixSimplexPoint (t := x + y + z + 3) arms.2.1
        (recursiveBallotWord arms.2.1) List.prefix_rfl (by omega) := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem positiveLabelOneTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelOneTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem positiveLabelOneTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelOneTerminalEdge hstone x y z arms).boneClass.label =
      .one := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelOneTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelOneTerminalEdge hstone x y z arms).boneClass.step =
      stepB := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelOneTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelOneTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .majority := by
  unfold positiveLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_positiveLabelOneFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (positiveYLiteralTiling x y z arms)
          first (positiveLabelOneTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (positiveLabelOneTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.2.1 ++ [.majority] ∧
        first.source = sourceOne (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (positiveLabelOneEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelOneWord_nonempty x y z arms)
  let terminal := positiveLabelOneTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, positiveLabelOneTerminalEdge_source]
    simp only [positiveLabelOneEdgeSystem]
    rw [
      labelOnePrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelOnePrefixSimplexPoint,
      simplexPointToInt_labelOnePrefixSimplexPoint]
    exact congrArg (labelOnePrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, positiveLabelOneTerminalEdge_label]
    simp only [positiveLabelOneEdgeSystem]
    rw [
      labelOnePrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (positiveLabelOneTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      positiveLabelOneTerminalEdge_move]
  · rw [hfirst]
    simp only [positiveLabelOneEdgeSystem]
    rw [labelOnePrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceOne, labelOnePrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelOnePrefixPoint,
        majorityCount, minorityCount] <;> omega

noncomputable def positiveLabelTwoEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    WordEdgeSystem hstone (positiveYLiteralTiling x y z arms)
      (recursiveBallotWord arms.2.2) .two where
  edge pre move hp :=
    labelTwoPrefixBoneEdgeOfTiling hstone
      (positiveYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega)
      (by
        apply mem_positiveYChosen_of_twoWord x y z arms
        apply (mem_labelTwoWordBonePlacements_iff arms.2.2
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelTwoPrefixBoneEdge_mem hstone
    (positiveYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelTwoPrefixBoneEdge_label hstone
    (positiveYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelTwoPrefixBoneEdge_move hstone
    (positiveYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelTwoPrefixBoneEdge_target,
      labelTwoPrefixBoneEdge_source]
    subst pre₁
    rfl

theorem positiveLabelTwoWord_nonempty (x y z : ℕ)
    (arms : PositiveArmTriple x y z) :
    recursiveBallotWord arms.2.2 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.2.2
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_positiveLabelTwoWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (positiveYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (positiveYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.2.2 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (positiveLabelTwoEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelTwoWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def positiveLabelTwoTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
    arms.2.2 (recursiveBallotWord arms.2.2) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .two .majority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using positive_labelTwo_terminal_step x y z arms.2.2
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelTwoPrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.2.2 (recursiveBallotWord arms.2.2)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .two
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = positiveLabelTwoTerminalBone x y z arms.2.2 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (positiveYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_positiveYChosen_twoTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (positiveYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem positiveLabelTwoTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    positiveLabelTwoTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (positiveYLiteralTiling x y z arms) := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem positiveLabelTwoTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelTwoTerminalEdge hstone x y z arms).source =
      labelTwoPrefixSimplexPoint (t := x + y + z + 3) arms.2.2
        (recursiveBallotWord arms.2.2) List.prefix_rfl (by omega) := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem positiveLabelTwoTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelTwoTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem positiveLabelTwoTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelTwoTerminalEdge hstone x y z arms).boneClass.label =
      .two := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelTwoTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelTwoTerminalEdge hstone x y z arms).boneClass.step =
      stepA := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem positiveLabelTwoTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    (positiveLabelTwoTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .majority := by
  unfold positiveLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_positiveLabelTwoFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (positiveYLiteralTiling x y z arms)
          first (positiveLabelTwoTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (positiveLabelTwoTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.2.2 ++ [.majority] ∧
        first.source = sourceTwo (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (positiveLabelTwoEdgeSystem hstone x y z arms).nonempty_path
      (positiveLabelTwoWord_nonempty x y z arms)
  let terminal := positiveLabelTwoTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, positiveLabelTwoTerminalEdge_source]
    simp only [positiveLabelTwoEdgeSystem]
    rw [
      labelTwoPrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelTwoPrefixSimplexPoint,
      simplexPointToInt_labelTwoPrefixSimplexPoint]
    exact congrArg (labelTwoPrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, positiveLabelTwoTerminalEdge_label]
    simp only [positiveLabelTwoEdgeSystem]
    rw [
      labelTwoPrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (positiveLabelTwoTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      positiveLabelTwoTerminalEdge_move]
  · rw [hfirst]
    simp only [positiveLabelTwoEdgeSystem]
    rw [labelTwoPrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceTwo, labelTwoPrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelTwoPrefixPoint,
        majorityCount, minorityCount] <;> omega

theorem positiveReconstructedSink_active
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    sinkPoint x y z ∈ activeOwnerFinset hstone
      (positiveYLiteralTiling x y z arms) := by
  have hmem := edge_target_mem_active hstone
    (positiveYLiteralTiling x y z arms)
    (positiveLabelZeroTerminalEdge hstone x y z arms)
    (positiveLabelZeroTerminalEdge_mem hstone x y z arms)
  simpa using hmem

theorem positiveReconstructedSink_no_out
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    sinkPoint x y z ∉ activeOwnerEdgeSourceFinset hstone
      (positiveYLiteralTiling x y z arms) := by
  intro houtSource
  simp only [activeOwnerEdgeSourceFinset, Finset.mem_image] at houtSource
  obtain ⟨outEdge, hout, houtSource⟩ := houtSource
  have hzeroMeet :
      (positiveLabelZeroTerminalEdge hstone x y z arms).target =
        outEdge.source := by
    rw [positiveLabelZeroTerminalEdge_target, houtSource]
  have honeMeet :
      (positiveLabelOneTerminalEdge hstone x y z arms).target =
        outEdge.source := by
    rw [positiveLabelOneTerminalEdge_target, houtSource]
  have hzeroLabel := incoming_to_full_source_has_outgoing_label hstone
    (positiveYLiteralTiling x y z arms)
    (positiveLabelZeroTerminalEdge hstone x y z arms) outEdge
    (positiveLabelZeroTerminalEdge_mem hstone x y z arms) hout hzeroMeet
  have honeLabel := incoming_to_full_source_has_outgoing_label hstone
    (positiveYLiteralTiling x y z arms)
    (positiveLabelOneTerminalEdge hstone x y z arms) outEdge
    (positiveLabelOneTerminalEdge_mem hstone x y z arms) hout honeMeet
  rw [positiveLabelZeroTerminalEdge_label] at hzeroLabel
  rw [positiveLabelOneTerminalEdge_label] at honeLabel
  exact (by decide : MicroLabel.zero ≠ .one) (hzeroLabel.trans honeLabel.symm)

theorem exists_positiveLiteralYPathData
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : PositiveArmTriple x y z) :
    ∃ data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms),
      data.sink = sinkPoint x y z ∧
      data.zeroLast.boneClass.step = stepC ∧
      data.oneLast.boneClass.step = stepB ∧
      data.twoLast.boneClass.step = stepA ∧
      LiteralEdgePathData.ballotWord data.zeroFirst data.zeroLast data.zeroPath =
        recursiveBallotWord arms.1 ++ [.majority] ∧
      LiteralEdgePathData.ballotWord data.oneFirst data.oneLast data.onePath =
        recursiveBallotWord arms.2.1 ++ [.majority] ∧
      LiteralEdgePathData.ballotWord data.twoFirst data.twoLast data.twoPath =
        recursiveBallotWord arms.2.2 ++ [.majority] := by
  obtain ⟨zeroFirst, zeroPath, zeroWord, zeroSource⟩ :=
    exists_positiveLabelZeroFullPath hstone x y z arms
  obtain ⟨oneFirst, onePath, oneWord, oneSource⟩ :=
    exists_positiveLabelOneFullPath hstone x y z arms
  obtain ⟨twoFirst, twoPath, twoWord, twoSource⟩ :=
    exists_positiveLabelTwoFullPath hstone x y z arms
  let data : LiteralYPathData hstone (positiveYLiteralTiling x y z arms) :=
    { sink := sinkPoint x y z
      sink_active := positiveReconstructedSink_active hstone x y z arms
      sink_no_out := positiveReconstructedSink_no_out hstone x y z arms
      sink_positive := by simp [sinkPoint]; omega
      zeroFirst := zeroFirst
      zeroLast := positiveLabelZeroTerminalEdge hstone x y z arms
      oneFirst := oneFirst
      oneLast := positiveLabelOneTerminalEdge hstone x y z arms
      twoFirst := twoFirst
      twoLast := positiveLabelTwoTerminalEdge hstone x y z arms
      zeroPath := zeroPath
      onePath := onePath
      twoPath := twoPath
      zero_source := zeroSource
      one_source := oneSource
      two_source := twoSource
      zero_target := positiveLabelZeroTerminalEdge_target hstone x y z arms
      one_target := positiveLabelOneTerminalEdge_target hstone x y z arms
      two_target := positiveLabelTwoTerminalEdge_target hstone x y z arms
      zero_label := positiveLabelZeroTerminalEdge_label hstone x y z arms
      one_label := positiveLabelOneTerminalEdge_label hstone x y z arms
      two_label := positiveLabelTwoTerminalEdge_label hstone x y z arms }
  exact ⟨data, rfl, positiveLabelZeroTerminalEdge_step hstone x y z arms,
    positiveLabelOneTerminalEdge_step hstone x y z arms,
    positiveLabelTwoTerminalEdge_step hstone x y z arms,
    zeroWord, oneWord, twoWord⟩

end BenzelProblem6Kernel

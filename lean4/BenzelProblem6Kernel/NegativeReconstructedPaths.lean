import BenzelProblem6Kernel.WordEdgePathBuilder

/-!
# Explicit data-valued paths in a reconstructed negative-chirality tiling
-/

namespace BenzelProblem6Kernel

noncomputable def negativeLabelZeroEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    WordEdgeSystem hstone (negativeYLiteralTiling x y z arms)
      (recursiveBallotWord arms.1) .zero where
  edge pre move hp :=
    labelZeroPrefixBoneEdgeOfTiling hstone
      (negativeYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega)
      (by
        apply mem_negativeYChosen_of_zeroWord x y z arms
        apply (mem_labelZeroWordBonePlacements_iff arms.1
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelZeroPrefixBoneEdge_mem hstone
    (negativeYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelZeroPrefixBoneEdge_label hstone
    (negativeYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelZeroPrefixBoneEdge_move hstone
    (negativeYLiteralTiling x y z arms) arms.1 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelZeroPrefixBoneEdge_target,
      labelZeroPrefixBoneEdge_source]
    subst pre₁
    rfl

theorem negativeLabelZeroWord_nonempty (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    recursiveBallotWord arms.1 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.1
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_negativeLabelZeroWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (negativeYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (negativeYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.1 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (negativeLabelZeroEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelZeroWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def negativeLabelZeroTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelZeroPrefixSimplexPoint (t := x + y + z + 3)
    arms.1 (recursiveBallotWord arms.1) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .zero .minority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using negative_labelZero_terminal_step x y z arms.1
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelZeroPrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.1 (recursiveBallotWord arms.1)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .zero
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = negativeLabelZeroTerminalBone x y z arms.1 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (negativeYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_negativeYChosen_zeroTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (negativeYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem negativeLabelZeroTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    negativeLabelZeroTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (negativeYLiteralTiling x y z arms) := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem negativeLabelZeroTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelZeroTerminalEdge hstone x y z arms).source =
      labelZeroPrefixSimplexPoint (t := x + y + z + 3) arms.1
        (recursiveBallotWord arms.1) List.prefix_rfl (by omega) := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem negativeLabelZeroTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelZeroTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem negativeLabelZeroTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelZeroTerminalEdge hstone x y z arms).boneClass.label =
      .zero := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelZeroTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelZeroTerminalEdge hstone x y z arms).boneClass.step =
      stepA := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelZeroTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelZeroTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .minority := by
  unfold negativeLabelZeroTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_negativeLabelZeroFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (negativeYLiteralTiling x y z arms)
          first (negativeLabelZeroTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (negativeLabelZeroTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.1 ++ [.minority] ∧
        first.source = sourceZero (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (negativeLabelZeroEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelZeroWord_nonempty x y z arms)
  let terminal := negativeLabelZeroTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, negativeLabelZeroTerminalEdge_source]
    simp only [negativeLabelZeroEdgeSystem]
    rw [
      labelZeroPrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelZeroPrefixSimplexPoint,
      simplexPointToInt_labelZeroPrefixSimplexPoint]
    exact congrArg (labelZeroPrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, negativeLabelZeroTerminalEdge_label]
    simp only [negativeLabelZeroEdgeSystem]
    rw [
      labelZeroPrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (negativeLabelZeroTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      negativeLabelZeroTerminalEdge_move]
  · rw [hfirst]
    simp only [negativeLabelZeroEdgeSystem]
    rw [labelZeroPrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceZero, labelZeroPrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelZeroPrefixPoint,
        majorityCount, minorityCount] <;> omega

noncomputable def negativeLabelOneEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    WordEdgeSystem hstone (negativeYLiteralTiling x y z arms)
      (recursiveBallotWord arms.2.1) .one where
  edge pre move hp :=
    labelOnePrefixBoneEdgeOfTiling hstone
      (negativeYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega)
      (by
        apply mem_negativeYChosen_of_oneWord x y z arms
        apply (mem_labelOneWordBonePlacements_iff arms.2.1
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelOnePrefixBoneEdge_mem hstone
    (negativeYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelOnePrefixBoneEdge_label hstone
    (negativeYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelOnePrefixBoneEdge_move hstone
    (negativeYLiteralTiling x y z arms) arms.2.1 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelOnePrefixBoneEdge_target,
      labelOnePrefixBoneEdge_source]
    subst pre₁
    rfl

theorem negativeLabelOneWord_nonempty (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    recursiveBallotWord arms.2.1 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.2.1
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_negativeLabelOneWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (negativeYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (negativeYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.2.1 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (negativeLabelOneEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelOneWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def negativeLabelOneTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelOnePrefixSimplexPoint (t := x + y + z + 3)
    arms.2.1 (recursiveBallotWord arms.2.1) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .one .minority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using negative_labelOne_terminal_step x y z arms.2.1
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelOnePrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.2.1 (recursiveBallotWord arms.2.1)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .one
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = negativeLabelOneTerminalBone x y z arms.2.1 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (negativeYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_negativeYChosen_oneTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (negativeYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem negativeLabelOneTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    negativeLabelOneTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (negativeYLiteralTiling x y z arms) := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem negativeLabelOneTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelOneTerminalEdge hstone x y z arms).source =
      labelOnePrefixSimplexPoint (t := x + y + z + 3) arms.2.1
        (recursiveBallotWord arms.2.1) List.prefix_rfl (by omega) := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem negativeLabelOneTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelOneTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem negativeLabelOneTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelOneTerminalEdge hstone x y z arms).boneClass.label =
      .one := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelOneTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelOneTerminalEdge hstone x y z arms).boneClass.step =
      stepC := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelOneTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelOneTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .minority := by
  unfold negativeLabelOneTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_negativeLabelOneFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (negativeYLiteralTiling x y z arms)
          first (negativeLabelOneTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (negativeLabelOneTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.2.1 ++ [.minority] ∧
        first.source = sourceOne (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (negativeLabelOneEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelOneWord_nonempty x y z arms)
  let terminal := negativeLabelOneTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, negativeLabelOneTerminalEdge_source]
    simp only [negativeLabelOneEdgeSystem]
    rw [
      labelOnePrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelOnePrefixSimplexPoint,
      simplexPointToInt_labelOnePrefixSimplexPoint]
    exact congrArg (labelOnePrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, negativeLabelOneTerminalEdge_label]
    simp only [negativeLabelOneEdgeSystem]
    rw [
      labelOnePrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (negativeLabelOneTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      negativeLabelOneTerminalEdge_move]
  · rw [hfirst]
    simp only [negativeLabelOneEdgeSystem]
    rw [labelOnePrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceOne, labelOnePrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelOnePrefixPoint,
        majorityCount, minorityCount] <;> omega

noncomputable def negativeLabelTwoEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    WordEdgeSystem hstone (negativeYLiteralTiling x y z arms)
      (recursiveBallotWord arms.2.2) .two where
  edge pre move hp :=
    labelTwoPrefixBoneEdgeOfTiling hstone
      (negativeYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega)
      (by
        apply mem_negativeYChosen_of_twoWord x y z arms
        apply (mem_labelTwoWordBonePlacements_iff arms.2.2
          (by omega) (by omega) _).2
        exact ⟨pre, move, hp, rfl⟩)
  mem pre move hp := labelTwoPrefixBoneEdge_mem hstone
    (negativeYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  edgeLabel pre move hp := labelTwoPrefixBoneEdge_label hstone
    (negativeYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  edgeMove pre move hp := labelTwoPrefixBoneEdge_move hstone
    (negativeYLiteralTiling x y z arms) arms.2.2 pre move hp
      (by omega) (by omega) _
  meet pre₀ move₀ hp₀ pre₁ move₁ hp₁ hpre := by
    rw [labelTwoPrefixBoneEdge_target,
      labelTwoPrefixBoneEdge_source]
    subst pre₁
    rfl

theorem negativeLabelTwoWord_nonempty (x y z : ℕ)
    (arms : NegativeArmTriple x y z) :
    recursiveBallotWord arms.2.2 ≠ [] := by
  intro hempty
  have hlen := recursiveBallotWord_length arms.2.2
  rw [hempty] at hlen
  simp at hlen
  omega

theorem exists_negativeLabelTwoWordPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first last : LiteralDirectedEdge (x + y + z),
      Nonempty (LiteralEdgePathData hstone
        (negativeYLiteralTiling x y z arms) first last) ∧
      ∃ path : LiteralEdgePathData hstone
          (negativeYLiteralTiling x y z arms) first last,
        LiteralEdgePathData.ballotWord first last path =
          recursiveBallotWord arms.2.2 := by
  obtain ⟨first, last, hpath, path, hword, _⟩ :=
    (negativeLabelTwoEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelTwoWord_nonempty x y z arms)
  exact ⟨first, last, hpath, path, hword⟩

noncomputable def negativeLabelTwoTerminalEdge
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    LiteralDirectedEdge (x + y + z) := by
  let source := labelTwoPrefixSimplexPoint (t := x + y + z + 3)
    arms.2.2 (recursiveBallotWord arms.2.2) List.prefix_rfl (by omega)
  let target := sinkPoint x y z
  let boneClass := goodBoneClassOfMove .two .minority
  let hstep : addCell (ownerQ source, ownerR source) boneClass.step =
      (ownerQ target, ownerR target) := by
    simpa [source, target, boneClass, goodBoneClassOfMove,
      GoodBoneClass.step] using negative_labelTwo_terminal_step x y z arms.2.2
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (x + y + z + 5) (ownerCell source label) := by
    simpa [source, boneClass] using labelTwoPrefix_source_cells_mem_of_prefix
      (m := x + y + z) arms.2.2 (recursiveBallotWord arms.2.2)
        List.prefix_rfl (by omega) (by omega)
  let htargetMem : inPeripheralBenzel (x + y + z + 5)
      (ownerCell target boneClass.label) := by
    simpa [target, boneClass] using sinkPoint_ownerCell_mem x y z .two
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem = negativeLabelTwoTerminalBone x y z arms.2.2 := by
    apply Subtype.ext
    rfl
  have hplacement : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ (negativeYLiteralTiling x y z arms).1 := by
    rw [heq]
    exact mem_negativeYChosen_twoTerminal x y z arms
  exact reverseBoneEdgeOfTiling hstone (negativeYLiteralTiling x y z arms)
    source target boneClass hstep hsourceMem htargetMem hplacement

theorem negativeLabelTwoTerminalEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    negativeLabelTwoTerminalEdge hstone x y z arms ∈
      literalDirectedEdges hstone (negativeYLiteralTiling x y z arms) := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem negativeLabelTwoTerminalEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelTwoTerminalEdge hstone x y z arms).source =
      labelTwoPrefixSimplexPoint (t := x + y + z + 3) arms.2.2
        (recursiveBallotWord arms.2.2) List.prefix_rfl (by omega) := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem negativeLabelTwoTerminalEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelTwoTerminalEdge hstone x y z arms).target =
      sinkPoint x y z := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem negativeLabelTwoTerminalEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelTwoTerminalEdge hstone x y z arms).boneClass.label =
      .two := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelTwoTerminalEdge_step
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelTwoTerminalEdge hstone x y z arms).boneClass.step =
      stepB := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

@[simp] theorem negativeLabelTwoTerminalEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    (negativeLabelTwoTerminalEdge hstone x y z arms).boneClass.ballotMove =
      .minority := by
  unfold negativeLabelTwoTerminalEdge
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  rfl

theorem exists_negativeLabelTwoFullPath
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ first : LiteralDirectedEdge (x + y + z),
      ∃ path : LiteralEdgePathData hstone (negativeYLiteralTiling x y z arms)
          first (negativeLabelTwoTerminalEdge hstone x y z arms),
        LiteralEdgePathData.ballotWord first
            (negativeLabelTwoTerminalEdge hstone x y z arms) path =
          recursiveBallotWord arms.2.2 ++ [.minority] ∧
        first.source = sourceTwo (x + y + z + 3) := by
  obtain ⟨first, last, _, wordPath, hword, firstMove, hpFirst,
      hfirst, lastPre, lastMove, hpLast, hlastWord, hlast⟩ :=
    (negativeLabelTwoEdgeSystem hstone x y z arms).nonempty_path
      (negativeLabelTwoWord_nonempty x y z arms)
  let terminal := negativeLabelTwoTerminalEdge hstone x y z arms
  have hmeet : last.target = terminal.source := by
    rw [hlast, negativeLabelTwoTerminalEdge_source]
    simp only [negativeLabelTwoEdgeSystem]
    rw [
      labelTwoPrefixBoneEdge_target]
    apply simplexPointToInt_injective
    rw [simplexPointToInt_labelTwoPrefixSimplexPoint,
      simplexPointToInt_labelTwoPrefixSimplexPoint]
    exact congrArg (labelTwoPrefixPoint (x + y + z + 3)) hlastWord.symm
  have hlabel : last.boneClass.label = terminal.boneClass.label := by
    rw [hlast, negativeLabelTwoTerminalEdge_label]
    simp only [negativeLabelTwoEdgeSystem]
    rw [
      labelTwoPrefixBoneEdge_label]
  let fullPath := LiteralEdgePathData.snoc wordPath
    (negativeLabelTwoTerminalEdge_mem hstone x y z arms) hmeet hlabel
  refine ⟨first, fullPath, ?_, ?_⟩
  · simp [fullPath, LiteralEdgePathData.ballotWord, hword,
      negativeLabelTwoTerminalEdge_move]
  · rw [hfirst]
    simp only [negativeLabelTwoEdgeSystem]
    rw [labelTwoPrefixBoneEdge_source]
    apply simplexPoint_ext <;>
      simp [sourceTwo, labelTwoPrefixSimplexPoint,
        IntSimplex.toSimplexPoint, labelTwoPrefixPoint,
        majorityCount, minorityCount] <;> omega

theorem negativeReconstructedSink_active
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    sinkPoint x y z ∈ activeOwnerFinset hstone
      (negativeYLiteralTiling x y z arms) := by
  have hmem := edge_target_mem_active hstone
    (negativeYLiteralTiling x y z arms)
    (negativeLabelZeroTerminalEdge hstone x y z arms)
    (negativeLabelZeroTerminalEdge_mem hstone x y z arms)
  simpa using hmem

theorem negativeReconstructedSink_no_out
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    sinkPoint x y z ∉ activeOwnerEdgeSourceFinset hstone
      (negativeYLiteralTiling x y z arms) := by
  intro houtSource
  simp only [activeOwnerEdgeSourceFinset, Finset.mem_image] at houtSource
  obtain ⟨outEdge, hout, houtSource⟩ := houtSource
  have hzeroMeet :
      (negativeLabelZeroTerminalEdge hstone x y z arms).target =
        outEdge.source := by
    rw [negativeLabelZeroTerminalEdge_target, houtSource]
  have honeMeet :
      (negativeLabelOneTerminalEdge hstone x y z arms).target =
        outEdge.source := by
    rw [negativeLabelOneTerminalEdge_target, houtSource]
  have hzeroLabel := incoming_to_full_source_has_outgoing_label hstone
    (negativeYLiteralTiling x y z arms)
    (negativeLabelZeroTerminalEdge hstone x y z arms) outEdge
    (negativeLabelZeroTerminalEdge_mem hstone x y z arms) hout hzeroMeet
  have honeLabel := incoming_to_full_source_has_outgoing_label hstone
    (negativeYLiteralTiling x y z arms)
    (negativeLabelOneTerminalEdge hstone x y z arms) outEdge
    (negativeLabelOneTerminalEdge_mem hstone x y z arms) hout honeMeet
  rw [negativeLabelZeroTerminalEdge_label] at hzeroLabel
  rw [negativeLabelOneTerminalEdge_label] at honeLabel
  exact (by decide : MicroLabel.zero ≠ .one) (hzeroLabel.trans honeLabel.symm)

theorem exists_negativeLiteralYPathData
    (hstone : conwayLagariasStoneCountTarget)
    (x y z : ℕ) (arms : NegativeArmTriple x y z) :
    ∃ data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms),
      data.sink = sinkPoint x y z ∧
      data.zeroLast.boneClass.step = stepA ∧
      data.oneLast.boneClass.step = stepC ∧
      data.twoLast.boneClass.step = stepB ∧
      LiteralEdgePathData.ballotWord data.zeroFirst data.zeroLast data.zeroPath =
        recursiveBallotWord arms.1 ++ [.minority] ∧
      LiteralEdgePathData.ballotWord data.oneFirst data.oneLast data.onePath =
        recursiveBallotWord arms.2.1 ++ [.minority] ∧
      LiteralEdgePathData.ballotWord data.twoFirst data.twoLast data.twoPath =
        recursiveBallotWord arms.2.2 ++ [.minority] := by
  obtain ⟨zeroFirst, zeroPath, zeroWord, zeroSource⟩ :=
    exists_negativeLabelZeroFullPath hstone x y z arms
  obtain ⟨oneFirst, onePath, oneWord, oneSource⟩ :=
    exists_negativeLabelOneFullPath hstone x y z arms
  obtain ⟨twoFirst, twoPath, twoWord, twoSource⟩ :=
    exists_negativeLabelTwoFullPath hstone x y z arms
  let data : LiteralYPathData hstone (negativeYLiteralTiling x y z arms) :=
    { sink := sinkPoint x y z
      sink_active := negativeReconstructedSink_active hstone x y z arms
      sink_no_out := negativeReconstructedSink_no_out hstone x y z arms
      sink_positive := by simp [sinkPoint]; omega
      zeroFirst := zeroFirst
      zeroLast := negativeLabelZeroTerminalEdge hstone x y z arms
      oneFirst := oneFirst
      oneLast := negativeLabelOneTerminalEdge hstone x y z arms
      twoFirst := twoFirst
      twoLast := negativeLabelTwoTerminalEdge hstone x y z arms
      zeroPath := zeroPath
      onePath := onePath
      twoPath := twoPath
      zero_source := zeroSource
      one_source := oneSource
      two_source := twoSource
      zero_target := negativeLabelZeroTerminalEdge_target hstone x y z arms
      one_target := negativeLabelOneTerminalEdge_target hstone x y z arms
      two_target := negativeLabelTwoTerminalEdge_target hstone x y z arms
      zero_label := negativeLabelZeroTerminalEdge_label hstone x y z arms
      one_label := negativeLabelOneTerminalEdge_label hstone x y z arms
      two_label := negativeLabelTwoTerminalEdge_label hstone x y z arms }
  exact ⟨data, rfl, negativeLabelZeroTerminalEdge_step hstone x y z arms,
    negativeLabelOneTerminalEdge_step hstone x y z arms,
    negativeLabelTwoTerminalEdge_step hstone x y z arms,
    zeroWord, oneWord, twoWord⟩

end BenzelProblem6Kernel

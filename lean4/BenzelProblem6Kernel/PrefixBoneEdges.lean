import BenzelProblem6Kernel.ReverseBoneDirectedEdge

/-!
# Reconstructed prefix placements as directed edges of a chosen tiling
-/

namespace BenzelProblem6Kernel

noncomputable def labelZeroPrefixBoneEdgeOfTiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) : LiteralDirectedEdge m := by
  let hpSource := (List.prefix_append pre [move]).trans hp
  let source := labelZeroPrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelZeroPrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .zero move
  let hstep := labelZeroPrefix_owner_step (t := m + 3)
    path pre move hp (by omega)
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label) := by
      intro label hne
      apply labelZeroPrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne
  let htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label) := by
    simpa [boneClass] using labelZeroPrefix_target_cell_mem path pre move hp hup
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem =
      labelZeroPrefixBonePlacement path pre move hp hup hdown := by
    apply Subtype.ext
    rfl
  have hplacement' : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1 := heq ▸ hplacement
  exact reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement'

theorem labelZeroPrefixBoneEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    labelZeroPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement ∈ literalDirectedEdges hstone tiling := by
  unfold labelZeroPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem labelZeroPrefixBoneEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelZeroPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).source =
      labelZeroPrefixSimplexPoint (t := m + 3) path pre
        ((List.prefix_append pre [move]).trans hp) (by omega) := by
  unfold labelZeroPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem labelZeroPrefixBoneEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelZeroPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).target =
      labelZeroPrefixSimplexPoint (t := m + 3) path (pre ++ [move]) hp
        (by omega) := by
  unfold labelZeroPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem labelZeroPrefixBoneEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelZeroPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.label = .zero := by
  unfold labelZeroPrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

@[simp] theorem labelZeroPrefixBoneEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelZeroPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelZeroPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.ballotMove = move := by
  unfold labelZeroPrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

noncomputable def labelOnePrefixBoneEdgeOfTiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) : LiteralDirectedEdge m := by
  let hpSource := (List.prefix_append pre [move]).trans hp
  let source := labelOnePrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelOnePrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .one move
  let hstep := labelOnePrefix_owner_step (t := m + 3)
    path pre move hp (by omega)
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label) := by
      intro label hne
      apply labelOnePrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne
  let htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label) := by
    simpa [boneClass] using labelOnePrefix_target_cell_mem path pre move hp hup
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem =
      labelOnePrefixBonePlacement path pre move hp hup hdown := by
    apply Subtype.ext
    rfl
  have hplacement' : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1 := heq ▸ hplacement
  exact reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement'

theorem labelOnePrefixBoneEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    labelOnePrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement ∈ literalDirectedEdges hstone tiling := by
  unfold labelOnePrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem labelOnePrefixBoneEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelOnePrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).source =
      labelOnePrefixSimplexPoint (t := m + 3) path pre
        ((List.prefix_append pre [move]).trans hp) (by omega) := by
  unfold labelOnePrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem labelOnePrefixBoneEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelOnePrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).target =
      labelOnePrefixSimplexPoint (t := m + 3) path (pre ++ [move]) hp
        (by omega) := by
  unfold labelOnePrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem labelOnePrefixBoneEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelOnePrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.label = .one := by
  unfold labelOnePrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

@[simp] theorem labelOnePrefixBoneEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelOnePrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelOnePrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.ballotMove = move := by
  unfold labelOnePrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

noncomputable def labelTwoPrefixBoneEdgeOfTiling
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) : LiteralDirectedEdge m := by
  let hpSource := (List.prefix_append pre [move]).trans hp
  let source := labelTwoPrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelTwoPrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .two move
  let hstep := labelTwoPrefix_owner_step (t := m + 3)
    path pre move hp (by omega)
  let hsourceMem : ∀ label, label ≠ boneClass.label →
      inPeripheralBenzel (m + 5) (ownerCell source label) := by
      intro label hne
      apply labelTwoPrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne
  let htargetMem : inPeripheralBenzel (m + 5)
      (ownerCell target boneClass.label) := by
    simpa [boneClass] using labelTwoPrefix_target_cell_mem path pre move hp hup
  have heq : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem =
      labelTwoPrefixBonePlacement path pre move hp hup hdown := by
    apply Subtype.ext
    rfl
  have hplacement' : reverseBonePlacement source target boneClass hstep
      hsourceMem htargetMem ∈ tiling.1 := heq ▸ hplacement
  exact reverseBoneEdgeOfTiling hstone tiling source target boneClass
    hstep hsourceMem htargetMem hplacement'

theorem labelTwoPrefixBoneEdge_mem
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    labelTwoPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement ∈ literalDirectedEdges hstone tiling := by
  unfold labelTwoPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_mem

@[simp] theorem labelTwoPrefixBoneEdge_source
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelTwoPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).source =
      labelTwoPrefixSimplexPoint (t := m + 3) path pre
        ((List.prefix_append pre [move]).trans hp) (by omega) := by
  unfold labelTwoPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_source

@[simp] theorem labelTwoPrefixBoneEdge_target
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelTwoPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).target =
      labelTwoPrefixSimplexPoint (t := m + 3) path (pre ++ [move]) hp
        (by omega) := by
  unfold labelTwoPrefixBoneEdgeOfTiling
  dsimp only
  apply reverseBoneEdgeOfTiling_target

@[simp] theorem labelTwoPrefixBoneEdge_label
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelTwoPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.label = .two := by
  unfold labelTwoPrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

@[simp] theorem labelTwoPrefixBoneEdge_move
    (hstone : conwayLagariasStoneCountTarget)
    {up down m : ℕ} (tiling : LiteralTiling m)
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hplacement : labelTwoPrefixBonePlacement path pre move hp hup hdown ∈
      tiling.1) :
    (labelTwoPrefixBoneEdgeOfTiling hstone tiling path pre move hp hup hdown
      hplacement).boneClass.ballotMove = move := by
  unfold labelTwoPrefixBoneEdgeOfTiling
  dsimp only
  rw [reverseBoneEdgeOfTiling_class]
  simp

end BenzelProblem6Kernel

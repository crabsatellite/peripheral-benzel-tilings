import BenzelProblem6Kernel.PrefixEdgeRegion

/-!
# The literal bone placement carried by one arm-word letter
-/

namespace BenzelProblem6Kernel

noncomputable def labelZeroPrefixBonePlacement {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) : LiteralPlacement m := by
  let hpSource : pre <+: recursiveBallotWord path :=
    (List.prefix_append pre [move]).trans hp
  let source := labelZeroPrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelZeroPrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .zero move
  exact reverseBonePlacement source target boneClass
    (labelZeroPrefix_owner_step path pre move hp (by omega))
    (by
      intro label hne
      apply labelZeroPrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne)
    (by
      simpa [boneClass] using
        labelZeroPrefix_target_cell_mem path pre move hp hup)

noncomputable def labelOnePrefixBonePlacement {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) : LiteralPlacement m := by
  let hpSource : pre <+: recursiveBallotWord path :=
    (List.prefix_append pre [move]).trans hp
  let source := labelOnePrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelOnePrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .one move
  exact reverseBonePlacement source target boneClass
    (labelOnePrefix_owner_step path pre move hp (by omega))
    (by
      intro label hne
      apply labelOnePrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne)
    (by
      simpa [boneClass] using
        labelOnePrefix_target_cell_mem path pre move hp hup)

noncomputable def labelTwoPrefixBonePlacement {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) : LiteralPlacement m := by
  let hpSource : pre <+: recursiveBallotWord path :=
    (List.prefix_append pre [move]).trans hp
  let source := labelTwoPrefixSimplexPoint (t := m + 3)
    path pre hpSource (by omega)
  let target := labelTwoPrefixSimplexPoint (t := m + 3)
    path (pre ++ [move]) hp (by omega)
  let boneClass := goodBoneClassOfMove .two move
  exact reverseBonePlacement source target boneClass
    (labelTwoPrefix_owner_step path pre move hp (by omega))
    (by
      intro label hne
      apply labelTwoPrefix_source_cells_mem path pre move hp hup hdown label
      simpa [boneClass] using hne)
    (by
      simpa [boneClass] using
        labelTwoPrefix_target_cell_mem path pre move hp hup)

end BenzelProblem6Kernel

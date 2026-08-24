import BenzelProblem6Kernel.PathModelRoundTrip

/-!
# Replaying literal path edges from their ballot-word prefixes
-/

namespace BenzelProblem6Kernel

def LiteralEdgePathData.placementList
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m} :
    {first last : LiteralDirectedEdge m} →
      LiteralEdgePathData hstone tiling first last → List (LiteralPlacement m)
  | _, _, .single edge _ => [edge.placement]
  | _, _, .snoc (next := next) path _ _ _ =>
      path.placementList ++ [next.placement]

theorem labelZero_edge_replays_at_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    (edge : LiteralDirectedEdge m)
    (pre : List BallotMove)
    (hp : pre ++ [edge.boneClass.ballotMove] <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : edge.boneClass.label = .zero)
    (hsource : edge.source = labelZeroPrefixSimplexPoint (t := m + 3)
      ballot pre ((List.prefix_append pre
        [edge.boneClass.ballotMove]).trans hp) (by omega)) :
    edge.target = labelZeroPrefixSimplexPoint (t := m + 3) ballot
        (pre ++ [edge.boneClass.ballotMove]) hp (by omega) ∧
      edge.placement = labelZeroPrefixBonePlacement ballot pre
        edge.boneClass.ballotMove hp hup hdown := by
  let move := edge.boneClass.ballotMove
  let hpPre := (List.prefix_append pre [move]).trans hp
  let source := labelZeroPrefixSimplexPoint (t := m + 3)
    ballot pre hpPre (by omega)
  let target := labelZeroPrefixSimplexPoint (t := m + 3)
    ballot (pre ++ [move]) hp (by omega)
  have hsource' : edge.source = source := by
    simpa [source, hpPre, move] using hsource
  have hclass : goodBoneClassOfMove .zero move = edge.boneClass := by
    rw [← hlabel]
    exact goodBoneClassOfMove_unique edge.boneClass
  have hstepClass : edge.boneClass.step =
      (goodBoneClassOfMove .zero move).step :=
    congrArg GoodBoneClass.step hclass.symm
  have htarget : edge.target = target := by
    apply owner_coordinates_injective
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelZeroPrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.fst (hedge.symm.trans hpref)
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelZeroPrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.snd (hedge.symm.trans hpref)
  constructor
  · exact htarget
  · rw [literalDirectedEdge_placement_eq_reverse edge]
    apply Subtype.ext
    apply Prod.ext
    · simpa [labelZeroPrefixBonePlacement, move, source, target, hpPre,
        hsource, htarget, hclass] using edge.class_spec.1
    · apply Subtype.ext
      change reverseBoneBase edge.source edge.boneClass =
        reverseBoneBase source (goodBoneClassOfMove .zero move)
      rw [hsource']
      apply Prod.ext
      · have hs := congrArg (fun bone => bone.sourceShift.1) hclass
        change ownerQ source - edge.boneClass.sourceShift.1 =
          ownerQ source - (goodBoneClassOfMove .zero move).sourceShift.1
        exact (congrArg (fun shift : ℤ => ownerQ source - shift) hs).symm
      · have hs := congrArg (fun bone => bone.sourceShift.2) hclass
        change ownerR source - edge.boneClass.sourceShift.2 =
          ownerR source - (goodBoneClassOfMove .zero move).sourceShift.2
        exact (congrArg (fun shift : ℤ => ownerR source - shift) hs).symm

theorem labelOne_edge_replays_at_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    (edge : LiteralDirectedEdge m)
    (pre : List BallotMove)
    (hp : pre ++ [edge.boneClass.ballotMove] <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : edge.boneClass.label = .one)
    (hsource : edge.source = labelOnePrefixSimplexPoint (t := m + 3)
      ballot pre ((List.prefix_append pre
        [edge.boneClass.ballotMove]).trans hp) (by omega)) :
    edge.target = labelOnePrefixSimplexPoint (t := m + 3) ballot
        (pre ++ [edge.boneClass.ballotMove]) hp (by omega) ∧
      edge.placement = labelOnePrefixBonePlacement ballot pre
        edge.boneClass.ballotMove hp hup hdown := by
  let move := edge.boneClass.ballotMove
  let hpPre := (List.prefix_append pre [move]).trans hp
  let source := labelOnePrefixSimplexPoint (t := m + 3)
    ballot pre hpPre (by omega)
  let target := labelOnePrefixSimplexPoint (t := m + 3)
    ballot (pre ++ [move]) hp (by omega)
  have hsource' : edge.source = source := by
    simpa [source, hpPre, move] using hsource
  have hclass : goodBoneClassOfMove .one move = edge.boneClass := by
    rw [← hlabel]
    exact goodBoneClassOfMove_unique edge.boneClass
  have hstepClass : edge.boneClass.step =
      (goodBoneClassOfMove .one move).step :=
    congrArg GoodBoneClass.step hclass.symm
  have htarget : edge.target = target := by
    apply owner_coordinates_injective
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelOnePrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.fst (hedge.symm.trans hpref)
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelOnePrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.snd (hedge.symm.trans hpref)
  constructor
  · exact htarget
  · rw [literalDirectedEdge_placement_eq_reverse edge]
    apply Subtype.ext
    apply Prod.ext
    · simpa [labelOnePrefixBonePlacement, move, source, target, hpPre,
        hsource, htarget, hclass] using edge.class_spec.1
    · apply Subtype.ext
      change reverseBoneBase edge.source edge.boneClass =
        reverseBoneBase source (goodBoneClassOfMove .one move)
      rw [hsource']
      apply Prod.ext
      · have hs := congrArg (fun bone => bone.sourceShift.1) hclass
        change ownerQ source - edge.boneClass.sourceShift.1 =
          ownerQ source - (goodBoneClassOfMove .one move).sourceShift.1
        exact (congrArg (fun shift : ℤ => ownerQ source - shift) hs).symm
      · have hs := congrArg (fun bone => bone.sourceShift.2) hclass
        change ownerR source - edge.boneClass.sourceShift.2 =
          ownerR source - (goodBoneClassOfMove .one move).sourceShift.2
        exact (congrArg (fun shift : ℤ => ownerR source - shift) hs).symm

theorem labelTwo_edge_replays_at_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    (edge : LiteralDirectedEdge m)
    (pre : List BallotMove)
    (hp : pre ++ [edge.boneClass.ballotMove] <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : edge.boneClass.label = .two)
    (hsource : edge.source = labelTwoPrefixSimplexPoint (t := m + 3)
      ballot pre ((List.prefix_append pre
        [edge.boneClass.ballotMove]).trans hp) (by omega)) :
    edge.target = labelTwoPrefixSimplexPoint (t := m + 3) ballot
        (pre ++ [edge.boneClass.ballotMove]) hp (by omega) ∧
      edge.placement = labelTwoPrefixBonePlacement ballot pre
        edge.boneClass.ballotMove hp hup hdown := by
  let move := edge.boneClass.ballotMove
  let hpPre := (List.prefix_append pre [move]).trans hp
  let source := labelTwoPrefixSimplexPoint (t := m + 3)
    ballot pre hpPre (by omega)
  let target := labelTwoPrefixSimplexPoint (t := m + 3)
    ballot (pre ++ [move]) hp (by omega)
  have hsource' : edge.source = source := by
    simpa [source, hpPre, move] using hsource
  have hclass : goodBoneClassOfMove .two move = edge.boneClass := by
    rw [← hlabel]
    exact goodBoneClassOfMove_unique edge.boneClass
  have hstepClass : edge.boneClass.step =
      (goodBoneClassOfMove .two move).step :=
    congrArg GoodBoneClass.step hclass.symm
  have htarget : edge.target = target := by
    apply owner_coordinates_injective
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelTwoPrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.fst (hedge.symm.trans hpref)
    · have hedge := literalDirectedEdge_anchor_step edge
      have hpref := labelTwoPrefix_owner_step (t := m + 3)
        ballot pre move hp (by omega)
      rw [hsource', hstepClass] at hedge
      exact congrArg Prod.snd (hedge.symm.trans hpref)
  constructor
  · exact htarget
  · rw [literalDirectedEdge_placement_eq_reverse edge]
    apply Subtype.ext
    apply Prod.ext
    · simpa [labelTwoPrefixBonePlacement, move, source, target, hpPre,
        hsource, htarget, hclass] using edge.class_spec.1
    · apply Subtype.ext
      change reverseBoneBase edge.source edge.boneClass =
        reverseBoneBase source (goodBoneClassOfMove .two move)
      rw [hsource']
      apply Prod.ext
      · have hs := congrArg (fun bone => bone.sourceShift.1) hclass
        change ownerQ source - edge.boneClass.sourceShift.1 =
          ownerQ source - (goodBoneClassOfMove .two move).sourceShift.1
        exact (congrArg (fun shift : ℤ => ownerQ source - shift) hs).symm
      · have hs := congrArg (fun bone => bone.sourceShift.2) hclass
        change ownerR source - edge.boneClass.sourceShift.2 =
          ownerR source - (goodBoneClassOfMove .two move).sourceShift.2
        exact (congrArg (fun shift : ℤ => ownerR source - shift) hs).symm

theorem labelZero_path_replays_from_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (pre : List BallotMove)
    (hpFull : pre ++ LiteralEdgePathData.ballotWord first last path <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : last.boneClass.label = .zero)
    (hsource : first.source = labelZeroPrefixSimplexPoint (t := m + 3)
      ballot pre (by
        exact (List.prefix_append pre
          (LiteralEdgePathData.ballotWord first last path)).trans hpFull)
        (by omega)) :
    last.target = labelZeroPrefixSimplexPoint (t := m + 3) ballot
        (pre ++ LiteralEdgePathData.ballotWord first last path) hpFull
        (by omega) ∧
      ∀ placement ∈ path.placementList,
        placement ∈ labelZeroWordBonePlacements ballot hup hdown := by
  induction path generalizing pre with
  | single hedge =>
      have hpEdge : pre ++ [first.boneClass.ballotMove] <+:
          recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord] using hpFull
      have hsource' : first.source = labelZeroPrefixSimplexPoint (t := m + 3)
          ballot pre ((List.prefix_append pre
            [first.boneClass.ballotMove]).trans hpEdge) (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have hreplay := labelZero_edge_replays_at_prefix (hstone := hstone)
        tiling ballot first pre
        hpEdge hup hdown hlabel hsource'
      constructor
      · simpa [LiteralEdgePathData.ballotWord] using hreplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_singleton] at hplacement
        subst placement
        apply (mem_labelZeroWordBonePlacements_iff ballot hup hdown _).2
        exact ⟨pre, first.boneClass.ballotMove, hpEdge, hreplay.2⟩
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpNext : (pre ++ LiteralEdgePathData.ballotWord first previous path) ++
          [next.boneClass.ballotMove] <+: recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord, List.append_assoc] using hpFull
      have hpPrefix : pre ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot :=
        (List.prefix_append _ [next.boneClass.ballotMove]).trans hpNext
      have hsourcePrefix : first.source = labelZeroPrefixSimplexPoint
          (t := m + 3) ballot pre
          ((List.prefix_append pre
            (LiteralEdgePathData.ballotWord first previous path)).trans hpPrefix)
          (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have ihResult := ih pre hpPrefix (hsame.trans hlabel) hsourcePrefix
      let nextPre := pre ++ LiteralEdgePathData.ballotWord first previous path
      have hnextSource : next.source = labelZeroPrefixSimplexPoint (t := m + 3)
          ballot nextPre ((List.prefix_append nextPre
            [next.boneClass.ballotMove]).trans hpNext) (by omega) := by
        rw [← hmeet, ihResult.1]
      have hnextReplay := labelZero_edge_replays_at_prefix (hstone := hstone)
        tiling ballot next
        nextPre hpNext hup hdown hlabel hnextSource
      constructor
      · simpa [LiteralEdgePathData.ballotWord, nextPre, List.append_assoc] using
          hnextReplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_append,
          List.mem_singleton] at hplacement
        rcases hplacement with hprefix | rfl
        · exact ihResult.2 placement hprefix
        · apply (mem_labelZeroWordBonePlacements_iff ballot hup hdown _).2
          exact ⟨nextPre, next.boneClass.ballotMove, hpNext,
            hnextReplay.2⟩

theorem labelOne_path_replays_from_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (pre : List BallotMove)
    (hpFull : pre ++ LiteralEdgePathData.ballotWord first last path <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : last.boneClass.label = .one)
    (hsource : first.source = labelOnePrefixSimplexPoint (t := m + 3)
      ballot pre (by
        exact (List.prefix_append pre
          (LiteralEdgePathData.ballotWord first last path)).trans hpFull)
        (by omega)) :
    last.target = labelOnePrefixSimplexPoint (t := m + 3) ballot
        (pre ++ LiteralEdgePathData.ballotWord first last path) hpFull
        (by omega) ∧
      ∀ placement ∈ path.placementList,
        placement ∈ labelOneWordBonePlacements ballot hup hdown := by
  induction path generalizing pre with
  | single hedge =>
      have hpEdge : pre ++ [first.boneClass.ballotMove] <+:
          recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord] using hpFull
      have hsource' : first.source = labelOnePrefixSimplexPoint (t := m + 3)
          ballot pre ((List.prefix_append pre
            [first.boneClass.ballotMove]).trans hpEdge) (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have hreplay := labelOne_edge_replays_at_prefix (hstone := hstone)
        tiling ballot first pre
        hpEdge hup hdown hlabel hsource'
      constructor
      · simpa [LiteralEdgePathData.ballotWord] using hreplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_singleton] at hplacement
        subst placement
        apply (mem_labelOneWordBonePlacements_iff ballot hup hdown _).2
        exact ⟨pre, first.boneClass.ballotMove, hpEdge, hreplay.2⟩
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpNext : (pre ++ LiteralEdgePathData.ballotWord first previous path) ++
          [next.boneClass.ballotMove] <+: recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord, List.append_assoc] using hpFull
      have hpPrefix : pre ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot :=
        (List.prefix_append _ [next.boneClass.ballotMove]).trans hpNext
      have hsourcePrefix : first.source = labelOnePrefixSimplexPoint
          (t := m + 3) ballot pre
          ((List.prefix_append pre
            (LiteralEdgePathData.ballotWord first previous path)).trans hpPrefix)
          (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have ihResult := ih pre hpPrefix (hsame.trans hlabel) hsourcePrefix
      let nextPre := pre ++ LiteralEdgePathData.ballotWord first previous path
      have hnextSource : next.source = labelOnePrefixSimplexPoint (t := m + 3)
          ballot nextPre ((List.prefix_append nextPre
            [next.boneClass.ballotMove]).trans hpNext) (by omega) := by
        rw [← hmeet, ihResult.1]
      have hnextReplay := labelOne_edge_replays_at_prefix (hstone := hstone)
        tiling ballot next
        nextPre hpNext hup hdown hlabel hnextSource
      constructor
      · simpa [LiteralEdgePathData.ballotWord, nextPre, List.append_assoc] using
          hnextReplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_append,
          List.mem_singleton] at hplacement
        rcases hplacement with hprefix | rfl
        · exact ihResult.2 placement hprefix
        · apply (mem_labelOneWordBonePlacements_iff ballot hup hdown _).2
          exact ⟨nextPre, next.boneClass.ballotMove, hpNext,
            hnextReplay.2⟩

theorem labelTwo_path_replays_from_prefix
    {hstone : conwayLagariasStoneCountTarget}
    {up down m : ℕ} (tiling : LiteralTiling m)
    (ballot : RecursiveBallot up down)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (pre : List BallotMove)
    (hpFull : pre ++ LiteralEdgePathData.ballotWord first last path <+:
      recursiveBallotWord ballot)
    (hup : up < m + 3) (hdown : down < m + 3)
    (hlabel : last.boneClass.label = .two)
    (hsource : first.source = labelTwoPrefixSimplexPoint (t := m + 3)
      ballot pre (by
        exact (List.prefix_append pre
          (LiteralEdgePathData.ballotWord first last path)).trans hpFull)
        (by omega)) :
    last.target = labelTwoPrefixSimplexPoint (t := m + 3) ballot
        (pre ++ LiteralEdgePathData.ballotWord first last path) hpFull
        (by omega) ∧
      ∀ placement ∈ path.placementList,
        placement ∈ labelTwoWordBonePlacements ballot hup hdown := by
  induction path generalizing pre with
  | single hedge =>
      have hpEdge : pre ++ [first.boneClass.ballotMove] <+:
          recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord] using hpFull
      have hsource' : first.source = labelTwoPrefixSimplexPoint (t := m + 3)
          ballot pre ((List.prefix_append pre
            [first.boneClass.ballotMove]).trans hpEdge) (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have hreplay := labelTwo_edge_replays_at_prefix (hstone := hstone)
        tiling ballot first pre
        hpEdge hup hdown hlabel hsource'
      constructor
      · simpa [LiteralEdgePathData.ballotWord] using hreplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_singleton] at hplacement
        subst placement
        apply (mem_labelTwoWordBonePlacements_iff ballot hup hdown _).2
        exact ⟨pre, first.boneClass.ballotMove, hpEdge, hreplay.2⟩
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpNext : (pre ++ LiteralEdgePathData.ballotWord first previous path) ++
          [next.boneClass.ballotMove] <+: recursiveBallotWord ballot := by
        simpa [LiteralEdgePathData.ballotWord, List.append_assoc] using hpFull
      have hpPrefix : pre ++ LiteralEdgePathData.ballotWord first previous path <+:
          recursiveBallotWord ballot :=
        (List.prefix_append _ [next.boneClass.ballotMove]).trans hpNext
      have hsourcePrefix : first.source = labelTwoPrefixSimplexPoint
          (t := m + 3) ballot pre
          ((List.prefix_append pre
            (LiteralEdgePathData.ballotWord first previous path)).trans hpPrefix)
          (by omega) := by
        simpa [LiteralEdgePathData.ballotWord] using hsource
      have ihResult := ih pre hpPrefix (hsame.trans hlabel) hsourcePrefix
      let nextPre := pre ++ LiteralEdgePathData.ballotWord first previous path
      have hnextSource : next.source = labelTwoPrefixSimplexPoint (t := m + 3)
          ballot nextPre ((List.prefix_append nextPre
            [next.boneClass.ballotMove]).trans hpNext) (by omega) := by
        rw [← hmeet, ihResult.1]
      have hnextReplay := labelTwo_edge_replays_at_prefix (hstone := hstone)
        tiling ballot next
        nextPre hpNext hup hdown hlabel hnextSource
      constructor
      · simpa [LiteralEdgePathData.ballotWord, nextPre, List.append_assoc] using
          hnextReplay.1
      · intro placement hplacement
        simp only [LiteralEdgePathData.placementList, List.mem_append,
          List.mem_singleton] at hplacement
        rcases hplacement with hprefix | rfl
        · exact ihResult.2 placement hprefix
        · apply (mem_labelTwoWordBonePlacements_iff ballot hup hdown _).2
          exact ⟨nextPre, next.boneClass.ballotMove, hpNext,
            hnextReplay.2⟩

end BenzelProblem6Kernel

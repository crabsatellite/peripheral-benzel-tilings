import BenzelProblem6Kernel.LiteralPathReconstruction

/-!
# Distinct placements carried by a data-valued literal path
-/

namespace BenzelProblem6Kernel

def LiteralEdgePathData.edgeList
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m} :
    {first last : LiteralDirectedEdge m} →
      LiteralEdgePathData hstone tiling first last → List (LiteralDirectedEdge m)
  | _, _, .single edge _ => [edge]
  | _, _, .snoc (next := next) path _ _ _ => path.edgeList ++ [next]

theorem LiteralEdgePathData.placementList_eq_map
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    path.placementList = path.edgeList.map LiteralDirectedEdge.placement := by
  induction path with
  | single => simp [LiteralEdgePathData.placementList,
      LiteralEdgePathData.edgeList]
  | snoc _ _ _ _ ih => simp [LiteralEdgePathData.placementList,
      LiteralEdgePathData.edgeList, ih]

theorem LiteralEdgePathData.edgeList_mem_directed
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    {edge : LiteralDirectedEdge m} (hmem : edge ∈ path.edgeList) :
    edge ∈ literalDirectedEdges hstone tiling := by
  induction path with
  | single hedge =>
      simp only [LiteralEdgePathData.edgeList, List.mem_singleton] at hmem
      subst edge
      exact hedge
  | snoc _ hnext _ _ ih =>
      simp only [LiteralEdgePathData.edgeList, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hprefix | rfl
      · exact ih hprefix
      · exact hnext

theorem LiteralEdgePathData.edgeList_rank_le_last
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    {edge : LiteralDirectedEdge m} (hmem : edge ∈ path.edgeList) :
    simplexLabelRank last.boneClass.label edge.source ≤
      simplexLabelRank last.boneClass.label last.source := by
  induction path with
  | single hedge =>
      simp only [LiteralEdgePathData.edgeList, List.mem_singleton] at hmem
      subst edge
      exact Nat.le_refl _
  | @snoc previous next path hnext hmeet hlabel ih =>
      simp only [LiteralEdgePathData.edgeList, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hprefix | rfl
      · have hle := ih hprefix
        rw [hlabel] at hle
        exact hle.trans (incoming_rank_lt_source_rank previous next
          hmeet hlabel).le
      · exact Nat.le_refl _

theorem LiteralEdgePathData.edgeList_nodup
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    path.edgeList.Nodup := by
  induction path with
  | single => simp [LiteralEdgePathData.edgeList]
  | @snoc previous next path hnext hmeet hlabel ih =>
      rw [LiteralEdgePathData.edgeList]
      apply List.Nodup.append ih (List.nodup_singleton _)
      rw [List.disjoint_left]
      intro edge hmem hedge
      simp only [List.mem_singleton] at hedge
      subst edge
      have hle := path.edgeList_rank_le_last hmem
      have hlt := incoming_rank_lt_source_rank previous next hmeet hlabel
      rw [← hlabel] at hlt
      omega

theorem LiteralEdgePathData.placementList_nodup
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    path.placementList.Nodup := by
  rw [path.placementList_eq_map]
  apply List.Nodup.map_on
  · intro left hleft right hright heq
    apply literalEdges_eq_of_placement_eq hstone tiling
      (path.edgeList_mem_directed hleft)
      (path.edgeList_mem_directed hright) heq
  · exact path.edgeList_nodup

theorem LiteralEdgePathData.placementList_length
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last) :
    path.placementList.length =
      (LiteralEdgePathData.ballotWord first last path).length := by
  induction path with
  | single => simp [LiteralEdgePathData.placementList,
      LiteralEdgePathData.ballotWord]
  | snoc _ _ _ _ ih =>
      simp [LiteralEdgePathData.placementList,
        LiteralEdgePathData.ballotWord, ih]

theorem LiteralEdgePathData.placementList_mem_tiling
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    {placement : LiteralPlacement m} (hmem : placement ∈ path.placementList) :
    placement ∈ tiling.1 := by
  rw [path.placementList_eq_map] at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨edge, hedge, rfl⟩ := hmem
  exact (mem_literalDirectedEdges_placement hstone tiling edge
    (path.edgeList_mem_directed hedge)).1

end BenzelProblem6Kernel

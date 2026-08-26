import D4KernelOnly.D4SelectedEndpointSupport
import BenzelProblem6Kernel.HexEdgeEndpointInjectivity
import BenzelProblem6Kernel.ConnectedGraphTreeCard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The finite tree supported by the d=4 terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem d4TilingComplex_edge_has_cellSide {m : ℕ}
    (tiling : D4LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ d4TilingComplexDirectedEdges tiling) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  rw [d4TilingComplexDirectedEdges, List.mem_append] at hedge
  rcases hedge with hedgeOuter | hedgeTiles
  · exact d4ReducedBoundaryEdge_has_cellSide hedgeOuter
  · rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at hedgeTiles
    obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
    have horiginal : reverseLabeledHexEdge edge ∈
        literalPlacementBoundary placement :=
      (mem_reverseReorientedEdges_iff edge _).mp hedgePlacement
    obtain ⟨owner, howner, hownerEdge⟩ :=
      literalPlacementBoundary_edge_has_cell placement horiginal
    obtain ⟨side, hside⟩ := labeledCellBoundary_edge_has_side hownerEdge
    refine ⟨neighboringCell owner side, oppositeHexSide side, ?_⟩
    rw [cellBoundaryEdgeAt_neighbor_exact, hside,
      reverseLabeledHexEdge_involutive]

theorem d4Terminal_edge_has_cellSide {m : ℕ}
    (tiling : D4LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ (d4ReducedRightmostTerminal tiling).edges) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  have haccount := d4Terminal_edgeAccounting_perm tiling
  have hedgeComplex : edge ∈ d4TilingComplexDirectedEdges tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  exact d4TilingComplex_edge_has_cellSide tiling hedgeComplex

theorem d4Terminal_edge_endpoint_injective {m : ℕ}
    (tiling : D4LiteralTiling m)
    {left right : LabeledHexEdge}
    (hleft : left ∈ (d4ReducedRightmostTerminal tiling).edges)
    (hright : right ∈ (d4ReducedRightmostTerminal tiling).edges)
    (hsource : left.source = right.source)
    (htarget : left.target = right.target) : left = right := by
  obtain ⟨leftCell, leftSide, hleftEq⟩ :=
    d4Terminal_edge_has_cellSide tiling hleft
  obtain ⟨rightCell, rightSide, hrightEq⟩ :=
    d4Terminal_edge_has_cellSide tiling hright
  rw [← hleftEq, ← hrightEq] at hsource htarget ⊢
  exact cellBoundaryEdgeAt_endpoint_injective
    leftCell rightCell leftSide rightSide hsource htarget

noncomputable def d4TerminalSupportGraph {m : ℕ}
    (tiling : D4LiteralTiling m) :
    SimpleGraph (↥(d4TilingBoundaryVertexFinset tiling)) where
  Adj left right := ∃ edge ∈ (d4ReducedRightmostTerminal tiling).edges,
    edge.source = left.1 ∧ edge.target = right.1
  symm := by
    rintro left right ⟨edge, hedge, hsource, htarget⟩
    refine ⟨reverseLabeledHexEdge edge,
      d4ReducedRightmostTerminal_reverse_mem tiling hedge, ?_, ?_⟩
    · exact congrArg id htarget
    · exact congrArg id hsource
  loopless := by
    rintro vertex ⟨edge, hedge, hsource, htarget⟩
    have halternates := (d4ReducedRightmostTerminal tiling).alternates edge hedge
    apply halternates
    rw [hsource, htarget]

noncomputable def d4TerminalEdgeToDart {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (↥((d4ReducedRightmostTerminal tiling).edges.toFinset)) →
      (d4TerminalSupportGraph tiling).Dart := fun edge =>
  { toProd :=
      (⟨edge.1.source, by
        rw [← d4Terminal_source_eq_boundaryVertices tiling]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨edge.1, List.mem_toFinset.mp edge.2, rfl⟩⟩,
      ⟨edge.1.target, by
        rw [← d4Terminal_source_eq_boundaryVertices tiling]
        have hreverse := d4ReducedRightmostTerminal_reverse_mem tiling
          (List.mem_toFinset.mp edge.2)
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge.1, hreverse, rfl⟩⟩)
    adj := ⟨edge.1, List.mem_toFinset.mp edge.2, rfl, rfl⟩ }

noncomputable def d4TerminalDartToEdge {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TerminalSupportGraph tiling).Dart →
      ↥((d4ReducedRightmostTerminal tiling).edges.toFinset) := fun dart =>
  ⟨Classical.choose dart.adj,
    List.mem_toFinset.mpr (Classical.choose_spec dart.adj).1⟩

theorem d4TerminalEdgeToDart_leftInverse {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Function.LeftInverse (d4TerminalDartToEdge tiling)
      (d4TerminalEdgeToDart tiling) := by
  intro edge
  apply Subtype.ext
  apply d4Terminal_edge_endpoint_injective tiling
  · exact (Classical.choose_spec (d4TerminalEdgeToDart tiling edge).adj).1
  · exact List.mem_toFinset.mp edge.2
  · exact (Classical.choose_spec (d4TerminalEdgeToDart tiling edge).adj).2.1
  · exact (Classical.choose_spec (d4TerminalEdgeToDart tiling edge).adj).2.2

theorem d4TerminalEdgeToDart_rightInverse {m : ℕ}
    (tiling : D4LiteralTiling m) :
    Function.RightInverse (d4TerminalDartToEdge tiling)
      (d4TerminalEdgeToDart tiling) := by
  intro dart
  apply SimpleGraph.Dart.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (Classical.choose_spec dart.adj).2.1
  · exact (Classical.choose_spec dart.adj).2.2

noncomputable def d4TerminalEdgeDartEquiv {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (↥((d4ReducedRightmostTerminal tiling).edges.toFinset)) ≃
      (d4TerminalSupportGraph tiling).Dart where
  toFun := d4TerminalEdgeToDart tiling
  invFun := d4TerminalDartToEdge tiling
  left_inv := d4TerminalEdgeToDart_leftInverse tiling
  right_inv := d4TerminalEdgeToDart_rightInverse tiling

noncomputable instance d4TerminalSupportGraphAdjDecidable {m : ℕ}
    (tiling : D4LiteralTiling m) :
    DecidableRel (d4TerminalSupportGraph tiling).Adj := Classical.decRel _

theorem d4TerminalSupportGraph_twice_edges {m : ℕ}
    (tiling : D4LiteralTiling m) :
    2 * (d4TerminalSupportGraph tiling).edgeFinset.card =
      (d4ReducedRightmostTerminal tiling).edges.length := by
  calc
    _ = Fintype.card (d4TerminalSupportGraph tiling).Dart :=
      ((d4TerminalSupportGraph tiling).dart_card_eq_twice_card_edges).symm
    _ = Fintype.card
        (↥((d4ReducedRightmostTerminal tiling).edges.toFinset)) :=
      (Fintype.card_congr (d4TerminalEdgeDartEquiv tiling)).symm
    _ = (d4ReducedRightmostTerminal tiling).edges.toFinset.card :=
      Fintype.card_coe _
    _ = _ := List.toFinset_card_of_nodup
      (d4ReducedRightmostTerminal_nodup tiling)

theorem d4TerminalSupportGraph_edge_card_add_one {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TerminalSupportGraph tiling).edgeFinset.card + 1 =
      Fintype.card (↥(d4TilingBoundaryVertexFinset tiling)) := by
  have hedge := d4TerminalSupportGraph_twice_edges tiling
  have hcount := d4Terminal_length_add_two_eq_twice_boundary_vertices tiling
  rw [Fintype.card_coe]
  omega

theorem d4ReducedRightmostTerminal_nonempty {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedRightmostTerminal tiling).edges ≠ [] := by
  intro hempty
  have hsource := d4Terminal_source_eq_boundaryVertices tiling
  have houterNonempty : d4ReducedBoundaryWalk m ≠ [] := by
    intro hzero
    have hlen := d4ReducedBoundary_length m
    rw [hzero] at hlen
    simp at hlen
  obtain ⟨edge, hedge⟩ := List.exists_mem_of_ne_nil _ houterNonempty
  have hsourceOuter : edge.source ∈ d4TilingBoundaryVertexFinset tiling :=
    d4Outer_source_subset_boundaryVertices tiling (by
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨edge, hedge, rfl⟩)
  rw [← hsource] at hsourceOuter
  simp [edgeSourceFinset, hempty] at hsourceOuter

theorem d4Terminal_root_mem_boundaryVertices {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4ReducedRightmostTerminal tiling).root ∈
      d4TilingBoundaryVertexFinset tiling := by
  rw [← d4Terminal_source_eq_boundaryVertices]
  exact (d4ReducedRightmostTerminal tiling).continuous
    |>.start_mem_source_of_ne_nil (d4ReducedRightmostTerminal_nonempty tiling)

theorem d4TerminalWalkOfContinuous_nonempty {m : ℕ}
    (tiling : D4LiteralTiling m)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (d4ReducedRightmostTerminal tiling).edges)
    (hstart : start ∈ d4TilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ d4TilingBoundaryVertexFinset tiling) :
    Nonempty ((d4TerminalSupportGraph tiling).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈ (d4ReducedRightmostTerminal tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ d4TilingBoundaryVertexFinset tiling := by
        rw [← d4Terminal_source_eq_boundaryVertices]
        have hreverse := d4ReducedRightmostTerminal_reverse_mem tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hreverse, rfl⟩
      obtain ⟨tailWalk⟩ := ih
        (fun item hitem => hsubset (by simp [hitem])) htarget hfinish
      exact ⟨SimpleGraph.Walk.cons ⟨edge, hedge, rfl, rfl⟩ tailWalk⟩

theorem d4TerminalSupportGraph_connected {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TerminalSupportGraph tiling).Connected := by
  let root : ↥(d4TilingBoundaryVertexFinset tiling) :=
    ⟨(d4ReducedRightmostTerminal tiling).root,
      d4Terminal_root_mem_boundaryVertices tiling⟩
  letI : Nonempty (↥(d4TilingBoundaryVertexFinset tiling)) := ⟨root⟩
  refine ⟨?_⟩
  intro left right
  have hleftSource : left.1 ∈
      edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges := by
    rw [d4Terminal_source_eq_boundaryVertices]
    exact left.2
  have hrightSource : right.1 ∈
      edgeSourceFinset (d4ReducedRightmostTerminal tiling).edges := by
    rw [d4Terminal_source_eq_boundaryVertices]
    exact right.2
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map] at hleftSource hrightSource
  obtain ⟨leftEdge, hleftEdge, hleftSource⟩ := hleftSource
  obtain ⟨rightEdge, hrightEdge, hrightSource⟩ := hrightSource
  obtain ⟨leftPrefix, leftSuffix, hleftSplit⟩ :=
    List.mem_iff_append.mp hleftEdge
  obtain ⟨rightPrefix, rightSuffix, hrightSplit⟩ :=
    List.mem_iff_append.mp hrightEdge
  have leftFull := (d4ReducedRightmostTerminal tiling).continuous
  rw [hleftSplit] at leftFull
  have leftPath := leftFull.prefix_before_edge
  have rightFull := (d4ReducedRightmostTerminal tiling).continuous
  rw [hrightSplit] at rightFull
  have rightPath := rightFull.prefix_before_edge
  have hleftPrefix : leftPrefix ⊆
      (d4ReducedRightmostTerminal tiling).edges := by
    intro edge hedge
    rw [hleftSplit]
    simp [hedge]
  have hrightPrefix : rightPrefix ⊆
      (d4ReducedRightmostTerminal tiling).edges := by
    intro edge hedge
    rw [hrightSplit]
    simp [hedge]
  have hleftVertex : leftEdge.source ∈
      d4TilingBoundaryVertexFinset tiling := by rw [hleftSource]; exact left.2
  have hrightVertex : rightEdge.source ∈
      d4TilingBoundaryVertexFinset tiling := by rw [hrightSource]; exact right.2
  obtain ⟨leftWalk⟩ := d4TerminalWalkOfContinuous_nonempty tiling
    leftPath hleftPrefix (d4Terminal_root_mem_boundaryVertices tiling)
      hleftVertex
  obtain ⟨rightWalk⟩ := d4TerminalWalkOfContinuous_nonempty tiling
    rightPath hrightPrefix (d4Terminal_root_mem_boundaryVertices tiling)
      hrightVertex
  have hleftSubtype :
      (⟨leftEdge.source, hleftVertex⟩ :
        ↥(d4TilingBoundaryVertexFinset tiling)) = left :=
    Subtype.ext hleftSource
  have hrightSubtype :
      (⟨rightEdge.source, hrightVertex⟩ :
        ↥(d4TilingBoundaryVertexFinset tiling)) = right :=
    Subtype.ext hrightSource
  let leftWalk' := leftWalk.copy rfl hleftSubtype
  let rightWalk' := rightWalk.copy rfl hrightSubtype
  exact (leftWalk'.reverse.append rightWalk').reachable

theorem d4TerminalSupportGraph_isTree {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (d4TerminalSupportGraph tiling).IsTree :=
  isTree_of_connected_card_edge_add_one
    (d4TerminalSupportGraph tiling)
    (d4TerminalSupportGraph_connected tiling)
    (d4TerminalSupportGraph_edge_card_add_one tiling)

end FiniteDefects

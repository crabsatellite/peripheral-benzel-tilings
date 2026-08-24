import BenzelProblem6Kernel.HexEdgeEndpointInjectivity
import BenzelProblem6Kernel.ConnectedGraphTreeCard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The finite graph supported by the terminal contour -/

namespace BenzelProblem6Kernel

theorem tilingComplex_edge_has_cellSide {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ literalTilingComplexDirectedEdges tiling) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  rw [literalTilingComplexDirectedEdges, List.mem_append] at hedge
  rcases hedge with hedgeOuter | hedgeTiles
  · obtain ⟨datum, hdatum, hedgeEq⟩ :=
      mem_literalReducedPeripheralBoundary_exists_datum hedgeOuter
    exact ⟨datum.1, datum.2, hedgeEq⟩
  · rw [reverseLiteralPlacementBoundaryList,
      List.mem_flatMap] at hedgeTiles
    obtain ⟨placement, hplacement, hedgePlacement⟩ := hedgeTiles
    have horiginal : reverseLabeledHexEdge edge ∈
        literalPlacementBoundary placement :=
      (mem_reverseReorientedEdges_iff edge _).mp hedgePlacement
    obtain ⟨owner, howner, hownerEdge⟩ :=
      literalPlacementBoundary_edge_has_cell placement horiginal
    obtain ⟨side, hside⟩ :=
      labeledCellBoundary_edge_has_side hownerEdge
    refine ⟨neighboringCell owner side, oppositeHexSide side, ?_⟩
    rw [cellBoundaryEdgeAt_neighbor_exact, hside,
      reverseLabeledHexEdge_involutive]

theorem terminal_edge_has_cellSide {m : ℕ}
    (tiling : LiteralTiling m) {edge : LabeledHexEdge}
    (hedge : edge ∈ (literalTilingRightmostTerminal tiling).edges) :
    ∃ (cell : Cell) (side : HexSide),
      cellBoundaryEdgeAt cell side = edge := by
  have haccount := literalTilingTerminal_edgeAccounting_perm tiling
  have hedgeComplex : edge ∈ literalTilingComplexDirectedEdges tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  exact tilingComplex_edge_has_cellSide tiling hedgeComplex

theorem terminal_edge_endpoint_injective {m : ℕ}
    (tiling : LiteralTiling m)
    {left right : LabeledHexEdge}
    (hleft : left ∈ (literalTilingRightmostTerminal tiling).edges)
    (hright : right ∈ (literalTilingRightmostTerminal tiling).edges)
    (hsource : left.source = right.source)
    (htarget : left.target = right.target) : left = right := by
  obtain ⟨leftCell, leftSide, hleftEq⟩ :=
    terminal_edge_has_cellSide tiling hleft
  obtain ⟨rightCell, rightSide, hrightEq⟩ :=
    terminal_edge_has_cellSide tiling hright
  rw [← hleftEq, ← hrightEq] at hsource htarget ⊢
  exact cellBoundaryEdgeAt_endpoint_injective
    leftCell rightCell leftSide rightSide hsource htarget

noncomputable def terminalSupportGraph {m : ℕ}
    (tiling : LiteralTiling m) :
    SimpleGraph (↥(tilingBoundaryVertexFinset tiling)) where
  Adj left right := ∃ edge ∈
      (literalTilingRightmostTerminal tiling).edges,
    edge.source = left.1 ∧ edge.target = right.1
  symm := by
    rintro left right ⟨edge, hedge, hsource, htarget⟩
    refine ⟨reverseLabeledHexEdge edge,
      literalTilingRightmostTerminal_reverse_mem tiling hedge,
      ?_, ?_⟩
    · exact congrArg id htarget
    · exact congrArg id hsource
  loopless := by
    rintro vertex ⟨edge, hedge, hsource, htarget⟩
    have halternates :=
      (literalTilingRightmostTerminal tiling).alternates edge hedge
    apply halternates
    rw [hsource, htarget]

noncomputable def terminalEdgeToDart {m : ℕ}
    (tiling : LiteralTiling m) :
    (↥((literalTilingRightmostTerminal tiling).edges.toFinset)) →
      (terminalSupportGraph tiling).Dart := fun edge =>
  { toProd :=
      (⟨edge.1.source, by
        rw [← terminal_source_eq_boundaryVertices tiling]
        simp only [edgeSourceFinset, List.mem_toFinset,
          List.mem_map]
        exact ⟨edge.1, List.mem_toFinset.mp edge.2, rfl⟩⟩,
      ⟨edge.1.target, by
        rw [← terminal_source_eq_boundaryVertices tiling]
        have hreverse := literalTilingRightmostTerminal_reverse_mem
          tiling (List.mem_toFinset.mp edge.2)
        simp only [edgeSourceFinset, List.mem_toFinset,
          List.mem_map]
        exact ⟨reverseLabeledHexEdge edge.1, hreverse, rfl⟩⟩)
    adj := ⟨edge.1, List.mem_toFinset.mp edge.2, rfl, rfl⟩ }

noncomputable def terminalDartToEdge {m : ℕ}
    (tiling : LiteralTiling m) :
    (terminalSupportGraph tiling).Dart →
      ↥((literalTilingRightmostTerminal tiling).edges.toFinset) := fun dart =>
  ⟨Classical.choose dart.adj,
    List.mem_toFinset.mpr (Classical.choose_spec dart.adj).1⟩

theorem terminalEdgeToDart_leftInverse {m : ℕ}
    (tiling : LiteralTiling m) :
    Function.LeftInverse (terminalDartToEdge tiling)
      (terminalEdgeToDart tiling) := by
  intro edge
  apply Subtype.ext
  apply terminal_edge_endpoint_injective tiling
  · exact (Classical.choose_spec
      (terminalEdgeToDart tiling edge).adj).1
  · exact List.mem_toFinset.mp edge.2
  · exact (Classical.choose_spec
      (terminalEdgeToDart tiling edge).adj).2.1
  · exact (Classical.choose_spec
      (terminalEdgeToDart tiling edge).adj).2.2

theorem terminalEdgeToDart_rightInverse {m : ℕ}
    (tiling : LiteralTiling m) :
    Function.RightInverse (terminalDartToEdge tiling)
      (terminalEdgeToDart tiling) := by
  intro dart
  apply SimpleGraph.Dart.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (Classical.choose_spec dart.adj).2.1
  · exact (Classical.choose_spec dart.adj).2.2

noncomputable def terminalEdgeDartEquiv {m : ℕ}
    (tiling : LiteralTiling m) :
    (↥((literalTilingRightmostTerminal tiling).edges.toFinset)) ≃
      (terminalSupportGraph tiling).Dart where
  toFun := terminalEdgeToDart tiling
  invFun := terminalDartToEdge tiling
  left_inv := terminalEdgeToDart_leftInverse tiling
  right_inv := terminalEdgeToDart_rightInverse tiling

noncomputable instance terminalSupportGraphAdjDecidable {m : ℕ}
    (tiling : LiteralTiling m) :
    DecidableRel (terminalSupportGraph tiling).Adj :=
  Classical.decRel _

theorem terminalSupportGraph_twice_edges {m : ℕ}
    (tiling : LiteralTiling m) :
    2 * (terminalSupportGraph tiling).edgeFinset.card =
      (literalTilingRightmostTerminal tiling).edges.length := by
  calc
    2 * (terminalSupportGraph tiling).edgeFinset.card =
        Fintype.card (terminalSupportGraph tiling).Dart :=
      ((terminalSupportGraph tiling).dart_card_eq_twice_card_edges).symm
    _ = Fintype.card
        (↥((literalTilingRightmostTerminal tiling).edges.toFinset)) :=
      (Fintype.card_congr (terminalEdgeDartEquiv tiling)).symm
    _ = (literalTilingRightmostTerminal tiling).edges.toFinset.card :=
      Fintype.card_coe _
    _ = (literalTilingRightmostTerminal tiling).edges.length :=
      List.toFinset_card_of_nodup
        (literalTilingRightmostTerminal_nodup tiling)

theorem terminalSupportGraph_edge_card_add_one {m : ℕ}
    (tiling : LiteralTiling m) :
    (terminalSupportGraph tiling).edgeFinset.card + 1 =
      Fintype.card (↥(tilingBoundaryVertexFinset tiling)) := by
  have hedge := terminalSupportGraph_twice_edges tiling
  have hcount := terminal_length_add_two_eq_twice_boundary_vertices tiling
  rw [Fintype.card_coe]
  omega

theorem literalTilingRightmostTerminal_nonempty {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingRightmostTerminal tiling).edges ≠ [] := by
  intro hempty
  have hlength := literalTilingRightmostTerminal_length tiling
  rw [hempty] at hlength
  simp at hlength
  omega

theorem terminal_root_mem_boundaryVertices {m : ℕ}
    (tiling : LiteralTiling m) :
    (literalTilingRightmostTerminal tiling).root ∈
      tilingBoundaryVertexFinset tiling := by
  rw [← terminal_source_eq_boundaryVertices]
  exact (literalTilingRightmostTerminal tiling).continuous
    |>.start_mem_source_of_ne_nil
      (literalTilingRightmostTerminal_nonempty tiling)

theorem terminalWalkOfContinuous_nonempty {m : ℕ}
    (tiling : LiteralTiling m)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (literalTilingRightmostTerminal tiling).edges)
    (hstart : start ∈ tilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ tilingBoundaryVertexFinset tiling) :
    Nonempty ((terminalSupportGraph tiling).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈
          (literalTilingRightmostTerminal tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ tilingBoundaryVertexFinset tiling := by
        rw [← terminal_source_eq_boundaryVertices]
        have hreverse := literalTilingRightmostTerminal_reverse_mem
          tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset,
          List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hreverse, rfl⟩
      have htail := ih
        (fun item hitem => hsubset (by simp [hitem]))
        htarget hfinish
      obtain ⟨tailWalk⟩ := htail
      exact ⟨SimpleGraph.Walk.cons
        ⟨edge, hedge, rfl, rfl⟩ tailWalk⟩

theorem terminalSupportGraph_connected {m : ℕ}
    (tiling : LiteralTiling m) :
    (terminalSupportGraph tiling).Connected := by
  let root : ↥(tilingBoundaryVertexFinset tiling) :=
    ⟨(literalTilingRightmostTerminal tiling).root,
      terminal_root_mem_boundaryVertices tiling⟩
  letI : Nonempty (↥(tilingBoundaryVertexFinset tiling)) := ⟨root⟩
  refine ⟨?_⟩
  intro left right
  have hleftSource : left.1 ∈ edgeSourceFinset
      (literalTilingRightmostTerminal tiling).edges := by
    rw [terminal_source_eq_boundaryVertices]
    exact left.2
  have hrightSource : right.1 ∈ edgeSourceFinset
      (literalTilingRightmostTerminal tiling).edges := by
    rw [terminal_source_eq_boundaryVertices]
    exact right.2
  simp only [edgeSourceFinset, List.mem_toFinset,
    List.mem_map] at hleftSource hrightSource
  obtain ⟨leftEdge, hleftEdge, hleftSource⟩ := hleftSource
  obtain ⟨rightEdge, hrightEdge, hrightSource⟩ := hrightSource
  obtain ⟨leftPrefix, leftSuffix, hleftSplit⟩ :=
    List.mem_iff_append.mp hleftEdge
  obtain ⟨rightPrefix, rightSuffix, hrightSplit⟩ :=
    List.mem_iff_append.mp hrightEdge
  have leftFull := (literalTilingRightmostTerminal tiling).continuous
  rw [hleftSplit] at leftFull
  have leftPath := leftFull.prefix_before_edge
    (segment := leftPrefix) (suffix := leftSuffix) (edge := leftEdge)
  have rightFull := (literalTilingRightmostTerminal tiling).continuous
  rw [hrightSplit] at rightFull
  have rightPath := rightFull.prefix_before_edge
    (segment := rightPrefix) (suffix := rightSuffix) (edge := rightEdge)
  have hleftPrefix : leftPrefix ⊆
      (literalTilingRightmostTerminal tiling).edges := by
    intro edge hedge
    rw [hleftSplit]
    simp [hedge]
  have hrightPrefix : rightPrefix ⊆
      (literalTilingRightmostTerminal tiling).edges := by
    intro edge hedge
    rw [hrightSplit]
    simp [hedge]
  have hleftVertex : leftEdge.source ∈
      tilingBoundaryVertexFinset tiling := by
    rw [hleftSource]
    exact left.2
  have hrightVertex : rightEdge.source ∈
      tilingBoundaryVertexFinset tiling := by
    rw [hrightSource]
    exact right.2
  obtain ⟨leftWalk⟩ := terminalWalkOfContinuous_nonempty tiling
    leftPath hleftPrefix (terminal_root_mem_boundaryVertices tiling)
      hleftVertex
  obtain ⟨rightWalk⟩ := terminalWalkOfContinuous_nonempty tiling
    rightPath hrightPrefix (terminal_root_mem_boundaryVertices tiling)
      hrightVertex
  have hleftSubtype :
      (⟨leftEdge.source, hleftVertex⟩ :
        ↥(tilingBoundaryVertexFinset tiling)) = left :=
    Subtype.ext hleftSource
  have hrightSubtype :
      (⟨rightEdge.source, hrightVertex⟩ :
        ↥(tilingBoundaryVertexFinset tiling)) = right :=
    Subtype.ext hrightSource
  let leftWalk' := leftWalk.copy rfl hleftSubtype
  let rightWalk' := rightWalk.copy rfl hrightSubtype
  exact (leftWalk'.reverse.append rightWalk').reachable

theorem terminalSupportGraph_isTree {m : ℕ}
    (tiling : LiteralTiling m) :
    (terminalSupportGraph tiling).IsTree :=
  isTree_of_connected_card_edge_add_one
    (terminalSupportGraph tiling)
    (terminalSupportGraph_connected tiling)
    (terminalSupportGraph_edge_card_add_one tiling)

end BenzelProblem6Kernel

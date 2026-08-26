import D4KernelOnly.GeneralClassMinusOneSelectedEndpointSupport
import BenzelProblem6Kernel.HexEdgeEndpointInjectivity
import BenzelProblem6Kernel.ConnectedGraphTreeCard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The finite tree supported by a class-minus-one terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem cmoTilingComplex_edge_has_cellSide
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {edge : LabeledHexEdge} (hedge : edge ∈ cmoTilingComplexDirectedEdges hs tiling) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  rw [cmoTilingComplexDirectedEdges, List.mem_append] at hedge
  rcases hedge with hedgeOuter | hedgeTiles
  · exact cmoReducedBoundaryEdge_has_cellSide hedgeOuter
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

theorem cmoTerminal_edge_has_cellSide
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {edge : LabeledHexEdge}
    (hedge : edge ∈ (cmoReducedRightmostTerminal hs tiling).edges) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  have haccount := cmoTerminal_edgeAccounting_perm hs tiling
  have hedgeComplex : edge ∈ cmoTilingComplexDirectedEdges hs tiling :=
    haccount.mem_iff.mpr (List.mem_append_left _ hedge)
  exact cmoTilingComplex_edge_has_cellSide hs tiling hedgeComplex

theorem cmoTerminal_edge_endpoint_injective
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {left right : LabeledHexEdge}
    (hleft : left ∈ (cmoReducedRightmostTerminal hs tiling).edges)
    (hright : right ∈ (cmoReducedRightmostTerminal hs tiling).edges)
    (hsource : left.source = right.source)
    (htarget : left.target = right.target) : left = right := by
  obtain ⟨leftCell, leftSide, hleftEq⟩ :=
    cmoTerminal_edge_has_cellSide hs tiling hleft
  obtain ⟨rightCell, rightSide, hrightEq⟩ :=
    cmoTerminal_edge_has_cellSide hs tiling hright
  rw [← hleftEq, ← hrightEq] at hsource htarget ⊢
  exact cellBoundaryEdgeAt_endpoint_injective
    leftCell rightCell leftSide rightSide hsource htarget

noncomputable def cmoTerminalSupportGraph
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    SimpleGraph (↥(cmoTilingBoundaryVertexFinset tiling)) where
  Adj left right := ∃ edge ∈ (cmoReducedRightmostTerminal hs tiling).edges,
    edge.source = left.1 ∧ edge.target = right.1
  symm := by
    rintro left right ⟨edge, hedge, hsource, htarget⟩
    refine ⟨reverseLabeledHexEdge edge,
      cmoReducedRightmostTerminal_reverse_mem hs tiling hedge, ?_, ?_⟩
    · exact congrArg id htarget
    · exact congrArg id hsource
  loopless := by
    rintro vertex ⟨edge, hedge, hsource, htarget⟩
    have halternates := (cmoReducedRightmostTerminal hs tiling).alternates edge hedge
    apply halternates
    rw [hsource, htarget]

noncomputable def cmoTerminalEdgeToDart
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (↥((cmoReducedRightmostTerminal hs tiling).edges.toFinset)) →
      (cmoTerminalSupportGraph hs tiling).Dart := fun edge =>
  { toProd :=
      (⟨edge.1.source, by
        rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨edge.1, List.mem_toFinset.mp edge.2, rfl⟩⟩,
      ⟨edge.1.target, by
        rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
        have hreverse := cmoReducedRightmostTerminal_reverse_mem hs tiling
          (List.mem_toFinset.mp edge.2)
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge.1, hreverse, rfl⟩⟩)
    adj := ⟨edge.1, List.mem_toFinset.mp edge.2, rfl, rfl⟩ }

noncomputable def cmoTerminalDartToEdge
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoTerminalSupportGraph hs tiling).Dart →
      ↥((cmoReducedRightmostTerminal hs tiling).edges.toFinset) := fun dart =>
  ⟨Classical.choose dart.adj,
    List.mem_toFinset.mpr (Classical.choose_spec dart.adj).1⟩

theorem cmoTerminalEdgeToDart_leftInverse
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    Function.LeftInverse (cmoTerminalDartToEdge hs tiling)
      (cmoTerminalEdgeToDart hs tiling) := by
  intro edge
  apply Subtype.ext
  apply cmoTerminal_edge_endpoint_injective hs tiling
  · exact (Classical.choose_spec (cmoTerminalEdgeToDart hs tiling edge).adj).1
  · exact List.mem_toFinset.mp edge.2
  · exact (Classical.choose_spec (cmoTerminalEdgeToDart hs tiling edge).adj).2.1
  · exact (Classical.choose_spec (cmoTerminalEdgeToDart hs tiling edge).adj).2.2

theorem cmoTerminalEdgeToDart_rightInverse
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    Function.RightInverse (cmoTerminalDartToEdge hs tiling)
      (cmoTerminalEdgeToDart hs tiling) := by
  intro dart
  apply SimpleGraph.Dart.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (Classical.choose_spec dart.adj).2.1
  · exact (Classical.choose_spec dart.adj).2.2

noncomputable def cmoTerminalEdgeDartEquiv
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (↥((cmoReducedRightmostTerminal hs tiling).edges.toFinset)) ≃
      (cmoTerminalSupportGraph hs tiling).Dart where
  toFun := cmoTerminalEdgeToDart hs tiling
  invFun := cmoTerminalDartToEdge hs tiling
  left_inv := cmoTerminalEdgeToDart_leftInverse hs tiling
  right_inv := cmoTerminalEdgeToDart_rightInverse hs tiling

noncomputable instance cmoTerminalSupportGraphAdjDecidable
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    DecidableRel (cmoTerminalSupportGraph hs tiling).Adj := Classical.decRel _

theorem cmoTerminalSupportGraph_twice_edges
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    2 * (cmoTerminalSupportGraph hs tiling).edgeFinset.card =
      (cmoReducedRightmostTerminal hs tiling).edges.length := by
  calc
    _ = Fintype.card (cmoTerminalSupportGraph hs tiling).Dart :=
      ((cmoTerminalSupportGraph hs tiling).dart_card_eq_twice_card_edges).symm
    _ = Fintype.card
        (↥((cmoReducedRightmostTerminal hs tiling).edges.toFinset)) :=
      (Fintype.card_congr (cmoTerminalEdgeDartEquiv hs tiling)).symm
    _ = (cmoReducedRightmostTerminal hs tiling).edges.toFinset.card :=
      Fintype.card_coe _
    _ = _ := List.toFinset_card_of_nodup
      (cmoReducedRightmostTerminal_nodup hs tiling)

theorem cmoTerminalSupportGraph_edge_card_add_one
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoTerminalSupportGraph hs tiling).edgeFinset.card + 1 =
      Fintype.card (↥(cmoTilingBoundaryVertexFinset tiling)) := by
  have hedge := cmoTerminalSupportGraph_twice_edges hs tiling
  have hcount :=
    cmoTerminal_length_add_two_eq_twice_boundary_vertices_kernelOnly hs tiling
  rw [Fintype.card_coe]
  omega

theorem cmoReducedRightmostTerminal_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).edges ≠ [] := by
  intro hempty
  have hsource := cmoTerminal_source_eq_boundaryVertices hs tiling
  have houterNonempty : cmoReducedBoundaryWalk s r ≠ [] := by
    intro hzero
    have hlen := cmoReducedBoundary_length s r hs
    rw [hzero] at hlen
    simp at hlen
    omega
  obtain ⟨edge, hedge⟩ := List.exists_mem_of_ne_nil _ houterNonempty
  have hsourceOuter : edge.source ∈ cmoTilingBoundaryVertexFinset tiling :=
    cmoOuter_source_subset_boundaryVertices hs tiling (by
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨edge, hedge, rfl⟩)
  rw [← hsource] at hsourceOuter
  simp [edgeSourceFinset, hempty] at hsourceOuter

theorem cmoTerminal_root_mem_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoReducedRightmostTerminal hs tiling).root ∈
      cmoTilingBoundaryVertexFinset tiling := by
  rw [← cmoTerminal_source_eq_boundaryVertices]
  exact (cmoReducedRightmostTerminal hs tiling).continuous
    |>.start_mem_source_of_ne_nil (cmoReducedRightmostTerminal_nonempty hs tiling)

theorem cmoTerminalWalkOfContinuous_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (cmoReducedRightmostTerminal hs tiling).edges)
    (hstart : start ∈ cmoTilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ cmoTilingBoundaryVertexFinset tiling) :
    Nonempty ((cmoTerminalSupportGraph hs tiling).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
      have hedge : edge ∈ (cmoReducedRightmostTerminal hs tiling).edges :=
        hsubset (by simp)
      have htarget : edge.target ∈ cmoTilingBoundaryVertexFinset tiling := by
        rw [← cmoTerminal_source_eq_boundaryVertices hs tiling]
        have hreverse := cmoReducedRightmostTerminal_reverse_mem hs tiling hedge
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge, hreverse, rfl⟩
      obtain ⟨tailWalk⟩ := ih
        (fun item hitem => hsubset (by simp [hitem])) htarget hfinish
      exact ⟨SimpleGraph.Walk.cons ⟨edge, hedge, rfl, rfl⟩ tailWalk⟩

theorem cmoTerminalSupportGraph_connected
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoTerminalSupportGraph hs tiling).Connected := by
  let root : ↥(cmoTilingBoundaryVertexFinset tiling) :=
    ⟨(cmoReducedRightmostTerminal hs tiling).root,
      cmoTerminal_root_mem_boundaryVertices hs tiling⟩
  letI : Nonempty (↥(cmoTilingBoundaryVertexFinset tiling)) := ⟨root⟩
  refine ⟨?_⟩
  intro left right
  have hleftSource : left.1 ∈
      edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges := by
    rw [cmoTerminal_source_eq_boundaryVertices]
    exact left.2
  have hrightSource : right.1 ∈
      edgeSourceFinset (cmoReducedRightmostTerminal hs tiling).edges := by
    rw [cmoTerminal_source_eq_boundaryVertices]
    exact right.2
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
    at hleftSource hrightSource
  obtain ⟨leftEdge, hleftEdge, hleftSource⟩ := hleftSource
  obtain ⟨rightEdge, hrightEdge, hrightSource⟩ := hrightSource
  obtain ⟨leftPrefix, leftSuffix, hleftSplit⟩ :=
    List.mem_iff_append.mp hleftEdge
  obtain ⟨rightPrefix, rightSuffix, hrightSplit⟩ :=
    List.mem_iff_append.mp hrightEdge
  have leftFull := (cmoReducedRightmostTerminal hs tiling).continuous
  rw [hleftSplit] at leftFull
  have leftPath := leftFull.prefix_before_edge
  have rightFull := (cmoReducedRightmostTerminal hs tiling).continuous
  rw [hrightSplit] at rightFull
  have rightPath := rightFull.prefix_before_edge
  have hleftPrefix : leftPrefix ⊆
      (cmoReducedRightmostTerminal hs tiling).edges := by
    intro edge hedge
    rw [hleftSplit]
    simp [hedge]
  have hrightPrefix : rightPrefix ⊆
      (cmoReducedRightmostTerminal hs tiling).edges := by
    intro edge hedge
    rw [hrightSplit]
    simp [hedge]
  have hleftVertex : leftEdge.source ∈ cmoTilingBoundaryVertexFinset tiling := by
    rw [hleftSource]
    exact left.2
  have hrightVertex : rightEdge.source ∈ cmoTilingBoundaryVertexFinset tiling := by
    rw [hrightSource]
    exact right.2
  obtain ⟨leftWalk⟩ := cmoTerminalWalkOfContinuous_nonempty hs tiling
    leftPath hleftPrefix (cmoTerminal_root_mem_boundaryVertices hs tiling)
      hleftVertex
  obtain ⟨rightWalk⟩ := cmoTerminalWalkOfContinuous_nonempty hs tiling
    rightPath hrightPrefix (cmoTerminal_root_mem_boundaryVertices hs tiling)
      hrightVertex
  have hleftSubtype :
      (⟨leftEdge.source, hleftVertex⟩ :
        ↥(cmoTilingBoundaryVertexFinset tiling)) = left :=
    Subtype.ext hleftSource
  have hrightSubtype :
      (⟨rightEdge.source, hrightVertex⟩ :
        ↥(cmoTilingBoundaryVertexFinset tiling)) = right :=
    Subtype.ext hrightSource
  let leftWalk' := leftWalk.copy rfl hleftSubtype
  let rightWalk' := rightWalk.copy rfl hrightSubtype
  exact (leftWalk'.reverse.append rightWalk').reachable

theorem cmoTerminalSupportGraph_isTree
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    (cmoTerminalSupportGraph hs tiling).IsTree :=
  isTree_of_connected_card_edge_add_one
    (cmoTerminalSupportGraph hs tiling)
    (cmoTerminalSupportGraph_connected hs tiling)
    (cmoTerminalSupportGraph_edge_card_add_one hs tiling)

end FiniteDefects

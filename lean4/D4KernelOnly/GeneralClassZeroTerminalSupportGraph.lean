import D4KernelOnly.GeneralClassZeroSelectedEndpointSupport
import BenzelProblem6Kernel.HexEdgeEndpointInjectivity
import BenzelProblem6Kernel.ConnectedGraphTreeCard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The finite tree supported by a class-zero terminal contour -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czTilingComplex_edge_has_cellSide
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {edge : LabeledHexEdge}
    (hedge : edge ∈ czTilingComplexDirectedEdges hs hr tiling) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  rw [czTilingComplexDirectedEdges, List.mem_append] at hedge
  rcases hedge with ho | ht
  · exact czReducedBoundaryEdge_has_cellSide hs hr ho
  · rw [reverseLiteralPlacementBoundaryList, List.mem_flatMap] at ht
    obtain ⟨placement, hp, hedgePlacement⟩ := ht
    have horiginal : reverseLabeledHexEdge edge ∈ literalPlacementBoundary placement :=
      (mem_reverseReorientedEdges_iff edge _).mp hedgePlacement
    obtain ⟨owner, howner, hownerEdge⟩ :=
      literalPlacementBoundary_edge_has_cell placement horiginal
    obtain ⟨side, hside⟩ := labeledCellBoundary_edge_has_side hownerEdge
    refine ⟨neighboringCell owner side, oppositeHexSide side, ?_⟩
    rw [cellBoundaryEdgeAt_neighbor_exact, hside,
      reverseLabeledHexEdge_involutive]

theorem czTerminal_edge_has_cellSide
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {edge : LabeledHexEdge}
    (hedge : edge ∈ (czReducedRightmostTerminal hs hr tiling).edges) :
    ∃ (cell : Cell) (side : HexSide), cellBoundaryEdgeAt cell side = edge := by
  have haccount := czTerminal_edgeAccounting_perm hs hr tiling
  exact czTilingComplex_edge_has_cellSide hs hr tiling
    (haccount.mem_iff.mpr (List.mem_append_left _ hedge))

theorem czTerminal_edge_endpoint_injective
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) {left right : LabeledHexEdge}
    (hl : left ∈ (czReducedRightmostTerminal hs hr tiling).edges)
    (hright : right ∈ (czReducedRightmostTerminal hs hr tiling).edges)
    (hsource : left.source = right.source)
    (htarget : left.target = right.target) : left = right := by
  obtain ⟨lc, ls, hleq⟩ := czTerminal_edge_has_cellSide hs hr tiling hl
  obtain ⟨rc, rs, hreq⟩ := czTerminal_edge_has_cellSide hs hr tiling hright
  rw [← hleq, ← hreq] at hsource htarget ⊢
  exact cellBoundaryEdgeAt_endpoint_injective lc rc ls rs hsource htarget

noncomputable def czTerminalSupportGraph
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    SimpleGraph (↥(offsetTilingBoundaryVertexFinset tiling)) where
  Adj left right := ∃ edge ∈ (czReducedRightmostTerminal hs hr tiling).edges,
    edge.source = left.1 ∧ edge.target = right.1
  symm := by
    rintro left right ⟨edge, hedge, hsource, htarget⟩
    exact ⟨reverseLabeledHexEdge edge,
      czReducedRightmostTerminal_reverse_mem hs hr tiling hedge,
      congrArg id htarget, congrArg id hsource⟩
  loopless := by
    rintro vertex ⟨edge, hedge, hsource, htarget⟩
    have halt := (czReducedRightmostTerminal hs hr tiling).alternates edge hedge
    apply halt
    rw [hsource, htarget]

noncomputable def czTerminalEdgeToDart
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    ↥((czReducedRightmostTerminal hs hr tiling).edges.toFinset) →
      (czTerminalSupportGraph hs hr tiling).Dart := fun edge =>
  { toProd :=
      (⟨edge.1.source, by
        rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨edge.1, List.mem_toFinset.mp edge.2, rfl⟩⟩,
      ⟨edge.1.target, by
        rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
        have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling
          (List.mem_toFinset.mp edge.2)
        simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
        exact ⟨reverseLabeledHexEdge edge.1, hrev, rfl⟩⟩)
    adj := ⟨edge.1, List.mem_toFinset.mp edge.2, rfl, rfl⟩ }

noncomputable def czTerminalDartToEdge
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czTerminalSupportGraph hs hr tiling).Dart →
      ↥((czReducedRightmostTerminal hs hr tiling).edges.toFinset) := fun dart =>
  ⟨Classical.choose dart.adj,
    List.mem_toFinset.mpr (Classical.choose_spec dart.adj).1⟩

theorem czTerminalEdgeToDart_leftInverse
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    Function.LeftInverse (czTerminalDartToEdge hs hr tiling)
      (czTerminalEdgeToDart hs hr tiling) := by
  intro edge
  apply Subtype.ext
  apply czTerminal_edge_endpoint_injective hs hr tiling
  · exact (Classical.choose_spec (czTerminalEdgeToDart hs hr tiling edge).adj).1
  · exact List.mem_toFinset.mp edge.2
  · exact (Classical.choose_spec (czTerminalEdgeToDart hs hr tiling edge).adj).2.1
  · exact (Classical.choose_spec (czTerminalEdgeToDart hs hr tiling edge).adj).2.2

theorem czTerminalEdgeToDart_rightInverse
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    Function.RightInverse (czTerminalDartToEdge hs hr tiling)
      (czTerminalEdgeToDart hs hr tiling) := by
  intro dart
  apply SimpleGraph.Dart.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact (Classical.choose_spec dart.adj).2.1
  · exact (Classical.choose_spec dart.adj).2.2

noncomputable def czTerminalEdgeDartEquiv
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    ↥((czReducedRightmostTerminal hs hr tiling).edges.toFinset) ≃
      (czTerminalSupportGraph hs hr tiling).Dart where
  toFun := czTerminalEdgeToDart hs hr tiling
  invFun := czTerminalDartToEdge hs hr tiling
  left_inv := czTerminalEdgeToDart_leftInverse hs hr tiling
  right_inv := czTerminalEdgeToDart_rightInverse hs hr tiling

noncomputable instance czTerminalSupportGraphAdjDecidable
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    DecidableRel (czTerminalSupportGraph hs hr tiling).Adj := Classical.decRel _

theorem czTerminalSupportGraph_twice_edges
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    2 * (czTerminalSupportGraph hs hr tiling).edgeFinset.card =
      (czReducedRightmostTerminal hs hr tiling).edges.length := by
  calc
    _ = Fintype.card (czTerminalSupportGraph hs hr tiling).Dart :=
      ((czTerminalSupportGraph hs hr tiling).dart_card_eq_twice_card_edges).symm
    _ = Fintype.card
        ↥((czReducedRightmostTerminal hs hr tiling).edges.toFinset) :=
      (Fintype.card_congr (czTerminalEdgeDartEquiv hs hr tiling)).symm
    _ = (czReducedRightmostTerminal hs hr tiling).edges.toFinset.card :=
      Fintype.card_coe _
    _ = _ := List.toFinset_card_of_nodup
      (czReducedRightmostTerminal_nodup hs hr tiling)

theorem czTerminalSupportGraph_edge_card_add_one
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czTerminalSupportGraph hs hr tiling).edgeFinset.card + 1 =
      Fintype.card ↥(offsetTilingBoundaryVertexFinset tiling) := by
  have he := czTerminalSupportGraph_twice_edges hs hr tiling
  have hc := czTerminal_length_add_two_eq_twice_boundary_vertices hs hr tiling
  rw [Fintype.card_coe]
  omega

theorem czReducedRightmostTerminal_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedRightmostTerminal hs hr tiling).edges ≠ [] := by
  intro hempty
  have hsource := czTerminal_source_eq_boundaryVertices hs hr tiling
  have houter : czReducedBoundaryWalk s r ≠ [] := by
    intro hzero
    have hlen := czReducedBoundary_length s r hs hr
    rw [hzero] at hlen
    simp at hlen
    omega
  obtain ⟨edge, hedge⟩ := List.exists_mem_of_ne_nil _ houter
  have hsOuter : edge.source ∈ offsetTilingBoundaryVertexFinset tiling :=
    czOuter_source_subset_boundaryVertices hs hr tiling (by
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨edge, hedge, rfl⟩)
  rw [← hsource] at hsOuter
  simp [edgeSourceFinset, hempty] at hsOuter

theorem czTerminal_root_mem_boundaryVertices
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czReducedRightmostTerminal hs hr tiling).root ∈
      offsetTilingBoundaryVertexFinset tiling := by
  rw [← czTerminal_source_eq_boundaryVertices]
  exact (czReducedRightmostTerminal hs hr tiling).continuous
    |>.start_mem_source_of_ne_nil
      (czReducedRightmostTerminal_nonempty hs hr tiling)

theorem czTerminalWalkOfContinuous_nonempty
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r)
    {start finish : HexVertex} {edges : List LabeledHexEdge}
    (path : ContinuousLabeledEdgePath start edges finish)
    (hsubset : edges ⊆ (czReducedRightmostTerminal hs hr tiling).edges)
    (hstart : start ∈ offsetTilingBoundaryVertexFinset tiling)
    (hfinish : finish ∈ offsetTilingBoundaryVertexFinset tiling) :
    Nonempty ((czTerminalSupportGraph hs hr tiling).Walk
      ⟨start, hstart⟩ ⟨finish, hfinish⟩) := by
  induction path with
  | nil => exact ⟨.nil⟩
  | @cons edge rest target tail ih =>
    have hedge : edge ∈ (czReducedRightmostTerminal hs hr tiling).edges :=
      hsubset (by simp)
    have htarget : edge.target ∈ offsetTilingBoundaryVertexFinset tiling := by
      rw [← czTerminal_source_eq_boundaryVertices hs hr tiling]
      have hrev := czReducedRightmostTerminal_reverse_mem hs hr tiling hedge
      simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
      exact ⟨reverseLabeledHexEdge edge, hrev, rfl⟩
    obtain ⟨tailWalk⟩ := ih
      (fun item hitem => hsubset (by simp [hitem])) htarget hfinish
    exact ⟨SimpleGraph.Walk.cons ⟨edge, hedge, rfl, rfl⟩ tailWalk⟩

theorem czTerminalSupportGraph_connected
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czTerminalSupportGraph hs hr tiling).Connected := by
  let root : ↥(offsetTilingBoundaryVertexFinset tiling) :=
    ⟨(czReducedRightmostTerminal hs hr tiling).root,
      czTerminal_root_mem_boundaryVertices hs hr tiling⟩
  letI : Nonempty ↥(offsetTilingBoundaryVertexFinset tiling) := ⟨root⟩
  refine ⟨?_⟩
  intro left right
  have hleftSource : left.1 ∈
      edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges := by
    rw [czTerminal_source_eq_boundaryVertices]
    exact left.2
  have hrightSource : right.1 ∈
      edgeSourceFinset (czReducedRightmostTerminal hs hr tiling).edges := by
    rw [czTerminal_source_eq_boundaryVertices]
    exact right.2
  simp only [edgeSourceFinset, List.mem_toFinset, List.mem_map]
    at hleftSource hrightSource
  obtain ⟨leftEdge, hleftEdge, hleftSource⟩ := hleftSource
  obtain ⟨rightEdge, hrightEdge, hrightSource⟩ := hrightSource
  obtain ⟨leftPrefix, leftSuffix, hleftSplit⟩ := List.mem_iff_append.mp hleftEdge
  obtain ⟨rightPrefix, rightSuffix, hrightSplit⟩ := List.mem_iff_append.mp hrightEdge
  have leftFull := (czReducedRightmostTerminal hs hr tiling).continuous
  rw [hleftSplit] at leftFull
  have leftPath := leftFull.prefix_before_edge
  have rightFull := (czReducedRightmostTerminal hs hr tiling).continuous
  rw [hrightSplit] at rightFull
  have rightPath := rightFull.prefix_before_edge
  have hleftPrefix : leftPrefix ⊆
      (czReducedRightmostTerminal hs hr tiling).edges := by
    intro edge hedge; rw [hleftSplit]; simp [hedge]
  have hrightPrefix : rightPrefix ⊆
      (czReducedRightmostTerminal hs hr tiling).edges := by
    intro edge hedge; rw [hrightSplit]; simp [hedge]
  have hleftVertex : leftEdge.source ∈ offsetTilingBoundaryVertexFinset tiling := by
    rw [hleftSource]; exact left.2
  have hrightVertex : rightEdge.source ∈ offsetTilingBoundaryVertexFinset tiling := by
    rw [hrightSource]; exact right.2
  obtain ⟨leftWalk⟩ := czTerminalWalkOfContinuous_nonempty hs hr tiling
    leftPath hleftPrefix (czTerminal_root_mem_boundaryVertices hs hr tiling)
      hleftVertex
  obtain ⟨rightWalk⟩ := czTerminalWalkOfContinuous_nonempty hs hr tiling
    rightPath hrightPrefix (czTerminal_root_mem_boundaryVertices hs hr tiling)
      hrightVertex
  have hleftSubtype :
      (⟨leftEdge.source, hleftVertex⟩ : ↥(offsetTilingBoundaryVertexFinset tiling)) = left :=
    Subtype.ext hleftSource
  have hrightSubtype :
      (⟨rightEdge.source, hrightVertex⟩ : ↥(offsetTilingBoundaryVertexFinset tiling)) = right :=
    Subtype.ext hrightSource
  let leftWalk' := leftWalk.copy rfl hleftSubtype
  let rightWalk' := rightWalk.copy rfl hrightSubtype
  exact (leftWalk'.reverse.append rightWalk').reachable

theorem czTerminalSupportGraph_isTree
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    (czTerminalSupportGraph hs hr tiling).IsTree :=
  isTree_of_connected_card_edge_add_one
    (czTerminalSupportGraph hs hr tiling)
    (czTerminalSupportGraph_connected hs hr tiling)
    (czTerminalSupportGraph_edge_card_add_one hs hr tiling)

end FiniteDefects

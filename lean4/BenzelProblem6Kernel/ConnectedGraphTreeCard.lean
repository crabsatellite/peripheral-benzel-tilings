import BenzelProblem6Kernel.ConnectedGraphDeleteEdge

/-! # The finite connected edge-cardinality characterization of trees -/

namespace BenzelProblem6Kernel

open SimpleGraph

theorem isTree_of_connected_card_edge_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconnected : G.Connected)
    (hcard : G.edgeFinset.card + 1 = Fintype.card V) :
    G.IsTree := by
  refine ⟨hconnected, ?_⟩
  intro cycleRoot cycle hcycle
  let firstDart := cycle.firstDart hcycle.not_nil
  have hedgeMem : firstDart.edge ∈ cycle.edges := by
    cases cycle with
    | nil => exact (hcycle.not_nil .nil).elim
    | cons hedge tail =>
        change s(cycleRoot, _) ∈ (SimpleGraph.Walk.cons hedge tail).edges
        simp
  have hcycleWitness :
      ∃ (root : V) (walk : G.Walk root root),
        walk.IsCycle ∧ s(firstDart.fst, firstDart.snd) ∈ walk.edges :=
    ⟨cycleRoot, cycle, hcycle, by simpa [firstDart] using hedgeMem⟩
  have hdeleteData :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G) (v := firstDart.fst) (w := firstDart.snd)).mpr
      hcycleWitness
  let removed : Sym2 V := s(firstDart.fst, firstDart.snd)
  let H := G.deleteEdges {removed}
  have hHConnected : H.Connected :=
    deleteEdge_connected_of_endpoint_reachable G hconnected
      hdeleteData.1 hdeleteData.2
  letI : DecidableRel H.Adj := Classical.decRel _
  have hLower := connected_vertex_card_le_edge_card_add_one
    H hHConnected
  have hedgeIn : removed ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hdeleteData.1
  have hsubset : H.edgeFinset ⊆ G.edgeFinset :=
    SimpleGraph.edgeFinset_mono (G.deleteEdges_le {removed})
  have hremovedNot : removed ∉ H.edgeFinset := by
    simp [H, removed, SimpleGraph.deleteEdges]
  have hstrict : H.edgeFinset ⊂ G.edgeFinset := by
    refine ⟨hsubset, ?_⟩
    intro hreverseSubset
    exact hremovedNot (hreverseSubset hedgeIn)
  have hcardLt := Finset.card_lt_card hstrict
  omega

end BenzelProblem6Kernel

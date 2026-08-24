import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The finite graph component bound

For a finite graph, `|V| ≤ |E| + number of connected components`.  We prove
this by choosing one root in every component and mapping every non-root vertex
to the final edge of a shortest path from its component root.
-/

namespace BenzelProblem6Kernel

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable instance graphConnectedComponentFintype :
    Fintype G.ConnectedComponent := by
  classical
  exact Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

noncomputable instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

noncomputable def componentRoot (component : G.ConnectedComponent) : V :=
  component.exists_rep.choose

theorem componentRoot_spec (component : G.ConnectedComponent) :
    G.connectedComponentMk (componentRoot G component) = component :=
  component.exists_rep.choose_spec

def IsComponentRoot (vertex : V) : Prop :=
  componentRoot G (G.connectedComponentMk vertex) = vertex

noncomputable instance isComponentRootDecidable (vertex : V) :
    Decidable (IsComponentRoot G vertex) := Classical.propDecidable _

abbrev NonrootVertex := {vertex : V // ¬IsComponentRoot G vertex}
abbrev RootVertex := {vertex : V // IsComponentRoot G vertex}

noncomputable def rootVertexEquiv : RootVertex G ≃ G.ConnectedComponent where
  toFun vertex := G.connectedComponentMk vertex.1
  invFun component := ⟨componentRoot G component, by
    unfold IsComponentRoot
    rw [componentRoot_spec]
  ⟩
  left_inv := by
    intro vertex
    apply Subtype.ext
    exact vertex.2
  right_inv := componentRoot_spec G

theorem rootVertex_card : Fintype.card (RootVertex G) =
    Fintype.card G.ConnectedComponent := by
  rw [Fintype.card_congr (rootVertexEquiv G)]

theorem root_reachable (vertex : V) :
    G.Reachable (componentRoot G (G.connectedComponentMk vertex)) vertex := by
  rw [← SimpleGraph.ConnectedComponent.eq]
  exact componentRoot_spec G _

noncomputable def rootShortestPath (vertex : V) :
    G.Walk (componentRoot G (G.connectedComponentMk vertex)) vertex :=
  (root_reachable G vertex).exists_path_of_dist.choose

theorem rootShortestPath_isPath (vertex : V) :
    (rootShortestPath G vertex).IsPath :=
  (root_reachable G vertex).exists_path_of_dist.choose_spec.1

theorem rootShortestPath_length (vertex : V) :
    (rootShortestPath G vertex).length =
      G.dist (componentRoot G (G.connectedComponentMk vertex)) vertex :=
  (root_reachable G vertex).exists_path_of_dist.choose_spec.2

theorem rootShortestPath_not_nil (vertex : NonrootVertex G) :
    ¬(rootShortestPath G vertex.1).Nil := by
  rw [SimpleGraph.Walk.nil_iff_length_eq, rootShortestPath_length]
  exact (SimpleGraph.dist_ne_zero_iff_ne_and_reachable.mpr
    ⟨fun heq => vertex.2 heq, root_reachable G vertex.1⟩)

noncomputable def nonrootParent (vertex : NonrootVertex G) : V :=
  (rootShortestPath G vertex.1).penultimate

theorem nonrootParent_adj (vertex : NonrootVertex G) :
    G.Adj (nonrootParent G vertex) vertex.1 :=
  (rootShortestPath G vertex.1).adj_penultimate
    (rootShortestPath_not_nil G vertex)

theorem reverse_snd_eq_penultimate (vertex : NonrootVertex G) :
    (rootShortestPath G vertex.1).reverse.snd = nonrootParent G vertex := by
  simp [SimpleGraph.Walk.snd, nonrootParent,
    SimpleGraph.Walk.getVert_reverse]

noncomputable def rootToParentWalk (vertex : NonrootVertex G) :
    G.Walk (componentRoot G (G.connectedComponentMk vertex.1))
      (nonrootParent G vertex) :=
  ((rootShortestPath G vertex.1).reverse.tail.reverse).copy rfl
    (reverse_snd_eq_penultimate G vertex)

theorem rootToParentWalk_length (vertex : NonrootVertex G) :
    (rootToParentWalk G vertex).length + 1 =
      (rootShortestPath G vertex.1).length := by
  rw [rootToParentWalk, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_tail_add_one]
  · exact SimpleGraph.Walk.length_reverse _
  · rw [SimpleGraph.Walk.nil_iff_length_eq,
      SimpleGraph.Walk.length_reverse]
    exact (SimpleGraph.Walk.nil_iff_length_eq.not.mp
      (rootShortestPath_not_nil G vertex))

theorem nonrootParent_dist_lt (vertex : NonrootVertex G) :
    G.dist (componentRoot G (G.connectedComponentMk vertex.1))
        (nonrootParent G vertex) <
      G.dist (componentRoot G (G.connectedComponentMk vertex.1)) vertex.1 := by
  have hle := SimpleGraph.dist_le (rootToParentWalk G vertex)
  have hparentLength := rootToParentWalk_length G vertex
  have hvertexLength := rootShortestPath_length G vertex.1
  omega

noncomputable def nonrootEdgeEmbedding : NonrootVertex G ↪ G.edgeSet where
  toFun vertex :=
    ⟨s(nonrootParent G vertex, vertex.1),
      (SimpleGraph.mem_edgeSet G).2 (nonrootParent_adj G vertex)⟩
  inj' := by
    intro left right hedge
    apply Subtype.ext
    have hedgeVal := congrArg Subtype.val hedge
    rw [Sym2.eq_iff] at hedgeVal
    rcases hedgeVal with hdirect | hswap
    · exact hdirect.2
    · have hadj : G.Adj left.1 right.1 := by
        simpa [hswap.2] using nonrootParent_adj G right
      have hcomponent : G.connectedComponentMk left.1 =
          G.connectedComponentMk right.1 :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hroot : componentRoot G (G.connectedComponentMk left.1) =
          componentRoot G (G.connectedComponentMk right.1) :=
        congrArg (componentRoot G) hcomponent
      have hleft := nonrootParent_dist_lt G left
      have hright := nonrootParent_dist_lt G right
      rw [hroot, hswap.1, hswap.2] at hleft
      exact (Nat.lt_asymm hleft hright).elim

theorem finite_graph_component_bound :
    Fintype.card V ≤ G.edgeFinset.card +
      Fintype.card G.ConnectedComponent := by
  classical
  have hedge := Fintype.card_le_of_injective (nonrootEdgeEmbedding G)
    (nonrootEdgeEmbedding G).injective
  have hpartition := Fintype.card_subtype_compl (IsComponentRoot G)
  have hrootLe : Fintype.card (RootVertex G) ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  have hsum : Fintype.card (NonrootVertex G) +
      Fintype.card (RootVertex G) = Fintype.card V := by
    rw [hpartition, Nat.sub_add_cancel hrootLe]
  rw [rootVertex_card] at hpartition
  have hedgeCard : Fintype.card G.edgeSet = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card]
  rw [hedgeCard] at hedge
  rw [rootVertex_card] at hsum
  omega

end BenzelProblem6Kernel

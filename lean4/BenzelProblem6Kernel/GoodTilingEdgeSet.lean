import BenzelProblem6Kernel.LiteralDirectedEdge
import BenzelProblem6Kernel.LiteralEnergyRigidity

/-!
# The directed edge finset of a good literal tiling
-/

namespace BenzelProblem6Kernel

def bonePlacementFinset {m : ℕ} (tiling : LiteralTiling m) :
    Finset (LiteralPlacement m) :=
  tiling.1.filter fun placement => placement.tile ≠ .stone

theorem bonePlacementFinset_card {m : ℕ} (tiling : LiteralTiling m) :
    (bonePlacementFinset tiling).card = boneCount tiling := rfl

noncomputable def directedEdgeOfBoneMember
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ bonePlacementFinset tiling}) : LiteralDirectedEdge m := by
  have hp := placement.2
  simp only [bonePlacementFinset, Finset.mem_filter] at hp
  exact literalDirectedEdgeOfPlacement placement.1 hp.2
    (every_literal_bone_has_two_owners hstone tiling placement.1 hp.1)

noncomputable def directedEdgeEmbedding
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    {p // p ∈ bonePlacementFinset tiling} ↪ LiteralDirectedEdge m where
  toFun := directedEdgeOfBoneMember hstone tiling
  inj' := by
    intro left right h
    apply Subtype.ext
    exact congrArg LiteralDirectedEdge.placement h

noncomputable def literalDirectedEdges
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Finset (LiteralDirectedEdge m) :=
  (bonePlacementFinset tiling).attach.map (directedEdgeEmbedding hstone tiling)

theorem literalDirectedEdges_card
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    (literalDirectedEdges hstone tiling).card = 3 * (m + 3) := by
  rw [literalDirectedEdges, Finset.card_map, Finset.card_attach,
    bonePlacementFinset_card, boneCount_of_conwayLagarias hstone]

theorem mem_literalDirectedEdges_placement
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (edge : LiteralDirectedEdge m)
    (hedge : edge ∈ literalDirectedEdges hstone tiling) :
    edge.placement ∈ tiling.1 ∧ edge.placement.tile ≠ .stone := by
  simp only [literalDirectedEdges, Finset.mem_map, Finset.mem_attach] at hedge
  obtain ⟨placement, _, heq⟩ := hedge
  have hp := placement.2
  simp only [bonePlacementFinset, Finset.mem_filter] at hp
  have hplacement : placement.1 = edge.placement := by
    simpa using congrArg LiteralDirectedEdge.placement heq
  constructor
  · rw [← hplacement]
    exact hp.1
  · rw [← hplacement]
    exact hp.2

end BenzelProblem6Kernel

import BenzelProblem6Kernel.LiteralCoveringRole
import BenzelProblem6Kernel.ActiveOwnerEdges

/-!
# Every present label of an active owner is covered by an incident edge
-/

namespace BenzelProblem6Kernel

theorem active_owner_present_label_role
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (p : SimplexPoint (m + 3))
    (hpActive : p ∈ activeOwnerFinset hstone tiling)
    (label : MicroLabel)
    (hmem : inPeripheralBenzel (m + 5) (ownerCell p label)) :
    ∃ edge ∈ literalDirectedEdges hstone tiling,
      (edge.source = p ∧ edge.boneClass.label ≠ label) ∨
        (edge.target = p ∧ edge.boneClass.label = label) := by
  classical
  let cell : BenzelCell (m + 5) := ⟨ownerCell p label, hmem⟩
  obtain ⟨placement, hplacement, _⟩ := tiling.2 cell
  have hbone : placement.tile ≠ .stone := by
    intro htile
    let member : {q // q ∈ stonePlacementFinset tiling} :=
      ⟨placement, by simp [stonePlacementFinset, hplacement.1, htile]⟩
    have howner : stoneOwner hstone tiling member = p :=
      stone_covering_owner_eq hstone tiling p label hmem member hplacement.2
    have hpStone : p ∈ stoneOwnerFinset hstone tiling := by
      simp only [stoneOwnerFinset, Finset.mem_map, Finset.mem_attach]
      refine ⟨member, by simp, ?_⟩
      simpa [stoneOwnerEmbedding] using howner
    have hpNotStone : p ∉ stoneOwnerFinset hstone tiling := by
      simpa [activeOwnerFinset] using hpActive
    exact hpNotStone hpStone
  obtain ⟨edge, hedge, _, hrole⟩ := covering_bone_edge_role hstone tiling
    p label hmem placement hplacement.1 hbone hplacement.2
  exact ⟨edge, hedge, hrole⟩

end BenzelProblem6Kernel

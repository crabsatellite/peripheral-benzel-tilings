import BenzelProblem6Kernel.LiteralPlacementBoundaryReverseFree
import BenzelProblem6Kernel.ContinuousBoundaryVertexFinset

/-! # Nonselected boundary edges survive at both endpoints of a splice -/

namespace BenzelProblem6Kernel

theorem GeometricTileBoundarySplice.rotatedTileRest_continuous {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    ContinuousLabeledEdgePath splice.sharedEdge.target
      splice.rotatedTileRest splice.sharedEdge.source := by
  let tile := literalPlacementRootedBoundary splice.placement
  have path := tile.continuous
  change ContinuousLabeledEdgePath tile.root
    (literalPlacementBoundary splice.placement) tile.root at path
  rw [splice.tile_eq] at path
  exact path.suffix_after_edge.append path.prefix_before_edge

theorem GeometricTileBoundarySplice.rotatedTileRest_nonempty {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    splice.rotatedTileRest ≠ [] := by
  intro hempty
  have hparts : splice.tileSuffix = [] ∧ splice.tilePrefix = [] := by
    exact List.append_eq_nil.mp hempty
  have hlength := literalPlacementBoundary_length splice.placement
  rw [splice.tile_eq, hparts.1, hparts.2] at hlength
  cases htile : splice.placement.tile <;> simp [htile] at hlength

theorem GeometricTileBoundarySplice.shared_mem_tile {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    splice.sharedEdge ∈ literalPlacementBoundary splice.placement := by
  rw [splice.tile_eq]
  simp

theorem GeometricTileBoundarySplice.shared_not_rotated {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    splice.sharedEdge ∉ splice.rotatedTileRest := by
  intro hmem
  have hcountRotated : 0 < splice.rotatedTileRest.count splice.sharedEdge :=
    List.count_pos_iff.mpr hmem
  have hcountTile := List.nodup_iff_count_le_one.mp
    (literalPlacementBoundary_nodup splice.placement) splice.sharedEdge
  rw [GeometricTileBoundarySplice.rotatedTileRest,
    List.count_append] at hcountRotated
  rw [splice.tile_eq, List.count_append, List.count_cons] at hcountTile
  simp at hcountTile
  omega

theorem GeometricTileBoundarySplice.reverse_shared_not_rotated {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    reverseLabeledHexEdge splice.sharedEdge ∉ splice.rotatedTileRest := by
  intro hmem
  apply literalPlacementBoundary_reverse_not_mem splice.placement
    splice.shared_mem_tile
  rw [splice.tile_eq]
  simp only [GeometricTileBoundarySplice.rotatedTileRest,
    List.mem_append] at hmem
  rcases hmem with hsuffix | hprefix
  · exact List.mem_append_right _ (by simp [hsuffix])
  · exact List.mem_append_left _ hprefix

theorem GeometricTileBoundarySplice.exists_target_alternative {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    ∃ edge ∈ splice.rotatedTileRest,
      edge.source = splice.sharedEdge.target ∧
      edge ≠ splice.sharedEdge ∧
      edge ≠ reverseLabeledHexEdge splice.sharedEdge := by
  have hsource := splice.rotatedTileRest_continuous.start_mem_source_of_ne_nil
    splice.rotatedTileRest_nonempty
  simp only [edgeSourceFinset, List.mem_toFinset,
    List.mem_map] at hsource
  obtain ⟨edge, hedge, hsource⟩ := hsource
  exact ⟨edge, hedge, hsource,
    fun heq => splice.shared_not_rotated (heq ▸ hedge),
    fun heq => splice.reverse_shared_not_rotated (heq ▸ hedge)⟩

theorem GeometricTileBoundarySplice.exists_source_alternative {m : ℕ}
    (splice : GeometricTileBoundarySplice m) :
    ∃ edge ∈ reverseReorientedEdges splice.rotatedTileRest,
      edge.source = splice.sharedEdge.source ∧
      edge ≠ splice.sharedEdge ∧
      edge ≠ reverseLabeledHexEdge splice.sharedEdge := by
  have hreversePath := splice.rotatedTileRest_continuous.reverse
  have hsource := hreversePath.start_mem_source_of_ne_nil (by
    simpa [reverseReorientedEdges] using splice.rotatedTileRest_nonempty)
  change splice.sharedEdge.source ∈ edgeSourceFinset
    (reverseReorientedEdges splice.rotatedTileRest) at hsource
  simp only [edgeSourceFinset, List.mem_toFinset,
    List.mem_map] at hsource
  obtain ⟨edge, hedge, hsource⟩ := hsource
  have horiginal : reverseLabeledHexEdge edge ∈ splice.rotatedTileRest :=
    (mem_reverseReorientedEdges_iff edge _).mp hedge
  refine ⟨edge, hedge, hsource, ?_, ?_⟩
  · intro heq
    subst edge
    exact splice.reverse_shared_not_rotated (by
      simpa [reverseLabeledHexEdge_involutive] using horiginal)
  · intro heq
    subst edge
    exact splice.shared_not_rotated (by
      simpa [reverseLabeledHexEdge_involutive] using horiginal)

end BenzelProblem6Kernel

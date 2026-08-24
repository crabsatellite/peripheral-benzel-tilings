import BenzelProblem6Kernel.ActiveOwnerEdges

/-!
# The unique active owner without an outgoing edge
-/

namespace BenzelProblem6Kernel

noncomputable def activeOwnerEdgeSourceFinset
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Finset (SimplexPoint (m + 3)) :=
  (literalDirectedEdges hstone tiling).image LiteralDirectedEdge.source

theorem edgeSource_injective_on
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    Set.InjOn LiteralDirectedEdge.source
      (literalDirectedEdges hstone tiling : Set (LiteralDirectedEdge m)) := by
  intro left hleft right hright hsource
  apply literalEdges_eq_of_placement_eq hstone tiling hleft hright
  exact edge_placements_eq_of_same_source hstone tiling hleft hright hsource

theorem activeOwnerEdgeSourceFinset_card
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    (activeOwnerEdgeSourceFinset hstone tiling).card = 3 * (m + 3) := by
  rw [activeOwnerEdgeSourceFinset,
    Finset.card_image_of_injOn (edgeSource_injective_on hstone tiling),
    literalDirectedEdges_card]

theorem activeOwnerEdgeSourceFinset_subset_active
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    activeOwnerEdgeSourceFinset hstone tiling ⊆ activeOwnerFinset hstone tiling := by
  intro p hp
  simp only [activeOwnerEdgeSourceFinset, Finset.mem_image] at hp
  obtain ⟨edge, hedge, rfl⟩ := hp
  exact edge_source_mem_active hstone tiling edge hedge

noncomputable def noOutgoingActiveFinset
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) : Finset (SimplexPoint (m + 3)) :=
  activeOwnerFinset hstone tiling \ activeOwnerEdgeSourceFinset hstone tiling

theorem noOutgoingActiveFinset_card
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    (noOutgoingActiveFinset hstone tiling).card = 1 := by
  rw [noOutgoingActiveFinset, Finset.card_sdiff,
    activeOwnerFinset_card hstone, activeOwnerEdgeSourceFinset_card hstone]
  · omega
  · exact activeOwnerEdgeSourceFinset_subset_active hstone tiling

theorem exists_unique_noOutgoingActiveOwner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∃! p : SimplexPoint (m + 3),
      p ∈ activeOwnerFinset hstone tiling ∧
        p ∉ activeOwnerEdgeSourceFinset hstone tiling := by
  have hcard := noOutgoingActiveFinset_card hstone tiling
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  refine ⟨p, ?_, ?_⟩
  · have hpmem : p ∈ noOutgoingActiveFinset hstone tiling := by
      rw [hp]
      simp
    simpa [noOutgoingActiveFinset] using hpmem
  · intro q hq
    have hqmem : q ∈ noOutgoingActiveFinset hstone tiling := by
      simpa [noOutgoingActiveFinset] using hq
    rw [hp] at hqmem
    simpa using hqmem

end BenzelProblem6Kernel

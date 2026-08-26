import D4KernelOnly.D4ShadowPlacement

/-! # Pairwise-disjoint subfamilies in the shared boundary carrier -/

namespace FiniteDefects

theorem mem_d4ShadowPlacementFinset_iff {m : ℕ}
    (tiling : D4LiteralTiling m)
    (placement : BenzelProblem6Kernel.LiteralPlacement m) :
    placement ∈ d4ShadowPlacementFinset tiling ↔
      ∃ source ∈ tiling.1, d4ShadowPlacement source = placement := by
  classical
  unfold d4ShadowPlacementFinset
  rw [Finset.mem_map]
  constructor
  · rintro ⟨source, hsource, heq⟩
    change d4ShadowPlacement source = placement at heq
    exact ⟨source, hsource, heq⟩
  · rintro ⟨source, hsource, heq⟩
    exact ⟨source, hsource, heq⟩

theorem d4ShadowSubfamily_flattened_cells_nodup {m : ℕ}
    (tiling : D4LiteralTiling m)
    (placements : Finset (BenzelProblem6Kernel.LiteralPlacement m))
    (hsubset : placements ⊆ d4ShadowPlacementFinset tiling) :
    (placements.toList.flatMap
      BenzelProblem6Kernel.LiteralPlacement.cells).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro placement hplacement
    exact BenzelProblem6Kernel.placementCellList_nodup placement.1
  · apply (Finset.nodup_toList placements).pairwise_of_forall_ne
    intro left hleft right hright hne
    have hleftMapped := hsubset (Finset.mem_toList.mp hleft)
    have hrightMapped := hsubset (Finset.mem_toList.mp hright)
    obtain ⟨leftSource, hleftSource, hleftEq⟩ :=
      (mem_d4ShadowPlacementFinset_iff tiling left).1 hleftMapped
    obtain ⟨rightSource, hrightSource, hrightEq⟩ :=
      (mem_d4ShadowPlacementFinset_iff tiling right).1 hrightMapped
    subst left
    subst right
    change List.Disjoint
      (d4ShadowPlacement leftSource).cells
      (d4ShadowPlacement rightSource).cells
    rw [d4ShadowPlacement_cells, d4ShadowPlacement_cells,
      List.disjoint_left]
    intro cell hcellLeft hcellRight
    have hsourceNe : leftSource ≠ rightSource := by
      intro heq
      apply hne
      exact congrArg d4ShadowPlacement heq
    let regionCell : D4Cell m :=
      ⟨cell, leftSource.2 cell hcellLeft⟩
    obtain ⟨covering, hcovering, hunique⟩ := tiling.2 regionCell
    have hleftUnique : leftSource = covering := hunique leftSource
      ⟨hleftSource, hcellLeft⟩
    have hrightUnique : rightSource = covering := hunique rightSource
      ⟨hrightSource, hcellRight⟩
    exact hsourceNe (hleftUnique.trans hrightUnique.symm)

end FiniteDefects

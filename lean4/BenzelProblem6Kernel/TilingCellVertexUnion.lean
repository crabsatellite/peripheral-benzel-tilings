import BenzelProblem6Kernel.BenzelCellVertices

/-! # The exact-cover union of all cell vertices -/

namespace BenzelProblem6Kernel

noncomputable def benzelCellVertexFinset (m : ℕ) : Finset HexVertex :=
  (Finset.univ : Finset (BenzelCell (m + 5))).biUnion
    (fun cell => cellVertexFinset cell.1)

noncomputable def benzelHexVertexValueFinset (m : ℕ) :
    Finset HexVertex :=
  (Finset.univ : Finset (BenzelHexVertex m)).image Subtype.val

theorem benzelCellVertexFinset_eq_valueFinset (m : ℕ) :
    benzelCellVertexFinset m = benzelHexVertexValueFinset m := by
  ext vertex
  simp only [benzelCellVertexFinset, benzelHexVertexValueFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨cell, hvertex⟩
    rw [mem_cellVertexFinset_iff] at hvertex
    rcases hvertex with
        ⟨anchor, label, hcell, hanchor⟩ |
        ⟨anchor, label, hcell, hanchor⟩
    · let upAnchor : UpBenzelVertexAnchor m :=
        ⟨anchor, ⟨label, by simpa [hcell] using cell.2⟩⟩
      let value : BenzelHexVertex m :=
        ⟨vertex, Or.inl ⟨upAnchor, hanchor⟩⟩
      exact ⟨value, by simp [value]⟩
    · let downAnchor : DownBenzelVertexAnchor m :=
        ⟨anchor, ⟨label, by simpa [hcell] using cell.2⟩⟩
      let value : BenzelHexVertex m :=
        ⟨vertex, Or.inr ⟨downAnchor, hanchor⟩⟩
      exact ⟨value, by simp [value]⟩
  · rintro ⟨value, _, rfl⟩
    rcases value.2 with ⟨anchor, hanchor⟩ | ⟨anchor, hanchor⟩
    · obtain ⟨label, hcell⟩ := anchor.2
      let cell : BenzelCell (m + 5) :=
        ⟨cellForOwnerAnchor anchor.1 label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inl ⟨anchor.1, label, rfl, hanchor⟩
    · obtain ⟨label, hcell⟩ := anchor.2
      let cell : BenzelCell (m + 5) :=
        ⟨downAnchorCell anchor.1 label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inr ⟨anchor.1, label, rfl, hanchor⟩

theorem card_benzelCellVertexFinset (m : ℕ) :
    (benzelCellVertexFinset m).card =
      Fintype.card (BenzelHexVertex m) := by
  rw [benzelCellVertexFinset_eq_valueFinset]
  exact Finset.card_image_iff.mpr Subtype.val_injective.injOn

theorem placementCellVertexFinset_eq_biUnion {m : ℕ}
    (placement : LiteralPlacement m) :
    placementCellVertexFinset placement =
      placement.cells.toFinset.biUnion cellVertexFinset := by
  ext vertex
  simp [placementCellVertexFinset, prototypeCellVertexFinset,
    orientedPrototypeCellBoundaryList, orientedCellBoundaryList,
    edgeSourceFinset, cellVertexFinset, List.mem_flatMap,
    LiteralPlacement.cells, placementCellList]
  aesop

noncomputable def tilingCellVertexFinset {m : ℕ}
    (tiling : LiteralTiling m) : Finset HexVertex :=
  tiling.1.biUnion placementCellVertexFinset

theorem tilingCellVertexFinset_eq_benzel {m : ℕ}
    (tiling : LiteralTiling m) :
    tilingCellVertexFinset tiling = benzelCellVertexFinset m := by
  ext vertex
  simp only [tilingCellVertexFinset, benzelCellVertexFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨placement, hplacement, hvertex⟩
    rw [placementCellVertexFinset_eq_biUnion,
      Finset.mem_biUnion] at hvertex
    obtain ⟨cell, hcell, hcellVertex⟩ := hvertex
    let regionCell : BenzelCell (m + 5) :=
      ⟨cell, placement.2 cell (List.mem_toFinset.mp hcell)⟩
    exact ⟨regionCell, hcellVertex⟩
  · rintro ⟨regionCell, hcellVertex⟩
    obtain ⟨placement, hplacement, hunique⟩ := tiling.2 regionCell
    refine ⟨placement, hplacement.1, ?_⟩
    rw [placementCellVertexFinset_eq_biUnion,
      Finset.mem_biUnion]
    exact ⟨regionCell.1,
      List.mem_toFinset.mpr hplacement.2, hcellVertex⟩

end BenzelProblem6Kernel

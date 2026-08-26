import D4KernelOnly.GeneralClassMinusOneTilingComplex
import BenzelProblem6Kernel.BenzelCellVertices

/-! # Finite vertex carrier of an arbitrary literal offset benzel -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def offsetUpAnchorFinset (t d : ℕ) : Finset Cell :=
  (Finset.univ : Finset (OffsetCell t d)).biUnion fun cell =>
    {cell.1, (cell.1.1 - 1, cell.1.2), (cell.1.1, cell.1.2 - 1)}

noncomputable def offsetDownAnchorFinset (t d : ℕ) : Finset Cell :=
  (Finset.univ : Finset (OffsetCell t d)).biUnion fun cell =>
    {cell.1, (cell.1.1, cell.1.2 - 1), (cell.1.1 + 1, cell.1.2 - 1)}

theorem mem_offsetUpAnchorFinset_iff
    (t d : ℕ) (anchor : Cell) :
    anchor ∈ offsetUpAnchorFinset t d ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (t + 2) (offsetB t d)
          (BenzelProblem6Kernel.cellForOwnerAnchor anchor label) := by
  simp only [offsetUpAnchorFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨cell, hanchor | hanchor | hanchor⟩
    · exact ⟨.zero, by simpa [BenzelProblem6Kernel.cellForOwnerAnchor,
        hanchor] using cell.2⟩
    · exact ⟨.one, by
        rcases cell with ⟨⟨i, j⟩, hcell⟩
        simp [BenzelProblem6Kernel.cellForOwnerAnchor] at hanchor ⊢
        subst anchor
        simpa using hcell⟩
    · exact ⟨.two, by
        rcases cell with ⟨⟨i, j⟩, hcell⟩
        simp [BenzelProblem6Kernel.cellForOwnerAnchor] at hanchor ⊢
        subst anchor
        simpa using hcell⟩
  · rintro ⟨label, hcell⟩
    cases label
    · exact ⟨⟨anchor, by simpa [BenzelProblem6Kernel.cellForOwnerAnchor]
        using hcell⟩, Or.inl rfl⟩
    · let cell : Cell := BenzelProblem6Kernel.cellForOwnerAnchor anchor .one
      refine ⟨⟨cell, hcell⟩, Or.inr (Or.inl ?_)⟩
      rcases anchor with ⟨i, j⟩
      simp [cell, BenzelProblem6Kernel.cellForOwnerAnchor]
    · let cell : Cell := BenzelProblem6Kernel.cellForOwnerAnchor anchor .two
      refine ⟨⟨cell, hcell⟩, Or.inr (Or.inr ?_)⟩
      rcases anchor with ⟨i, j⟩
      simp [cell, BenzelProblem6Kernel.cellForOwnerAnchor]

theorem mem_offsetDownAnchorFinset_iff
    (t d : ℕ) (anchor : Cell) :
    anchor ∈ offsetDownAnchorFinset t d ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (t + 2) (offsetB t d) (downAnchorCell anchor label) := by
  simp only [offsetDownAnchorFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨cell, hanchor | hanchor | hanchor⟩
    · exact ⟨.zero, by simpa [downAnchorCell, hanchor] using cell.2⟩
    · exact ⟨.one, by
        rcases cell with ⟨⟨i, j⟩, hcell⟩
        simp [downAnchorCell] at hanchor ⊢
        subst anchor
        simpa using hcell⟩
    · exact ⟨.two, by
        rcases cell with ⟨⟨i, j⟩, hcell⟩
        simp [downAnchorCell] at hanchor ⊢
        subst anchor
        simpa using hcell⟩
  · rintro ⟨label, hcell⟩
    cases label
    · exact ⟨⟨anchor, by simpa [downAnchorCell] using hcell⟩, Or.inl rfl⟩
    · let cell : Cell := downAnchorCell anchor .one
      refine ⟨⟨cell, hcell⟩, Or.inr (Or.inl ?_)⟩
      rcases anchor with ⟨i, j⟩
      simp [cell, downAnchorCell]
    · let cell : Cell := downAnchorCell anchor .two
      refine ⟨⟨cell, hcell⟩, Or.inr (Or.inr ?_)⟩
      rcases anchor with ⟨i, j⟩
      simp [cell, downAnchorCell]

noncomputable def offsetCellVertexFinset (t d : ℕ) : Finset HexVertex :=
  (Finset.univ : Finset (OffsetCell t d)).biUnion fun cell =>
    cellVertexFinset cell.1

noncomputable def offsetUpVertexFinset (t d : ℕ) : Finset HexVertex :=
  (offsetUpAnchorFinset t d).image upHexVertex

noncomputable def offsetDownVertexFinset (t d : ℕ) : Finset HexVertex :=
  (offsetDownAnchorFinset t d).image downHexVertex

theorem offsetCellVertexFinset_eq_up_union_down (t d : ℕ) :
    offsetCellVertexFinset t d =
      offsetUpVertexFinset t d ∪ offsetDownVertexFinset t d := by
  ext vertex
  simp only [offsetCellVertexFinset, offsetUpVertexFinset,
    offsetDownVertexFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨cell, hvertex⟩
    rw [mem_cellVertexFinset_iff] at hvertex
    rcases hvertex with ⟨anchor, label, hcell, hvertex⟩ |
        ⟨anchor, label, hcell, hvertex⟩
    · left
      refine ⟨anchor, ?_, hvertex⟩
      rw [mem_offsetUpAnchorFinset_iff]
      exact ⟨label, by simpa [hcell] using cell.2⟩
    · right
      refine ⟨anchor, ?_, hvertex⟩
      rw [mem_offsetDownAnchorFinset_iff]
      exact ⟨label, by simpa [hcell] using cell.2⟩
  · rintro (⟨anchor, hanchor, hvertex⟩ | ⟨anchor, hanchor, hvertex⟩)
    · obtain ⟨label, hcell⟩ :=
        (mem_offsetUpAnchorFinset_iff t d anchor).1 hanchor
      let cell : OffsetCell t d :=
        ⟨BenzelProblem6Kernel.cellForOwnerAnchor anchor label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inl ⟨anchor, label, rfl, hvertex⟩
    · obtain ⟨label, hcell⟩ :=
        (mem_offsetDownAnchorFinset_iff t d anchor).1 hanchor
      let cell : OffsetCell t d := ⟨downAnchorCell anchor label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inr ⟨anchor, label, rfl, hvertex⟩

theorem offsetUpDownVertexFinset_disjoint (t d : ℕ) :
    Disjoint (offsetUpVertexFinset t d) (offsetDownVertexFinset t d) := by
  rw [Finset.disjoint_left]
  intro vertex hup hdown
  obtain ⟨upAnchor, hupAnchor, hupEq⟩ := Finset.mem_image.mp hup
  obtain ⟨downAnchor, hdownAnchor, hdownEq⟩ := Finset.mem_image.mp hdown
  exact upHexVertex_ne_downHexVertex upAnchor downAnchor
    (hupEq.trans hdownEq.symm)

theorem card_offsetCellVertexFinset (t d : ℕ) :
    (offsetCellVertexFinset t d).card =
      (offsetUpAnchorFinset t d).card +
        (offsetDownAnchorFinset t d).card := by
  rw [offsetCellVertexFinset_eq_up_union_down,
    Finset.card_union_of_disjoint (offsetUpDownVertexFinset_disjoint t d),
    offsetUpVertexFinset, offsetDownVertexFinset,
    Finset.card_image_iff.mpr upHexVertex_injective.injOn,
    Finset.card_image_iff.mpr downHexVertex_injective.injOn]

end FiniteDefects

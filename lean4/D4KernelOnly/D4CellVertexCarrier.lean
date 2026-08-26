import D4KernelOnly.D4TilingComplex
import BenzelProblem6Kernel.BenzelCellVertices

/-! # Finite vertex carrier of the d=4 benzel -/

namespace FiniteDefects

open BenzelProblem6Kernel

noncomputable def d4UpAnchorFinset (m : ℕ) : Finset Cell :=
  (Finset.univ : Finset (D4Cell m)).biUnion fun cell =>
    {cell.1, (cell.1.1 - 1, cell.1.2), (cell.1.1, cell.1.2 - 1)}

noncomputable def d4DownAnchorFinset (m : ℕ) : Finset Cell :=
  (Finset.univ : Finset (D4Cell m)).biUnion fun cell =>
    {cell.1, (cell.1.1, cell.1.2 - 1), (cell.1.1 + 1, cell.1.2 - 1)}

theorem mem_d4UpAnchorFinset_iff (m : ℕ) (anchor : Cell) :
    anchor ∈ d4UpAnchorFinset m ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (m + 4) (2 * m + 4)
          (BenzelProblem6Kernel.cellForOwnerAnchor anchor label) := by
  simp only [d4UpAnchorFinset, Finset.mem_biUnion,
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

theorem mem_d4DownAnchorFinset_iff (m : ℕ) (anchor : Cell) :
    anchor ∈ d4DownAnchorFinset m ↔
      ∃ label : BenzelProblem6Kernel.MicroLabel,
        inBenzel (m + 4) (2 * m + 4)
          (downAnchorCell anchor label) := by
  simp only [d4DownAnchorFinset, Finset.mem_biUnion,
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

noncomputable def d4CellVertexFinset (m : ℕ) : Finset HexVertex :=
  (Finset.univ : Finset (D4Cell m)).biUnion fun cell =>
    cellVertexFinset cell.1

noncomputable def d4UpVertexFinset (m : ℕ) : Finset HexVertex :=
  (d4UpAnchorFinset m).image upHexVertex

noncomputable def d4DownVertexFinset (m : ℕ) : Finset HexVertex :=
  (d4DownAnchorFinset m).image downHexVertex

theorem d4CellVertexFinset_eq_up_union_down (m : ℕ) :
    d4CellVertexFinset m =
      d4UpVertexFinset m ∪ d4DownVertexFinset m := by
  ext vertex
  simp only [d4CellVertexFinset, d4UpVertexFinset, d4DownVertexFinset,
    Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨cell, hvertex⟩
    rw [mem_cellVertexFinset_iff] at hvertex
    rcases hvertex with
        ⟨anchor, label, hcell, hvertex⟩ |
        ⟨anchor, label, hcell, hvertex⟩
    · left
      refine ⟨anchor, ?_, hvertex⟩
      rw [mem_d4UpAnchorFinset_iff]
      exact ⟨label, by simpa [hcell] using cell.2⟩
    · right
      refine ⟨anchor, ?_, hvertex⟩
      rw [mem_d4DownAnchorFinset_iff]
      exact ⟨label, by simpa [hcell] using cell.2⟩
  · rintro (⟨anchor, hanchor, hvertex⟩ | ⟨anchor, hanchor, hvertex⟩)
    · obtain ⟨label, hcell⟩ := (mem_d4UpAnchorFinset_iff m anchor).1 hanchor
      let cell : D4Cell m :=
        ⟨BenzelProblem6Kernel.cellForOwnerAnchor anchor label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inl ⟨anchor, label, rfl, hvertex⟩
    · obtain ⟨label, hcell⟩ := (mem_d4DownAnchorFinset_iff m anchor).1 hanchor
      let cell : D4Cell m := ⟨downAnchorCell anchor label, hcell⟩
      refine ⟨cell, ?_⟩
      rw [mem_cellVertexFinset_iff]
      exact Or.inr ⟨anchor, label, rfl, hvertex⟩

theorem d4UpDownVertexFinset_disjoint (m : ℕ) :
    Disjoint (d4UpVertexFinset m) (d4DownVertexFinset m) := by
  rw [Finset.disjoint_left]
  intro vertex hup hdown
  obtain ⟨upAnchor, hupAnchor, hupEq⟩ := Finset.mem_image.mp hup
  obtain ⟨downAnchor, hdownAnchor, hdownEq⟩ := Finset.mem_image.mp hdown
  exact upHexVertex_ne_downHexVertex upAnchor downAnchor
    (hupEq.trans hdownEq.symm)

theorem card_d4UpVertexFinset (m : ℕ) :
    (d4UpVertexFinset m).card = (d4UpAnchorFinset m).card := by
  exact Finset.card_image_iff.mpr upHexVertex_injective.injOn

theorem card_d4DownVertexFinset (m : ℕ) :
    (d4DownVertexFinset m).card = (d4DownAnchorFinset m).card := by
  exact Finset.card_image_iff.mpr downHexVertex_injective.injOn

theorem card_d4CellVertexFinset (m : ℕ) :
    (d4CellVertexFinset m).card =
      (d4UpAnchorFinset m).card + (d4DownAnchorFinset m).card := by
  rw [d4CellVertexFinset_eq_up_union_down,
    Finset.card_union_of_disjoint (d4UpDownVertexFinset_disjoint m),
    card_d4UpVertexFinset, card_d4DownVertexFinset]

end FiniteDefects

import FiniteDefects.D4PathIncidence

/-! # Reconstructing a literal exact cover from defect and path data -/

namespace FiniteDefects

def D4DefectPathData.usesOwner {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2)) : Prop :=
  ∃ label, D4AbstractPathVisits (d4BoundaryOwner m label)
    (data.defect.core label) (data.paths label) p

noncomputable instance d4DataUsesOwnerDecidable {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2)) :
    Decidable (data.usesOwner p) := Classical.propDecidable _

abbrev D4UnusedFullOwner {m : ℕ} (data : D4DefectPathData m) :=
  {p : SimplexPoint (m + 2) // IsD4FullOwner p ∧ ¬data.usesOwner p}

noncomputable instance d4UnusedFullOwnerFintype {m : ℕ}
    (data : D4DefectPathData m) : Fintype (D4UnusedFullOwner data) :=
  Fintype.ofFinite (D4UnusedFullOwner data)

def D4DefectPathData.allEdges {m : ℕ} (data : D4DefectPathData m) :
    List (D4LiteralDirectedEdge m) :=
  data.paths .zero ++ data.paths .one ++ data.paths .two

noncomputable def D4DefectPathData.pathPlacements {m : ℕ}
    (data : D4DefectPathData m) : Finset (D4LiteralPlacement m) :=
  (data.allEdges.map D4LiteralDirectedEdge.placement).toFinset

noncomputable def D4DefectPathData.stonePlacements {m : ℕ}
    (data : D4DefectPathData m) : Finset (D4LiteralPlacement m) :=
  Finset.univ.image fun owner : D4UnusedFullOwner data =>
    d4ReverseStonePlacement owner.1 owner.2.1

noncomputable def D4DefectPathData.selectedPlacements {m : ℕ}
    (data : D4DefectPathData m) : Finset (D4LiteralPlacement m) :=
  insert data.defect.1 (data.pathPlacements ∪ data.stonePlacements)

theorem D4DefectPathData.edge_mem_allEdges {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    edge ∈ data.allEdges := by
  rcases label <;> simp [D4DefectPathData.allEdges, hmem]

theorem D4DefectPathData.edge_placement_mem {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    edge.placement ∈ data.selectedPlacements := by
  simp only [D4DefectPathData.selectedPlacements, Finset.mem_insert,
    Finset.mem_union]
  right; left
  simp only [D4DefectPathData.pathPlacements, List.mem_toFinset, List.mem_map]
  exact ⟨edge, data.edge_mem_allEdges label edge hmem, rfl⟩

theorem D4DefectPathData.defect_mem {m : ℕ}
    (data : D4DefectPathData m) :
    data.defect.1 ∈ data.selectedPlacements := by
  simp [D4DefectPathData.selectedPlacements]

theorem D4DefectPathData.unused_owner_stone_mem {m : ℕ}
    (data : D4DefectPathData m) (owner : D4UnusedFullOwner data) :
    d4ReverseStonePlacement owner.1 owner.2.1 ∈
      data.selectedPlacements := by
  simp only [D4DefectPathData.selectedPlacements, Finset.mem_insert,
    Finset.mem_union]
  right; right
  simp [D4DefectPathData.stonePlacements]

theorem D4DefectPathData.exists_cover {m : ℕ}
    (data : D4DefectPathData m) (cell : D4Cell m) :
    ∃ placement : D4LiteralPlacement m,
      placement ∈ data.selectedPlacements ∧
        D4PlacementCovers placement cell := by
  let pair := (d4OwnerCellEquiv m).symm cell
  let p := pair.1.1
  let label := pair.1.2
  have hcell : ownerCell p label = cell.1 := by
    have h := (d4OwnerCellEquiv m).apply_symm_apply cell
    exact congrArg Subtype.val h
  have hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label) := by
    rw [hcell]
    exact cell.2
  by_cases hused : data.usesOwner p
  · obtain ⟨pathLabel, hvisit⟩ := hused
    by_cases hsame : label = pathLabel
    · by_cases hcore : p = data.defect.core pathLabel
      · refine ⟨data.defect.1, data.defect_mem, ?_⟩
        have hcover := data.defect.covers_core pathLabel
        have hcellEq :
            (⟨ownerCell (data.defect.core pathLabel) pathLabel,
              data.defect.core_present pathLabel⟩ : D4Cell m) = cell := by
          apply Subtype.ext
          rw [← hcell, hcore, ← hsame]
        rw [← hcellEq]
        exact hcover
      · obtain ⟨edge, hedge, htarget, hedgeLabel⟩ :=
          reversePath_target_exists_of_ne_core (data.path_spec pathLabel)
            hvisit hcore
        refine ⟨edge.placement, data.edge_placement_mem pathLabel edge hedge, ?_⟩
        have htargetPresent : inBenzel (m + 4) (2 * m + 4)
            (ownerCell edge.target edge.boneClass.label) := by
          simpa [htarget, hedgeLabel, hsame] using hpresent
        have hcover := d4GoodEdge_covers_target_label edge htargetPresent
        have hcellEq :
            (⟨ownerCell edge.target edge.boneClass.label,
              htargetPresent⟩ : D4Cell m) = cell := by
          apply Subtype.ext
          change ownerCell edge.target edge.boneClass.label = cell.1
          rw [← hcell, htarget, hedgeLabel, hsame]
        rw [← hcellEq]
        exact hcover
    · have hnotTerminal : p ≠ d4BoundaryOwner m pathLabel := by
        intro hp
        have hpresent' : inBenzel (m + 4) (2 * m + 4)
            (ownerCell (d4BoundaryOwner m pathLabel) label) := by
          simpa [hp] using hpresent
        have hlabel :=
          (d4BoundaryOwner_present_iff m pathLabel label).1 hpresent'
        exact hsame hlabel
      obtain ⟨edge, hedge, hsource, hedgeLabel⟩ :=
        reversePath_source_exists_of_ne_terminal (data.path_spec pathLabel)
          hvisit hnotTerminal
      refine ⟨edge.placement, data.edge_placement_mem pathLabel edge hedge, ?_⟩
      have hne : label ≠ edge.boneClass.label := by
        intro heq
        exact hsame (heq.trans hedgeLabel)
      have hsourcePresent : inBenzel (m + 4) (2 * m + 4)
          (ownerCell edge.source label) := by simpa [hsource] using hpresent
      have hcover := d4GoodEdge_covers_source_other edge label hne hsourcePresent
      simpa [hsource, hcell] using hcover
  · have hfull : IsD4FullOwner p := by
      rcases d4_owner_full_or_boundary p with hfull | hboundary
      · exact hfull
      · obtain ⟨endpointLabel, hp⟩ := hboundary
        exfalso
        apply hused
        refine ⟨endpointLabel, ?_⟩
        exact Or.inl hp
    let owner : D4UnusedFullOwner data := ⟨p, hfull, hused⟩
    refine ⟨d4ReverseStonePlacement owner.1 owner.2.1,
      data.unused_owner_stone_mem owner, ?_⟩
    have hcover := d4ReverseStonePlacement_covers owner.1 owner.2.1 label
    simpa [owner, hcell] using hcover

end FiniteDefects

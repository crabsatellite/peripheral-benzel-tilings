import FiniteDefects.D4PathUniqueness

/-! # Uniqueness of the reconstructed covering placement -/

namespace FiniteDefects

theorem D4DefectPathData.path_label_unique {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2))
    (left right : MicroLabel)
    (hleft : D4AbstractPathVisits (d4BoundaryOwner m left)
      (data.defect.core left) (data.paths left) p)
    (hright : D4AbstractPathVisits (d4BoundaryOwner m right)
      (data.defect.core right) (data.paths right) p) : left = right := by
  rcases left <;> rcases right
  all_goals first
    | rfl
    | exact (d4_paths_zero_one_disjoint data p hleft hright).elim
    | exact (d4_paths_two_zero_disjoint data p hright hleft).elim
    | exact (d4_paths_zero_one_disjoint data p hright hleft).elim
    | exact (d4_paths_one_two_disjoint data p hleft hright).elim
    | exact (d4_paths_two_zero_disjoint data p hleft hright).elim
    | exact (d4_paths_one_two_disjoint data p hright hleft).elim

theorem D4DefectPathData.pathPlacement_witness {m : ℕ}
    (data : D4DefectPathData m) (placement : D4LiteralPlacement m)
    (hmem : placement ∈ data.pathPlacements) :
    ∃ label edge, edge ∈ data.paths label ∧ edge.placement = placement := by
  simp only [D4DefectPathData.pathPlacements, List.mem_toFinset,
    List.mem_map] at hmem
  obtain ⟨edge, hedge, heq⟩ := hmem
  have hclass : edge ∈ data.paths .zero ∨ edge ∈ data.paths .one ∨
      edge ∈ data.paths .two := by
    simpa [D4DefectPathData.allEdges] using hedge
  rcases hclass with hzero | hone | htwo
  · exact ⟨.zero, edge, hzero, heq⟩
  · exact ⟨.one, edge, hone, heq⟩
  · exact ⟨.two, edge, htwo, heq⟩

theorem D4DefectPathData.stonePlacement_witness {m : ℕ}
    (data : D4DefectPathData m) (placement : D4LiteralPlacement m)
    (hmem : placement ∈ data.stonePlacements) :
    ∃ owner : D4UnusedFullOwner data,
      d4ReverseStonePlacement owner.1 owner.2.1 = placement := by
  simp [D4DefectPathData.stonePlacements] at hmem
  obtain ⟨owner, howner, heq⟩ := hmem
  exact ⟨⟨owner, howner⟩, heq⟩

theorem D4DefectPathData.defect_path_role_false {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2))
    (label pathLabel : MicroLabel) (edge : D4LiteralDirectedEdge m)
    (hcore : p = data.defect.core label)
    (hedge : edge ∈ data.paths pathLabel)
    (hvisit : D4AbstractPathVisits (d4BoundaryOwner m pathLabel)
      (data.defect.core pathLabel) (data.paths pathLabel) p)
    (hrole : (p = edge.source ∧ label ≠ edge.boneClass.label) ∨
      (p = edge.target ∧ label = edge.boneClass.label)) : False := by
  have labelVisit : D4AbstractPathVisits (d4BoundaryOwner m label)
      (data.defect.core label) (data.paths label) p :=
    Or.inr (Or.inl hcore)
  have hlabels := data.path_label_unique p label pathLabel labelVisit hvisit
  subst pathLabel
  have hedgeLabel := (data.path_spec label).all_labels edge hedge
  rcases hrole with hsource | htarget
  · exact hsource.2 hedgeLabel.symm
  · have hne := reversePath_target_ne_core (data.path_spec label) edge hedge
    exact hne (htarget.1.symm.trans hcore)

theorem D4DefectPathData.path_stone_false {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2))
    (pathLabel : MicroLabel)
    (hvisit : D4AbstractPathVisits (d4BoundaryOwner m pathLabel)
      (data.defect.core pathLabel) (data.paths pathLabel) p)
    (owner : D4UnusedFullOwner data) (hpowner : p = owner.1) : False := by
  apply owner.2.2
  exact ⟨pathLabel, by simpa [hpowner] using hvisit⟩

theorem D4DefectPathData.defect_stone_false {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2))
    (label : MicroLabel) (hcore : p = data.defect.core label)
    (owner : D4UnusedFullOwner data) (hpowner : p = owner.1) : False := by
  apply owner.2.2
  exact ⟨label, Or.inr (Or.inl (hpowner.symm.trans hcore))⟩

theorem d4ReverseStone_cover_owner {m : ℕ}
    (owner : SimplexPoint (m + 2)) (hfull : IsD4FullOwner owner)
    (p : SimplexPoint (m + 2)) (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (hcover : D4PlacementCovers (d4ReverseStonePlacement owner hfull)
      ⟨ownerCell p label, hpresent⟩) : p = owner := by
  obtain ⟨coveredLabel, hraw⟩ := d4ReverseStonePlacement_cover_role
    owner hfull (ownerCell p label) hcover
  exact (owner_representation_unique (ownerCell p label) p owner label
    coveredLabel rfl hraw.symm).1

theorem D4DefectPathData.selected_cover_category {m : ℕ}
    (data : D4DefectPathData m) (p : SimplexPoint (m + 2))
    (label : MicroLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label))
    (placement : D4LiteralPlacement m)
    (hmem : placement ∈ data.selectedPlacements)
    (hcover : D4PlacementCovers placement ⟨ownerCell p label, hpresent⟩) :
    (placement = data.defect.1 ∧ p = data.defect.core label) ∨
    (∃ pathLabel edge, edge ∈ data.paths pathLabel ∧
      edge.placement = placement ∧
      D4AbstractPathVisits (d4BoundaryOwner m pathLabel)
        (data.defect.core pathLabel) (data.paths pathLabel) p ∧
      ((p = edge.source ∧ label ≠ edge.boneClass.label) ∨
        (p = edge.target ∧ label = edge.boneClass.label))) ∨
    (∃ owner : D4UnusedFullOwner data,
      d4ReverseStonePlacement owner.1 owner.2.1 = placement ∧ p = owner.1) := by
  simp only [D4DefectPathData.selectedPlacements, Finset.mem_insert,
    Finset.mem_union] at hmem
  rcases hmem with heq | hpath | hstone
  · subst placement
    exact Or.inl ⟨rfl, data.defect.cover_is_core p label hpresent hcover⟩
  · obtain ⟨pathLabel, edge, hedge, hedgePlacement⟩ :=
      data.pathPlacement_witness placement hpath
    have hrole := d4_good_edge_cover_role edge p label hpresent (by
      rw [hedgePlacement]
      exact hcover)
    have hvisit : D4AbstractPathVisits (d4BoundaryOwner m pathLabel)
        (data.defect.core pathLabel) (data.paths pathLabel) p := by
      rcases hrole with hsource | htarget
      · exact Or.inr (Or.inr ⟨edge, hedge, Or.inl hsource.1⟩)
      · exact Or.inr (Or.inr ⟨edge, hedge, Or.inr htarget.1⟩)
    exact Or.inr (Or.inl
      ⟨pathLabel, edge, hedge, hedgePlacement, hvisit, hrole⟩)
  · obtain ⟨owner, hownerPlacement⟩ :=
      data.stonePlacement_witness placement hstone
    have hpowner := d4ReverseStone_cover_owner owner.1 owner.2.1 p label
      hpresent (by rw [hownerPlacement]; exact hcover)
    exact Or.inr (Or.inr ⟨owner, hownerPlacement, hpowner⟩)

theorem D4DefectPathData.cover_unique {m : ℕ}
    (data : D4DefectPathData m) (cell : D4Cell m)
    (left right : D4LiteralPlacement m)
    (hleftMem : left ∈ data.selectedPlacements)
    (hrightMem : right ∈ data.selectedPlacements)
    (hleftCover : D4PlacementCovers left cell)
    (hrightCover : D4PlacementCovers right cell) : left = right := by
  let pair := (d4OwnerCellEquiv m).symm cell
  let p := pair.1.1
  let label := pair.1.2
  have hcell : ownerCell p label = cell.1 := by
    exact congrArg Subtype.val ((d4OwnerCellEquiv m).apply_symm_apply cell)
  have hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label) := by
    rw [hcell]
    exact cell.2
  have hleftCover' : D4PlacementCovers left
      ⟨ownerCell p label, hpresent⟩ := by simpa [hcell] using hleftCover
  have hrightCover' : D4PlacementCovers right
      ⟨ownerCell p label, hpresent⟩ := by simpa [hcell] using hrightCover
  have hleft := data.selected_cover_category p label hpresent left
    hleftMem hleftCover'
  have hright := data.selected_cover_category p label hpresent right
    hrightMem hrightCover'
  rcases hleft with hldef | hlpath | hlstone
  · rcases hright with hrdef | hrpath | hrstone
    · exact hldef.1.trans hrdef.1.symm
    · obtain ⟨rlabel, redge, redgeMem, _, rvisit, rrole⟩ := hrpath
      exact (data.defect_path_role_false p label rlabel redge hldef.2
        redgeMem rvisit rrole).elim
    · obtain ⟨owner, _, hpowner⟩ := hrstone
      exact (data.defect_stone_false p label hldef.2 owner hpowner).elim
  · rcases hright with hrdef | hrpath | hrstone
    · obtain ⟨llabel, ledge, ledgeMem, _, lvisit, lrole⟩ := hlpath
      exact (data.defect_path_role_false p label llabel ledge hrdef.2
        ledgeMem lvisit lrole).elim
    · obtain ⟨llabel, ledge, ledgeMem, ledgePlacement, lvisit, lrole⟩ := hlpath
      obtain ⟨rlabel, redge, redgeMem, redgePlacement, rvisit, rrole⟩ := hrpath
      have hlabels := data.path_label_unique p llabel rlabel lvisit rvisit
      subst rlabel
      have lEdgeLabel := (data.path_spec llabel).all_labels ledge ledgeMem
      have rEdgeLabel := (data.path_spec llabel).all_labels redge redgeMem
      rcases lrole with lsource | ltarget
      · rcases rrole with rsource | rtarget
        · have hedge := reversePath_source_unique (data.path_spec llabel)
            ledge redge ledgeMem redgeMem (lsource.1.symm.trans rsource.1)
          exact (ledgePlacement.symm.trans
            (congrArg D4LiteralDirectedEdge.placement hedge)).trans redgePlacement
        · exact (lsource.2 (rtarget.2.trans
            (rEdgeLabel.trans lEdgeLabel.symm))).elim
      · rcases rrole with rsource | rtarget
        · exact (rsource.2 (ltarget.2.trans
            (lEdgeLabel.trans rEdgeLabel.symm))).elim
        · have hedge := reversePath_target_unique (data.path_spec llabel)
            ledge redge ledgeMem redgeMem (ltarget.1.symm.trans rtarget.1)
          exact (ledgePlacement.symm.trans
            (congrArg D4LiteralDirectedEdge.placement hedge)).trans redgePlacement
    · obtain ⟨llabel, _, _, _, lvisit, _⟩ := hlpath
      obtain ⟨owner, _, hpowner⟩ := hrstone
      exact (data.path_stone_false p llabel lvisit owner hpowner).elim
  · rcases hright with hrdef | hrpath | hrstone
    · obtain ⟨owner, _, hpowner⟩ := hlstone
      exact (data.defect_stone_false p label hrdef.2 owner hpowner).elim
    · obtain ⟨rlabel, _, _, _, rvisit, _⟩ := hrpath
      obtain ⟨owner, _, hpowner⟩ := hlstone
      exact (data.path_stone_false p rlabel rvisit owner hpowner).elim
    · obtain ⟨lowner, lplacement, hlp⟩ := hlstone
      obtain ⟨rowner, rplacement, hrp⟩ := hrstone
      have howner : lowner = rowner := by
        apply Subtype.ext
        exact hlp.symm.trans hrp
      subst rowner
      exact lplacement.symm.trans rplacement

noncomputable def d4ReconstructedTiling {m : ℕ}
    (data : D4DefectPathData m) : D4LiteralTiling m :=
  ⟨data.selectedPlacements, by
    intro cell
    obtain ⟨placement, hmem, hcover⟩ := data.exists_cover cell
    exact ⟨placement, ⟨hmem, hcover⟩, fun candidate hc =>
      data.cover_unique cell candidate placement hc.1 hmem hc.2 hcover⟩⟩

end FiniteDefects

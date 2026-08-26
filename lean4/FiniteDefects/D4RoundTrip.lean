import FiniteDefects.D4UniqueCover

/-! # Canonical-path uniqueness and the literal bijection round trip -/

namespace FiniteDefects

noncomputable def D4DefectPathData.edgeAsGood {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    D4GoodBonePlacement (d4ReconstructedTiling data) :=
  ⟨edge.placement, data.edge_placement_mem label edge hmem,
    d4LiteralDirectedEdge_is_bone edge,
    d4LiteralDirectedEdge_not_three_owner edge⟩

theorem D4DefectPathData.edgeAsGood_edge {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    (data.edgeAsGood label edge hmem).edge = edge := by
  apply D4LiteralDirectedEdge.ext_of_placement
  rfl

@[simp] theorem D4DefectPathData.edgeAsGood_source {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    (data.edgeAsGood label edge hmem).source = edge.source := by
  unfold D4GoodBonePlacement.source
  rw [data.edgeAsGood_edge label edge hmem]

@[simp] theorem D4DefectPathData.edgeAsGood_target {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    (data.edgeAsGood label edge hmem).target = edge.target := by
  unfold D4GoodBonePlacement.target
  rw [data.edgeAsGood_edge label edge hmem]

@[simp] theorem D4DefectPathData.edgeAsGood_label {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edge : D4LiteralDirectedEdge m) (hmem : edge ∈ data.paths label) :
    (data.edgeAsGood label edge hmem).label = edge.boneClass.label := by
  unfold D4GoodBonePlacement.label
  rw [data.edgeAsGood_edge label edge hmem]

noncomputable def D4DefectPathData.wrapPathList {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    (edges : List (D4LiteralDirectedEdge m)) →
      (∀ edge ∈ edges, edge ∈ data.paths label) →
      List (D4GoodBonePlacement (d4ReconstructedTiling data))
  | [], _ => []
  | edge :: rest, hsub =>
      data.edgeAsGood label edge (hsub edge (by simp)) ::
        data.wrapPathList label rest
          (fun candidate hmem => hsub candidate (by simp [hmem]))

noncomputable def D4DefectPathData.wrappedPath {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    List (D4GoodBonePlacement (d4ReconstructedTiling data)) :=
  data.wrapPathList label (data.paths label) (fun _ h => h)

theorem D4DefectPathData.wrappedPath_spec {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    IsD4ReversePath label (d4BoundaryOwner m label)
      (data.defect.core label) (data.wrappedPath label) := by
  have helper (edges : List (D4LiteralDirectedEdge m))
      (hsub : ∀ edge ∈ edges, edge ∈ data.paths label)
      {terminal core : SimplexPoint (m + 2)}
      (hpath : IsD4AbstractReversePath label terminal core edges) :
      IsD4ReversePath label terminal core
        (data.wrapPathList label edges hsub) := by
    induction edges generalizing terminal with
    | nil => exact hpath
    | cons head rest ih =>
        simp only [IsD4AbstractReversePath] at hpath
        rw [D4DefectPathData.wrapPathList]
        simp only [IsD4ReversePath]
        refine ⟨by simpa using hpath.1,
          by simpa using hpath.2.1, ?_⟩
        simpa only [data.edgeAsGood_source label head
          (hsub head (by simp))] using
          ih (fun edge hedge => hsub edge (by simp [hedge])) hpath.2.2
  exact helper (data.paths label) (fun _ h => h) (data.path_spec label)

theorem D4DefectPathData.wrapPathList_map_edge {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel)
    (edges : List (D4LiteralDirectedEdge m))
    (hsub : ∀ edge ∈ edges, edge ∈ data.paths label) :
    (data.wrapPathList label edges hsub).map D4GoodBonePlacement.edge = edges := by
  induction edges with
  | nil => rfl
  | cons head rest ih =>
      rw [D4DefectPathData.wrapPathList, List.map_cons]
      rw [data.edgeAsGood_edge label head (hsub head (by simp))]
      congr 1
      exact ih (fun edge hedge => hsub edge (by simp [hedge]))

theorem D4DefectPathData.wrappedPath_map_edge {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    (data.wrappedPath label).map D4GoodBonePlacement.edge = data.paths label :=
  data.wrapPathList_map_edge label (data.paths label) (fun _ h => h)

theorem reconstructed_badPlacement {m : ℕ} (data : D4DefectPathData m) :
    d4BadPlacement (d4ReconstructedTiling data) = data.defect.1 := by
  exact (d4BadPlacement_unique (d4ReconstructedTiling data) data.defect.1
    data.defect_mem data.defect.2).symm

theorem reconstructed_defect {m : ℕ} (data : D4DefectPathData m) :
    d4TilingDefect (d4ReconstructedTiling data) = data.defect := by
  apply Subtype.ext
  exact reconstructed_badPlacement data

theorem reconstructed_core {m : ℕ} (data : D4DefectPathData m)
    (label : MicroLabel) :
    d4DefectCore (d4ReconstructedTiling data) label =
      data.defect.core label := by
  rw [← d4TilingDefect_core (d4ReconstructedTiling data) label,
    reconstructed_defect data]

theorem d4TilingEdge_target_ne_core {m : ℕ}
    {tiling : D4LiteralTiling m} (edge : D4GoodBonePlacement tiling) :
    edge.target ≠ d4DefectCore tiling edge.label := by
  intro htarget
  have hpresent := d4GoodEdge_target_present edge.edge
  have hedgeCover := d4TilingEdge_covers_target edge hpresent
  let defect := d4TilingDefect tiling
  have hdefCore : defect.core edge.label = d4DefectCore tiling edge.label :=
    d4TilingDefect_core tiling edge.label
  have hbadCover0 := defect.covers_core edge.label
  have hbadPresent : inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.target edge.label) := by
    change inBenzel (m + 4) (2 * m + 4)
      (ownerCell edge.edge.target edge.edge.boneClass.label)
    exact hpresent
  have hbadCover : D4PlacementCovers (d4BadPlacement tiling)
      ⟨ownerCell edge.target edge.label, hbadPresent⟩ := by
    have hcellEq :
        (⟨ownerCell (defect.core edge.label) edge.label,
          defect.core_present edge.label⟩ : D4Cell m) =
        ⟨ownerCell edge.target edge.label, hbadPresent⟩ := by
      apply Subtype.ext
      change ownerCell (defect.core edge.label) edge.label =
        ownerCell edge.target edge.label
      rw [hdefCore, ← htarget]
    rw [← hcellEq]
    exact hbadCover0
  have heq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.target edge.label, hpresent⟩ edge.1 edge.2.1 hedgeCover
  have hbadEq := d4CoveringPlacement_unique tiling
    ⟨ownerCell edge.target edge.label, hpresent⟩ (d4BadPlacement tiling)
      (d4BadPlacement_mem tiling) (by simpa [htarget] using hbadCover)
  have hplacement : edge.1 = d4BadPlacement tiling := heq.trans hbadEq.symm
  have hbone := edge.2.2.1
  rw [hplacement] at hbone
  rcases d4BadPlacement_isBad tiling with hwrong | hthree
  · exact hbone hwrong.1
  · exact edge.2.2.2 (by simpa [hplacement] using hthree)

theorem d4ReversePaths_unique {m : ℕ}
    {tiling : D4LiteralTiling m} (label : MicroLabel)
    (terminal : SimplexPoint (m + 2))
    (left right : List (D4GoodBonePlacement tiling))
    (hleft : IsD4ReversePath label terminal
      (d4DefectCore tiling label) left)
    (hright : IsD4ReversePath label terminal
      (d4DefectCore tiling label) right) : left = right := by
  induction left generalizing terminal right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head rest =>
          simp only [IsD4ReversePath] at hleft hright
          apply False.elim
          apply d4TilingEdge_target_ne_core head
          rw [hright.2.1]
          exact hright.1.trans hleft
  | cons head rest ih =>
      cases right with
      | nil =>
          simp only [IsD4ReversePath] at hleft hright
          apply False.elim
          apply d4TilingEdge_target_ne_core head
          rw [hleft.2.1]
          exact hleft.1.trans hright
      | cons other tail =>
          simp only [IsD4ReversePath] at hleft hright
          have hhead : head = other := d4TilingEdge_target_label_unique head other
            (hleft.1.trans hright.1.symm)
            (hleft.2.1.trans hright.2.1.symm)
          subst other
          congr 1
          exact ih head.source tail hleft.2.2 hright.2.2

theorem d4ReverseBoundaryPath_unique {m : ℕ}
    (tiling : D4LiteralTiling m) (label : MicroLabel)
    (edges : List (D4GoodBonePlacement tiling))
    (hpath : IsD4ReversePath label (d4BoundaryOwner m label)
      (d4DefectCore tiling label) edges) :
    edges = d4ReverseBoundaryPath tiling label :=
  d4ReversePaths_unique label (d4BoundaryOwner m label)
    edges (d4ReverseBoundaryPath tiling label)
    hpath (d4ReverseBoundaryPath_spec tiling label)

theorem reconstructed_wrappedPath_eq_canonical {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    data.wrappedPath label =
      d4ReverseBoundaryPath (d4ReconstructedTiling data) label := by
  apply d4ReverseBoundaryPath_unique
  have hpath := data.wrappedPath_spec label
  rw [reconstructed_core data label]
  exact hpath

theorem reconstructed_extraction_paths {m : ℕ}
    (data : D4DefectPathData m) (label : MicroLabel) :
    (d4ExtractedPathData (d4ReconstructedTiling data)).paths label =
      data.paths label := by
  change (d4ReverseBoundaryPath (d4ReconstructedTiling data) label).map
      D4GoodBonePlacement.edge = data.paths label
  rw [← reconstructed_wrappedPath_eq_canonical data label,
    data.wrappedPath_map_edge label]

theorem reconstructed_extraction {m : ℕ} (data : D4DefectPathData m) :
    d4ExtractedPathData (d4ReconstructedTiling data) = data := by
  let lhs := d4ExtractedPathData (d4ReconstructedTiling data)
  have hdefect : lhs.defect = data.defect := reconstructed_defect data
  have hpaths : lhs.paths = data.paths := by
    funext label
    exact reconstructed_extraction_paths data label
  change lhs = data
  rcases lhs with ⟨lhsDefect, lhsPaths, lhsSpec⟩
  rcases data with ⟨dataDefect, dataPaths, dataSpec⟩
  dsimp only at hdefect hpaths
  subst lhsDefect
  subst lhsPaths
  rfl

end FiniteDefects

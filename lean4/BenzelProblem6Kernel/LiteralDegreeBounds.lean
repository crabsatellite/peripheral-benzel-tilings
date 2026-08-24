import BenzelProblem6Kernel.GoodTilingDegrees
import BenzelProblem6Kernel.LiteralEdgeCoverage
import Mathlib.Data.Finset.Card

/-!
# Local source and labelled-target degree bounds
-/

namespace BenzelProblem6Kernel

theorem exists_microLabel_ne_two (left right : MicroLabel) :
    ∃ label : MicroLabel, label ≠ left ∧ label ≠ right := by
  rcases left <;> rcases right
  all_goals first | exact ⟨.zero, by decide, by decide⟩ |
    exact ⟨.one, by decide, by decide⟩ |
    exact ⟨.two, by decide, by decide⟩

theorem literalEdges_eq_of_placement_eq
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {left right : LiteralDirectedEdge m}
    (hleft : left ∈ literalDirectedEdges hstone tiling)
    (hright : right ∈ literalDirectedEdges hstone tiling)
    (hplacement : left.placement = right.placement) : left = right := by
  simp only [literalDirectedEdges, Finset.mem_map, Finset.mem_attach] at hleft hright
  obtain ⟨leftPlacement, _, hleftEq⟩ := hleft
  obtain ⟨rightPlacement, _, hrightEq⟩ := hright
  have hvalues : leftPlacement.1 = rightPlacement.1 := by
    have hl := congrArg LiteralDirectedEdge.placement hleftEq
    have hr := congrArg LiteralDirectedEdge.placement hrightEq
    calc
      leftPlacement.1 = left.placement := by simpa using hl
      _ = right.placement := hplacement
      _ = rightPlacement.1 := by simpa using hr.symm
  have hsubtype : leftPlacement = rightPlacement := by
    apply Subtype.ext
    exact hvalues
  rw [← hleftEq, ← hrightEq, hsubtype]

theorem edge_placements_eq_of_same_source
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {left right : LiteralDirectedEdge m}
    (hleft : left ∈ literalDirectedEdges hstone tiling)
    (hright : right ∈ literalDirectedEdges hstone tiling)
    (hsource : left.source = right.source) :
    left.placement = right.placement := by
  obtain ⟨label, hlabelLeft, hlabelRight⟩ :=
    exists_microLabel_ne_two left.boneClass.label right.boneClass.label
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell left.source label,
      literalDirectedEdge_source_cell_mem left label hlabelLeft⟩
  have hleftCover : PlacementCovers left.placement cell := by
    exact literalDirectedEdge_covers_source_cell left label hlabelLeft
  have hrightCover : PlacementCovers right.placement cell := by
    have hcover := literalDirectedEdge_covers_source_cell right label hlabelRight
    have hcell :
        (⟨ownerCell right.source label,
          literalDirectedEdge_source_cell_mem right label hlabelRight⟩ :
          BenzelCell (m + 5)) = cell := by
      apply Subtype.ext
      simp [cell, hsource]
    simpa [hcell] using hcover
  have hleftMem := (mem_literalDirectedEdges_placement hstone tiling left hleft).1
  have hrightMem := (mem_literalDirectedEdges_placement hstone tiling right hright).1
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have hl := hunique left.placement ⟨hleftMem, hleftCover⟩
  have hr := hunique right.placement ⟨hrightMem, hrightCover⟩
  exact hl.trans hr.symm

theorem edge_placements_eq_of_same_target_label
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    {left right : LiteralDirectedEdge m}
    (hleft : left ∈ literalDirectedEdges hstone tiling)
    (hright : right ∈ literalDirectedEdges hstone tiling)
    (htarget : left.target = right.target)
    (hlabel : left.boneClass.label = right.boneClass.label) :
    left.placement = right.placement := by
  let cell : BenzelCell (m + 5) :=
    ⟨ownerCell left.target left.boneClass.label,
      literalDirectedEdge_target_cell_mem left⟩
  have hleftCover : PlacementCovers left.placement cell :=
    literalDirectedEdge_covers_target_cell left
  have hrightCover : PlacementCovers right.placement cell := by
    have hcover := literalDirectedEdge_covers_target_cell right
    have hcell :
        (⟨ownerCell right.target right.boneClass.label,
          literalDirectedEdge_target_cell_mem right⟩ : BenzelCell (m + 5)) =
          cell := by
      apply Subtype.ext
      simp [cell, htarget, hlabel]
    simpa [hcell] using hcover
  have hleftMem := (mem_literalDirectedEdges_placement hstone tiling left hleft).1
  have hrightMem := (mem_literalDirectedEdges_placement hstone tiling right hright).1
  obtain ⟨placement, _, hunique⟩ := tiling.2 cell
  have hl := hunique left.placement ⟨hleftMem, hleftCover⟩
  have hr := hunique right.placement ⟨hrightMem, hrightCover⟩
  exact hl.trans hr.symm

theorem literalOutdegree_le_one
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) :
    literalOutdegree hstone tiling p ≤ 1 := by
  classical
  rw [literalOutdegree, Finset.card_le_one_iff]
  intro left right hleft hright
  have hleftEdge := (Finset.mem_filter.mp hleft)
  have hrightEdge := (Finset.mem_filter.mp hright)
  apply literalEdges_eq_of_placement_eq hstone tiling hleftEdge.1 hrightEdge.1
  apply edge_placements_eq_of_same_source hstone tiling
    hleftEdge.1 hrightEdge.1
  exact hleftEdge.2.trans hrightEdge.2.symm

theorem incoming_label_injective
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) :
    Set.InjOn (fun edge : LiteralDirectedEdge m => edge.boneClass.label)
      ((literalDirectedEdges hstone tiling).filter fun edge => edge.target = p) := by
  intro left hleft right hright hlabel
  have hleftEdge := Finset.mem_filter.mp hleft
  have hrightEdge := Finset.mem_filter.mp hright
  apply literalEdges_eq_of_placement_eq hstone tiling hleftEdge.1 hrightEdge.1
  apply edge_placements_eq_of_same_target_label hstone tiling
    hleftEdge.1 hrightEdge.1
  · exact hleftEdge.2.trans hrightEdge.2.symm
  · exact hlabel

theorem literalIndegree_le_three
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) :
    literalIndegree hstone tiling p ≤ 3 := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (s := (literalDirectedEdges hstone tiling).filter fun edge => edge.target = p)
    (t := (Finset.univ : Finset MicroLabel))
    (fun edge : LiteralDirectedEdge m => edge.boneClass.label)
    (by simp)
    (incoming_label_injective hstone tiling p)
  simpa [literalIndegree, microLabelFintype] using hcard

end BenzelProblem6Kernel

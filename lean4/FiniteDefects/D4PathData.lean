import FiniteDefects.D4AbstractDefect

/-! # Tiling-independent defect and three-path data -/

namespace FiniteDefects

def IsD4AbstractReversePath {m : ℕ} (label : MicroLabel) :
    SimplexPoint (m + 2) → SimplexPoint (m + 2) →
      List (D4LiteralDirectedEdge m) → Prop
  | terminal, core, [] => terminal = core
  | terminal, core, edge :: rest =>
      edge.target = terminal ∧ edge.boneClass.label = label ∧
        IsD4AbstractReversePath label edge.source core rest

theorem d4_map_reverse_path {m : ℕ} {tiling : D4LiteralTiling m}
    (label : MicroLabel) (terminal core : SimplexPoint (m + 2))
    (edges : List (D4GoodBonePlacement tiling))
    (hpath : IsD4ReversePath label terminal core edges) :
    IsD4AbstractReversePath label terminal core
      (edges.map D4GoodBonePlacement.edge) := by
  induction edges generalizing terminal with
  | nil => exact hpath
  | cons edge rest ih =>
      simp only [IsD4ReversePath] at hpath
      simp only [List.map_cons, IsD4AbstractReversePath]
      exact ⟨hpath.1, hpath.2.1, ih edge.source hpath.2.2⟩

structure D4DefectPathData (m : ℕ) where
  defect : D4DefectPlacement m
  paths : MicroLabel → List (D4LiteralDirectedEdge m)
  path_spec : ∀ label,
    IsD4AbstractReversePath label (d4BoundaryOwner m label)
      (defect.core label) (paths label)

noncomputable def d4ExtractedPathData {m : ℕ}
    (tiling : D4LiteralTiling m) : D4DefectPathData m where
  defect := d4TilingDefect tiling
  paths label :=
    (d4ReverseBoundaryPath tiling label).map D4GoodBonePlacement.edge
  path_spec label := by
    have hpath := d4_map_reverse_path label (d4BoundaryOwner m label)
      (d4DefectCore tiling label) (d4ReverseBoundaryPath tiling label)
      (d4ReverseBoundaryPath_spec tiling label)
    rw [d4TilingDefect_core tiling label]
    exact hpath

theorem IsD4AbstractReversePath.all_labels {m : ℕ}
    {label : MicroLabel} {terminal core : SimplexPoint (m + 2)}
    {edges : List (D4LiteralDirectedEdge m)}
    (hpath : IsD4AbstractReversePath label terminal core edges) :
    ∀ edge ∈ edges, edge.boneClass.label = label := by
  induction edges generalizing terminal with
  | nil => simp
  | cons first rest ih =>
      simp only [IsD4AbstractReversePath] at hpath
      intro edge hedge
      simp only [List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · exact hpath.2.1
      · exact ih hpath.2.2 edge hedge

end FiniteDefects

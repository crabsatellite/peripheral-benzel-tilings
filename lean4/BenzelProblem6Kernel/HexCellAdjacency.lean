import BenzelProblem6Kernel.HexCellDirectedEdgeIncidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Cell adjacency and connected literal placements

This is the discrete topology carrier for the component-boundary forest.
-/

namespace BenzelProblem6Kernel

def HexCellsAdjacent (left right : Cell) : Prop :=
  ∃ side : HexSide, neighboringCell left side = right

theorem hexCellsAdjacent_symm : Symmetric HexCellsAdjacent := by
  intro left right hadj
  obtain ⟨side, rfl⟩ := hadj
  exact ⟨oppositeHexSide side, neighboringCell_opposite left side⟩

theorem hexCellsAdjacent_irrefl : Irreflexive HexCellsAdjacent := by
  intro cell hadj
  obtain ⟨side, hside⟩ := hadj
  exact neighboringCell_ne cell side hside

def hexCellGraph : SimpleGraph Cell where
  Adj := HexCellsAdjacent
  symm := hexCellsAdjacent_symm
  loopless := hexCellsAdjacent_irrefl

theorem translateLocalCell_adjacent_side₀
    (base : Cell) (loc : LocalCell) :
    hexCellGraph.Adj (translateLocalCell base loc)
      (neighboringCell (translateLocalCell base loc) .side₀) :=
  ⟨.side₀, rfl⟩

theorem translateLocalCell_adjacent_side₄
    (base : Cell) (loc : LocalCell) :
    hexCellGraph.Adj (translateLocalCell base loc)
      (neighboringCell (translateLocalCell base loc) .side₄) :=
  ⟨.side₄, rfl⟩

theorem translateLocalCell_adjacent_side₅
    (base : Cell) (loc : LocalCell) :
    hexCellGraph.Adj (translateLocalCell base loc)
      (neighboringCell (translateLocalCell base loc) .side₅) :=
  ⟨.side₅, rfl⟩

theorem translated_c00_adjacent_c10 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c00)
      (translateLocalCell base c10) := by
  simpa [neighboringCell, translateLocalCell, c00, c10] using
    (translateLocalCell_adjacent_side₅ base c00)

theorem translated_c00_adjacent_c01 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c00)
      (translateLocalCell base c01) := by
  simpa [neighboringCell, translateLocalCell, c00, c01] using
    (translateLocalCell_adjacent_side₀ base c00)

theorem translated_c10_adjacent_c20 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c10)
      (translateLocalCell base c20) := by
  convert translateLocalCell_adjacent_side₅ base c10 using 1
  all_goals simp [neighboringCell, translateLocalCell, c10, c20]
  all_goals omega

theorem translated_c01_adjacent_c02 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c01)
      (translateLocalCell base c02) := by
  convert translateLocalCell_adjacent_side₀ base c01 using 1
  all_goals simp [neighboringCell, translateLocalCell, c01, c02]
  all_goals omega

theorem translated_c00_adjacent_c1m1 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c00)
      (translateLocalCell base c1m1) := by
  simpa [neighboringCell, translateLocalCell, c00, c1m1] using
    (translateLocalCell_adjacent_side₄ base c00)

theorem translated_c1m1_adjacent_c2m2 (base : Cell) :
    hexCellGraph.Adj (translateLocalCell base c1m1)
      (translateLocalCell base c2m2) := by
  convert translateLocalCell_adjacent_side₄ base c1m1 using 1
  all_goals simp [neighboringCell, translateLocalCell, c1m1, c2m2]
  all_goals omega

theorem reachable_of_mem_three {first second third left right : Cell}
    (hsecond : hexCellGraph.Reachable first second)
    (hthird : hexCellGraph.Reachable first third)
    (hleft : left ∈ [first, second, third])
    (hright : right ∈ [first, second, third]) :
    hexCellGraph.Reachable left right := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hleft hright
  rcases hleft with rfl | rfl | rfl
  all_goals rcases hright with rfl | rfl | rfl
  all_goals first
    | exact .rfl
    | exact hsecond
    | exact hthird
    | exact hsecond.symm
    | exact hsecond.symm.trans hthird
    | exact hthird.symm
    | exact hthird.symm.trans hsecond

theorem placement_cells_reachable {m : ℕ}
    (placement : LiteralPlacement m) {left right : Cell}
    (hleft : left ∈ placement.cells) (hright : right ∈ placement.cells) :
    hexCellGraph.Reachable left right := by
  rcases placement with ⟨⟨tile, base⟩, inside⟩
  cases tile
  case stone =>
    apply reachable_of_mem_three
      (translated_c00_adjacent_c10 base.1).reachable
      (translated_c00_adjacent_c01 base.1).reachable
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hleft
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hright
  case boneA =>
    apply reachable_of_mem_three
      (translated_c00_adjacent_c10 base.1).reachable
      ((translated_c00_adjacent_c10 base.1).reachable.trans
        (translated_c10_adjacent_c20 base.1).reachable)
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hleft
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hright
  case boneB =>
    apply reachable_of_mem_three
      (translated_c00_adjacent_c01 base.1).reachable
      ((translated_c00_adjacent_c01 base.1).reachable.trans
        (translated_c01_adjacent_c02 base.1).reachable)
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hleft
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hright
  case boneC =>
    apply reachable_of_mem_three
      (translated_c00_adjacent_c1m1 base.1).reachable
      ((translated_c00_adjacent_c1m1 base.1).reachable.trans
        (translated_c1m1_adjacent_c2m2 base.1).reachable)
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hleft
    · simpa [LiteralPlacement.cells, placementCellList, protoCells] using hright

end BenzelProblem6Kernel

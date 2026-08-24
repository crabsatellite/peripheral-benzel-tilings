import BenzelProblem6Kernel.LiteralPathModelEquiv
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path

/-!
# Bipartite incidence graph of tiling placements and periodic owners
-/

namespace BenzelProblem6Kernel

abbrev TilingPlacementNode {m : ℕ} (tiling : LiteralTiling m) :=
  {placement : LiteralPlacement m // placement ∈ tiling.1}

abbrev TilingIncidenceNode {m : ℕ} (tiling : LiteralTiling m) :=
  TilingPlacementNode tiling ⊕ SimplexPoint (m + 3)

noncomputable def coveringPlacementNode {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    TilingPlacementNode tiling :=
  ⟨(tiling.2 cell).choose, (tiling.2 cell).choose_spec.1.1⟩

theorem coveringPlacementNode_covers {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    PlacementCovers (coveringPlacementNode tiling cell).1 cell :=
  (tiling.2 cell).choose_spec.1.2

noncomputable def cellIncidencePair {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    TilingPlacementNode tiling × SimplexPoint (m + 3) :=
  (coveringPlacementNode tiling cell,
    chosenOwner (n := m + 5) (by omega) cell)

noncomputable def tilingIncidencePairs {m : ℕ}
    (tiling : LiteralTiling m) :
    Finset (TilingPlacementNode tiling × SimplexPoint (m + 3)) := by
  classical
  exact Finset.univ.image (cellIncidencePair tiling)

noncomputable def tilingIncidenceGraph {m : ℕ}
    (tiling : LiteralTiling m) : SimpleGraph (TilingIncidenceNode tiling) where
  Adj left right :=
    ∃ pair ∈ tilingIncidencePairs tiling,
      (left = Sum.inl pair.1 ∧ right = Sum.inr pair.2) ∨
      (left = Sum.inr pair.2 ∧ right = Sum.inl pair.1)
  symm := by
    intro left right hadj
    obtain ⟨pair, hpair, hforward | hbackward⟩ := hadj
    · exact ⟨pair, hpair, Or.inr ⟨hforward.2, hforward.1⟩⟩
    · exact ⟨pair, hpair, Or.inl ⟨hbackward.2, hbackward.1⟩⟩
  loopless := by
    intro node hadj
    obtain ⟨pair, _, hforward | hbackward⟩ := hadj
    · rw [hforward.1] at hforward
      cases hforward.2
    · rw [hbackward.1] at hbackward
      cases hbackward.2

theorem cellIncidencePair_mem {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    cellIncidencePair tiling cell ∈ tilingIncidencePairs tiling := by
  classical
  simp [tilingIncidencePairs]

theorem cell_tile_owner_adj {m : ℕ}
    (tiling : LiteralTiling m) (cell : BenzelCell (m + 5)) :
    (tilingIncidenceGraph tiling).Adj
      (Sum.inl (coveringPlacementNode tiling cell))
      (Sum.inr (chosenOwner (n := m + 5) (by omega) cell)) := by
  exact ⟨cellIncidencePair tiling cell, cellIncidencePair_mem tiling cell,
    Or.inl ⟨rfl, rfl⟩⟩

end BenzelProblem6Kernel

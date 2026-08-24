import BenzelProblem6Kernel.GoodTilingEdgeSet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Source and target degrees of the literal good-bone graph
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

noncomputable def literalOutdegree
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) : ℕ :=
  ((literalDirectedEdges hstone tiling).filter fun edge => edge.source = p).card

noncomputable def literalIndegree
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) (p : SimplexPoint (m + 3)) : ℕ :=
  ((literalDirectedEdges hstone tiling).filter fun edge => edge.target = p).card

theorem edge_source_filter_sum
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∑ p : SimplexPoint (m + 3), literalOutdegree hstone tiling p =
      (literalDirectedEdges hstone tiling).card := by
  classical
  calc
    (∑ p : SimplexPoint (m + 3), literalOutdegree hstone tiling p) =
        ∑ p : SimplexPoint (m + 3),
          ∑ edge ∈ literalDirectedEdges hstone tiling,
            if edge.source = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [literalOutdegree, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ edge ∈ literalDirectedEdges hstone tiling,
        ∑ p : SimplexPoint (m + 3), if edge.source = p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ edge ∈ literalDirectedEdges hstone tiling, 1 := by
        apply Finset.sum_congr rfl
        intro edge _
        simp
    _ = (literalDirectedEdges hstone tiling).card := by simp

theorem edge_target_filter_sum
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∑ p : SimplexPoint (m + 3), literalIndegree hstone tiling p =
      (literalDirectedEdges hstone tiling).card := by
  classical
  calc
    (∑ p : SimplexPoint (m + 3), literalIndegree hstone tiling p) =
        ∑ p : SimplexPoint (m + 3),
          ∑ edge ∈ literalDirectedEdges hstone tiling,
            if edge.target = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [literalIndegree, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ edge ∈ literalDirectedEdges hstone tiling,
        ∑ p : SimplexPoint (m + 3), if edge.target = p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ edge ∈ literalDirectedEdges hstone tiling, 1 := by
        apply Finset.sum_congr rfl
        intro edge _
        simp
    _ = (literalDirectedEdges hstone tiling).card := by simp

theorem total_literal_outdegree
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∑ p : SimplexPoint (m + 3), literalOutdegree hstone tiling p =
      3 * (m + 3) := by
  rw [edge_source_filter_sum, literalDirectedEdges_card]

theorem total_literal_indegree
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m) :
    ∑ p : SimplexPoint (m + 3), literalIndegree hstone tiling p =
      3 * (m + 3) := by
  rw [edge_target_filter_sum, literalDirectedEdges_card]

end BenzelProblem6Kernel

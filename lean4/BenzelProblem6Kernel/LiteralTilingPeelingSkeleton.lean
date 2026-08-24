import BenzelProblem6Kernel.ReducedPeripheralRootedBoundary
import BenzelProblem6Kernel.RightmostPeelingSkeleton

/-! # The canonical rightmost skeleton of every literal tiling -/

namespace BenzelProblem6Kernel

noncomputable def literalTilingRightmostSkeleton {m : ℕ}
    (tiling : LiteralTiling m) :
    RightmostPeelingSkeleton m
      (literalReducedPeripheralRootedBoundary m) tiling.1 :=
  buildRightmostPeelingSkeleton tiling
    (literalReducedPeripheralRootedBoundary m) tiling.1
    (fun _ h => h) (initialRightmostBoundaryCoefficientInvariant tiling)

noncomputable def literalTilingRightmostTerminal {m : ℕ}
    (tiling : LiteralTiling m) : RootedAlternatingBoundary :=
  (literalTilingRightmostSkeleton tiling).terminalRegion

noncomputable def literalTilingGeometricPeeling_of_terminal
    {m : ℕ} (tiling : LiteralTiling m)
    (terminal_empty : InvolutiveWordEquivalent
      (labeledEdgeWord (literalTilingRightmostTerminal tiling).edges) []) :
    LiteralTilingGeometricPeeling tiling where
  peeling := (literalTilingRightmostSkeleton tiling).toGeometricPeeling
    terminal_empty
  placements_exact := by
    rw [(literalTilingRightmostSkeleton tiling).toGeometricPeeling_placements
      terminal_empty]
    exact (literalTilingRightmostSkeleton tiling).removedPlacements_perm

theorem rightStoneCount_of_rightmostTerminal {m : ℕ}
    (tiling : LiteralTiling m)
    (terminal_empty : InvolutiveWordEquivalent
      (labeledEdgeWord (literalTilingRightmostTerminal tiling).edges) []) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  exact rightStoneCount_of_geometricPeeling tiling
    (literalTilingGeometricPeeling_of_terminal tiling terminal_empty)

theorem terminalWord_empty_of_backtrackReduction
    (edges : List LabeledHexEdge)
    (hreduced : reduceGeometricBacktracks edges = []) :
    InvolutiveWordEquivalent (labeledEdgeWord edges) [] := by
  have hnormalize := reduceGeometricBacktracks_word_equivalent edges
  rw [hreduced] at hnormalize
  exact hnormalize

theorem rightStoneCount_of_rightmostBacktrackReduction {m : ℕ}
    (tiling : LiteralTiling m)
    (hreduced : reduceGeometricBacktracks
      (literalTilingRightmostTerminal tiling).edges = []) :
    rightStoneCount tiling = m * (m + 3) / 2 := by
  exact rightStoneCount_of_rightmostTerminal tiling
    (terminalWord_empty_of_backtrackReduction _ hreduced)

end BenzelProblem6Kernel

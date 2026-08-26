import D4KernelOnly.GeneralRightmostPeeling

/-! # Premise-free rightmost peeling for class-zero benzels -/

namespace FiniteDefects

open BenzelProblem6Kernel

theorem czInitialRightmostBoundaryCoefficientInvariant
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    RightmostBoundaryCoefficientInvariant
      (classZeroLiteralBoundaryWalk s r)
      (offsetShadowPlacementFinset tiling) := by
  intro cell
  exact (directedEdgeCoefficient_classZeroBoundary_sideFive
      s r hs hr cell).trans
    ((offsetShadowPlacementFinsetBoundaries_eq_cellBoundaries tiling
      (cellBoundaryEdgeAt cell .side₅)).symm)

theorem czReducedBoundaryCoefficientInvariant
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    RightmostBoundaryCoefficientInvariant
      (czReducedBoundaryWalk s r)
      (offsetShadowPlacementFinset tiling) := by
  intro cell
  exact ((reduceGeometricBacktracks_same_chain
    (classZeroLiteralBoundaryWalk s r))
      (cellBoundaryEdgeAt cell .side₅)).symm.trans
        (czInitialRightmostBoundaryCoefficientInvariant hs hr tiling cell)

noncomputable def czReducedRightmostSkeleton
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) :
    RightmostPeelingSkeleton (2 * s + r - 2)
      (czReducedRootedBoundary s r)
      (offsetShadowPlacementFinset tiling) :=
  buildOffsetRightmostPeelingSkeleton tiling
    (czReducedRootedBoundary s r) (offsetShadowPlacementFinset tiling)
    (fun _ h => h) (czReducedBoundaryCoefficientInvariant hs hr tiling)

noncomputable def czReducedRightmostTerminal
    {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (tiling : CZLiteralTiling s r) : RootedAlternatingBoundary :=
  (czReducedRightmostSkeleton hs hr tiling).terminalRegion

end FiniteDefects

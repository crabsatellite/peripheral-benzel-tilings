import D4KernelOnly.GeneralClassMinusOneNodup
import D4KernelOnly.D4ReducedPeelingBoundary

/-! # Backtrack-reduced class-minus-one boundary and peeling skeleton -/

namespace FiniteDefects

open BenzelProblem6Kernel

def cmoReducedBoundaryWalk (s r : ℕ) : List LabeledHexEdge :=
  reduceGeometricBacktracks (classMinusOneLiteralBoundaryWalk s r)

theorem cmoReducedBoundary_continuous (s r : ℕ) :
    ContinuousLabeledEdgePath (classMinusOneLiteralBoundaryRoot s r)
      (cmoReducedBoundaryWalk s r)
      (classMinusOneLiteralBoundaryRoot s r) :=
  reduceGeometricBacktracks_continuous
    (classMinusOneLiteralBoundary_continuous s r)

theorem cmoReducedBoundary_edges_alternate (s r : ℕ) :
    ∀ edge ∈ cmoReducedBoundaryWalk s r,
      AlternatesHexVertexClass edge := by
  intro edge hedge
  exact classMinusOneLiteralBoundaryWalk_edges_alternate s r edge
    ((reduceGeometricBacktracks_sublist _).subset hedge)

theorem cmoReducedBoundary_nodup
    (s r : ℕ) (hs : 1 ≤ s) :
    (cmoReducedBoundaryWalk s r).Nodup :=
  (classMinusOneLiteralBoundaryWalk_nodup s r hs).sublist
    (reduceGeometricBacktracks_sublist _)

def cmoReducedRootedBoundary (s r : ℕ) : RootedAlternatingBoundary where
  edges := cmoReducedBoundaryWalk s r
  root := classMinusOneLiteralBoundaryRoot s r
  continuous := cmoReducedBoundary_continuous s r
  root_classZero := classMinusOneLiteralBoundaryRoot_classZero s r
  alternates := cmoReducedBoundary_edges_alternate s r

theorem cmoReducedBoundaryCoefficientInvariant
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RightmostBoundaryCoefficientInvariant
      (cmoReducedBoundaryWalk s r)
      (offsetShadowPlacementFinset tiling) := by
  intro cell
  exact ((reduceGeometricBacktracks_same_chain
    (classMinusOneLiteralBoundaryWalk s r))
      (cellBoundaryEdgeAt cell .side₅)).symm.trans
        (cmoInitialRightmostBoundaryCoefficientInvariant hs tiling cell)

noncomputable def cmoReducedRightmostSkeleton
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RightmostPeelingSkeleton (2 * s + r - 1)
      (cmoReducedRootedBoundary s r)
      (offsetShadowPlacementFinset tiling) :=
  buildCMORightmostPeelingSkeleton tiling
    (cmoReducedRootedBoundary s r)
    (offsetShadowPlacementFinset tiling)
    (fun _ h => h) (cmoReducedBoundaryCoefficientInvariant hs tiling)

noncomputable def cmoReducedRightmostTerminal
    {s r : ℕ} (hs : 1 ≤ s) (tiling : CMOLiteralTiling s r) :
    RootedAlternatingBoundary :=
  (cmoReducedRightmostSkeleton hs tiling).terminalRegion

end FiniteDefects

import D4KernelOnly.D4BoundaryAlternation
import D4KernelOnly.D4PlacementBoundaryCancellation
import D4KernelOnly.D4ShadowSubfamily
import BenzelProblem6Kernel.RootedAlternatingBoundary

/-! # The rooted d=4 boundary and its initial peeling invariant -/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4LiteralRootedBoundary (m : ℕ) :
    BenzelProblem6Kernel.RootedAlternatingBoundary where
  edges := d4LiteralBoundaryWalk m
  root := d4LiteralBoundaryRoot m
  continuous := d4LiteralBoundary_continuous m
  root_classZero := d4LiteralBoundaryRoot_classZero m
  alternates := d4LiteralBoundaryWalk_edges_alternate m

theorem d4ShadowPlacementFinset_toList_perm {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Perm (d4ShadowPlacementFinset tiling).toList
      (d4ShadowPlacementList tiling) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (Finset.nodup_toList _) (by
      unfold d4ShadowPlacementList
      exact (Finset.nodup_toList tiling.1).map
        d4ShadowPlacement_injective)).mpr
  intro placement
  rw [Finset.mem_toList]
  rw [mem_d4ShadowPlacementFinset_iff]
  simp only [d4ShadowPlacementList, List.mem_map, Finset.mem_toList]

theorem d4ShadowPlacementFinset_boundary_perm {m : ℕ}
    (tiling : D4LiteralTiling m) :
    List.Perm
      (literalPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList)
      (literalPlacementBoundaryList (d4ShadowPlacementList tiling)) := by
  exact (d4ShadowPlacementFinset_toList_perm tiling).map
    literalPlacementBoundary |>.flatten

theorem d4ShadowPlacementFinsetBoundaries_eq_d4CellBoundaries {m : ℕ}
    (tiling : D4LiteralTiling m) :
    SameOrientedBoundaryChain
      (literalPlacementBoundaryList
        (d4ShadowPlacementFinset tiling).toList)
      (orientedCellBoundaryList (d4CellValueList m)) :=
  (SameOrientedBoundaryChain.perm
    (d4ShadowPlacementFinset_boundary_perm tiling)).trans
      (d4ShadowPlacementBoundaries_eq_d4CellBoundaries tiling)

theorem d4InitialRightmostBoundaryCoefficientInvariant {m : ℕ}
    (tiling : D4LiteralTiling m) :
    RightmostBoundaryCoefficientInvariant
      (d4LiteralBoundaryWalk m) (d4ShadowPlacementFinset tiling) := by
  intro cell
  exact (directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive m cell).trans
    ((d4ShadowPlacementFinsetBoundaries_eq_d4CellBoundaries tiling
      (cellBoundaryEdgeAt cell .side₅)).symm)

end FiniteDefects

import BenzelProblem6Kernel.ExposedPlacementEdgeBoneC0
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneC1
import BenzelProblem6Kernel.ExposedPlacementEdgeBoneC2

namespace BenzelProblem6Kernel

theorem exposed_side₅_mem_boneCBoundary
    (base cell : Cell)
    (hcell : cell ∈
      (protoCells .boneC).map (translateLocalCell base))
    (hexposed : neighboringCell cell .side₅ ∉
      (protoCells .boneC).map (translateLocalCell base)) :
    cellBoundaryEdgeAt cell .side₅ ∈
      literalPrototypeBoundary .boneC base := by
  simp [protoCells] at hcell
  rcases hcell with rfl | rfl | rfl
  · exact exposed_side₅_mem_boneC_c00 base
  · exact exposed_side₅_mem_boneC_c1m1 base
  · exact exposed_side₅_mem_boneC_c2m2 base

end BenzelProblem6Kernel

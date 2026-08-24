import BenzelProblem6Kernel.DirectedY

/-!
# Global degree-count consequence
-/

namespace BenzelProblem6Kernel

theorem one_sink_type_of_edge_count
    (vertices edges fullSinks cornerSinks : ℤ)
    (hedges : edges = vertices - 1)
    (houtgoing : edges = vertices - fullSinks - cornerSinks) :
    fullSinks + cornerSinks = 1 := by
  omega

end BenzelProblem6Kernel

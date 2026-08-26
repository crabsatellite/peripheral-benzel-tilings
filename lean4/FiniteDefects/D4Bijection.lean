import FiniteDefects.D4BijectionInterface
import FiniteDefects.D4LeftInverse

/-! # Kernel producer for the literal d=4 defect-path equivalence -/

namespace FiniteDefects

theorem d4LiteralBijectionKernel : D4LiteralBijectionEvidence where
  literal_equiv m := ⟨d4LiteralTilingEquivPathData m⟩
  zero_one_disjoint := d4_paths_zero_one_disjoint
  one_two_disjoint := d4_paths_one_two_disjoint
  two_zero_disjoint := d4_paths_two_zero_disjoint

end FiniteDefects

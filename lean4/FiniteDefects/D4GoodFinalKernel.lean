import FiniteDefects.D4GoodFinalInterface

/-! # Kernel producer for the exact all-coefficient d=4 series -/

namespace FiniteDefects

theorem d4GeneratingFunctionKernel : D4GeneratingFunctionEvidence where
  small_root_constant := constantCoeff_ternarySeries
  small_root_equation := ternarySeries_equation
  small_root_unique := ternarySeries_unique
  exact_generating_function := d4Good_generating_function

end FiniteDefects

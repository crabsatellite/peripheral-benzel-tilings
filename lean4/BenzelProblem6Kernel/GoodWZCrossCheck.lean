import BenzelProblem6Kernel.ChiralityGeneratingSeries
import BenzelProblem6Kernel.GoodCoefficientExtraction
import BenzelProblem6Kernel.PathModelClosedForm

/-!
# Independent WZ cross-check of the evaluated total Good series

This theorem is deliberately a redundancy check.  It identifies the total
evaluated Good series with the already kernel-certified path-model series by
their exact coefficients; it does not replace the still-required specialized
multivariate Good producer for the separate positive and negative series.
-/

namespace BenzelProblem6Kernel

open PowerSeries

theorem pathModelGeneratingSeries_eq_totalGood :
    pathModelGeneratingSeries = totalGoodGeneratingSeries := by
  apply PowerSeries.ext
  intro degree
  rw [coeff_pathModelGeneratingSeries,
    coeff_totalGoodGeneratingSeries_ballot]
  exact pathModelClosedFormTarget_proved degree

end BenzelProblem6Kernel

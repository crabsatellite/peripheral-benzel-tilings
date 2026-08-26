# Combined paper-to-Lean map

The canonical manuscript is `peripheral_benzel_tilings.tex`, which imports
`d4_extension.tex`.  Exact machine-checked maps are located at:

- `lean4/BenzelProblem6Kernel/ManuscriptFormulaMap.lean` for the 20 Problem 6
  labels and 43 exact endpoints;
- `lean4/D4KernelOnly/D4KernelTheoremMap.lean` for the general finite-defect
  theorem and the 32 first-defect labels.

| Paper result | Exact Lean endpoint |
|---|---|
| Propp Problem 6 closed form | `BenzelProblem6Kernel.manuscript_main_theorem_proved` |
| Literal Problem 6 tiling/path equivalence | `BenzelProblem6Kernel.manuscript_prop_Y_bijection` |
| General finite-defect theorem | `FiniteDefects.generalFiniteDefectKernelOnly` |
| General-to-`d=4` literal carrier | `FiniteDefects.offsetD4LiteralTilingEquiv` |
| `d=4` one-defect theorem | `FiniteDefects.d4OneDefectKernelOnly` |
| Literal defect/path equivalence | `FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly` |
| Five defect classes and independent arms | `FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly` |
| Exact cyclic ballot sum | `FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly` |
| Three Lagrange--Good components | `FiniteDefects.d4Good_A0_component_kernelOnly`, `FiniteDefects.d4Good_C_component_kernelOnly`, `FiniteDefects.d4Good_H_component_kernelOnly` |
| First-defect generating function | `FiniteDefects.d4Good_generating_function_literal_kernelOnly` |
| Packaged first-defect endpoint | `FiniteDefects.d4GeneratingFunctionKernelOnly` |

`lean4/PeripheralBenzelPublication.lean` imports both theorem maps.  The final
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

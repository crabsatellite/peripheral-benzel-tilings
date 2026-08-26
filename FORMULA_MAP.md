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

The first-defect part is additionally checked label by label:

| Manuscript label | Audited Lean endpoint(s) |
|---|---|
| `d4:thm:main` | `FiniteDefects.d4GeneratingFunctionKernelOnly` |
| `d4:eq:main-formula` | `FiniteDefects.d4Good_generating_function_literal_kernelOnly` |
| `d4:eq:benzel` | `FiniteDefects.inBenzel` |
| `d4:eq:uvw` | `FiniteDefects.ownerQ`, `FiniteDefects.ownerR` |
| `d4:eq:difference-table` | `FiniteDefects.owner_cell_zero_differences`, `FiniteDefects.owner_cell_one_differences`, `FiniteDefects.owner_cell_two_differences` |
| `d4:lem:owner-domain` | `FiniteDefects.ownerDomainHierarchyKernel` |
| `d4:eq:potential` | `FiniteDefects.ownerPotential` |
| `d4:eq:energy-table` | `FiniteDefects.stone_energy_by_residue`, `FiniteDefects.boneA_energy_by_residue`, `FiniteDefects.boneB_energy_by_residue`, `FiniteDefects.boneC_energy_by_residue` |
| `d4:thm:defects` | `FiniteDefects.generalFiniteDefectKernelOnly` |
| `d4:eq:region-energy` | `FiniteDefects.d3k_exact_energy_count_identity`, `FiniteDefects.d3k1_exact_energy_count_identity` |
| `d4:eq:bone-counts` | `FiniteDefects.generalBoneCountKernelOnly` |
| `d4:eq:defect-cores` | `FiniteDefects.D4DefectParameter.core` |
| `d4:lem:three-paths` | `FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly`, `FiniteDefects.d4TerminalSupportGraph_isTree` |
| `d4:eq:path-monotonicity` | `FiniteDefects.d4AbstractEdge_zero_mono`, `FiniteDefects.d4AbstractEdge_one_mono`, `FiniteDefects.d4AbstractEdge_two_mono` |
| `d4:eq:core-separation` | `FiniteDefects.d4_core_zero_w_gt_one`, `FiniteDefects.d4_core_one_u_gt_two`, `FiniteDefects.d4_core_two_v_gt_zero` |
| `d4:prop:bijection` | `FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly` |
| `d4:eq:R` | `FiniteDefects.d4R` |
| `d4:eq:R-coeff` | `FiniteDefects.d4R_coefficient_formula` |
| `d4:thm:d4-sum` | `FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly` |
| `d4:eq:A` | `FiniteDefects.d4A` |
| `d4:eq:C` | `FiniteDefects.d4C` |
| `d4:eq:H` | `FiniteDefects.d4H` |
| `d4:eq:ballot-sum` | `FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly` |
| `d4:eq:phi` | `FiniteDefects.goodPhi` |
| `d4:eq:determinant` | `FiniteDefects.goodDeterminant` |
| `d4:eq:good-expansion` | `FiniteDefects.goodExpansion_functional` |
| `d4:eq:q` | `FiniteDefects.goodQ`, `FiniteDefects.goodDiagonal_goodW` |
| `d4:eq:diag-delta` | `FiniteDefects.goodDiagonal_goodDeterminant` |
| `d4:eq:A-good` | `FiniteDefects.d4A0_Good_equation` |
| `d4:eq:C-good` | `FiniteDefects.d4C_Good_equation` |
| `d4:eq:H-good` | `FiniteDefects.d4H_Good_equation` |
| `d4:eq:three-components` | `FiniteDefects.d4Good_A0_component_kernelOnly`, `FiniteDefects.d4Good_C_component_kernelOnly`, `FiniteDefects.d4Good_H_component_kernelOnly` |

`lean4/PeripheralBenzelPublication.lean` imports both theorem maps.  The final
audit also checks every endpoint in the table above and reports only
`propext`, `Classical.choice`, and `Quot.sound`.

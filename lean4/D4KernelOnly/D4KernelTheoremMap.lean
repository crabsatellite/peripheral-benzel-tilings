import D4KernelOnly.D4KernelOnlyFinalAudit

/-!
# Fail-closed paper-to-Lean map for the d=4 closure

Each `paper-label` line is consumed by `verify_all.py`.  Label order, label
identity, and every declaration named before the next label are audited.  A
renamed, missing, or silently unmapped manuscript claim therefore fails the
release check.
-/

-- paper-label: d4:thm:main
#check FiniteDefects.d4GeneratingFunctionKernelOnly

-- paper-label: d4:eq:main-formula
#check FiniteDefects.d4Good_generating_function_literal_kernelOnly

-- paper-label: d4:eq:benzel
#check FiniteDefects.inBenzel

-- paper-label: d4:eq:uvw
#check FiniteDefects.ownerQ
#check FiniteDefects.ownerR

-- paper-label: d4:eq:difference-table
#check FiniteDefects.owner_cell_zero_differences
#check FiniteDefects.owner_cell_one_differences
#check FiniteDefects.owner_cell_two_differences

-- paper-label: d4:lem:owner-domain
#check FiniteDefects.ownerDomainHierarchyKernel

-- paper-label: d4:eq:potential
#check FiniteDefects.ownerPotential

-- paper-label: d4:eq:energy-table
#check FiniteDefects.stone_energy_by_residue
#check FiniteDefects.boneA_energy_by_residue
#check FiniteDefects.boneB_energy_by_residue
#check FiniteDefects.boneC_energy_by_residue

-- paper-label: d4:thm:defects
#check FiniteDefects.generalFiniteDefectKernelOnly

-- paper-label: d4:eq:region-energy
#check FiniteDefects.d3k_exact_energy_count_identity
#check FiniteDefects.d3k1_exact_energy_count_identity

-- paper-label: d4:eq:bone-counts
#check FiniteDefects.generalBoneCountKernelOnly

-- paper-label: d4:eq:defect-cores
#check FiniteDefects.D4DefectParameter.core

-- paper-label: d4:lem:three-paths
#check FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly
#check FiniteDefects.d4TerminalSupportGraph_isTree

-- paper-label: d4:eq:path-monotonicity
#check FiniteDefects.d4AbstractEdge_zero_mono
#check FiniteDefects.d4AbstractEdge_one_mono
#check FiniteDefects.d4AbstractEdge_two_mono

-- paper-label: d4:eq:core-separation
#check FiniteDefects.d4_core_zero_w_gt_one
#check FiniteDefects.d4_core_one_u_gt_two
#check FiniteDefects.d4_core_two_v_gt_zero

-- paper-label: d4:prop:bijection
#check FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly

-- paper-label: d4:eq:R
#check FiniteDefects.d4R

-- paper-label: d4:eq:R-coeff
#check FiniteDefects.d4R_coefficient_formula

-- paper-label: d4:thm:d4-sum
#check FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly

-- paper-label: d4:eq:A
#check FiniteDefects.d4A

-- paper-label: d4:eq:C
#check FiniteDefects.d4C

-- paper-label: d4:eq:H
#check FiniteDefects.d4H

-- paper-label: d4:eq:ballot-sum
#check FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly

-- paper-label: d4:eq:phi
#check FiniteDefects.goodPhi

-- paper-label: d4:eq:determinant
#check FiniteDefects.goodDeterminant

-- paper-label: d4:eq:good-expansion
#check FiniteDefects.goodExpansion_functional

-- paper-label: d4:eq:q
#check FiniteDefects.goodQ
#check FiniteDefects.goodDiagonal_goodW

-- paper-label: d4:eq:diag-delta
#check FiniteDefects.goodDiagonal_goodDeterminant

-- paper-label: d4:eq:A-good
#check FiniteDefects.d4A0_Good_equation

-- paper-label: d4:eq:C-good
#check FiniteDefects.d4C_Good_equation

-- paper-label: d4:eq:H-good
#check FiniteDefects.d4H_Good_equation

-- paper-label: d4:eq:three-components
#check FiniteDefects.d4Good_A0_component_kernelOnly
#check FiniteDefects.d4Good_C_component_kernelOnly
#check FiniteDefects.d4Good_H_component_kernelOnly

namespace FiniteDefects

noncomputable section

/-!
The declarations below are exact type bridges, rather than existence-only
`#check` entries.  They fail to elaborate if a paper endpoint is weakened,
reindexed, or moved to a different carrier.
-/

example : OwnerDomainHierarchyEvidence := ownerDomainHierarchyKernel

example : GeneralBoneCountStatement := generalBoneCountKernelOnly

example : GeneralFiniteDefectStatement := generalFiniteDefectKernelOnly

example (m : ℕ) :
    OffsetLiteralTiling (m + 2) 4 ≃ D4LiteralTiling m :=
  offsetD4LiteralTilingEquiv m

example : D4OneDefectStatement := d4OneDefectKernelOnly

example (m : ℕ) :
    D4LiteralTiling m ≃ D4DefectPathData m :=
  d4LiteralTilingEquivPathData_kernelOnly m

example (m : ℕ) :
    D4LiteralTiling m ≃ Σ defect : D4DefectPlacement m,
      D4ArmTriple m defect :=
  d4LiteralTilingEquivSigmaArmTriple_kernelOnly m

example (m : ℕ) :
    d4LiteralTilingCountKernelOnly m = d4A m + d4C m + 3 * d4H m :=
  d4LiteralTilingCount_ballot_formula_kernelOnly m

example :
    d4LiteralTilingSeriesKernelOnly =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹ :=
  d4Good_generating_function_literal_kernelOnly

end

end FiniteDefects

import D4KernelOnly.D4KernelOnlyFinalAudit

/-! # Machine-checked paper-to-Lean map for the d=4 closure -/

#check FiniteDefects.inBenzel
#check FiniteDefects.ownerCell
#check FiniteDefects.ownerDomainHierarchyKernel
#check FiniteDefects.protoCells
#check FiniteDefects.allowedStep
#check FiniteDefects.D4DefectParameter.core
#check FiniteDefects.d4LiteralBoundaryWalk_labels
#check FiniteDefects.d4LiteralBoundary_continuous
#check FiniteDefects.directedEdgeCoefficient_d4LiteralBoundaryWalk_sideFive
#check FiniteDefects.directedEdgeCoefficient_d4LiteralBoundaryWalk_allSides
#check FiniteDefects.d4PerimeterEdges_perm_reduced
#check FiniteDefects.d4TilingComplexDirectedEdges_reverse_mem
#check FiniteDefects.d4TerminalSupportGraph_isTree
#check FiniteDefects.d4ReducedRightmostTerminal_word_empty
#check FiniteDefects.d4LiteralBoundaryFactorizationStatement_proved
#check FiniteDefects.d4ConwayLagariasStatement_proved
#check FiniteDefects.d4OneDefectKernelOnly
#check FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly
#check FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly
#check FiniteDefects.d4LiteralTilingCountKernelOnly
#check FiniteDefects.d4SpecializedTilingCount_eq_literal
#check FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly
#check FiniteDefects.d4Good_A0_component_kernelOnly
#check FiniteDefects.d4Good_C_component_kernelOnly
#check FiniteDefects.d4Good_H_component_kernelOnly
#check FiniteDefects.d4GoodKernelDelta_eq
#check FiniteDefects.goodExpansion_functional
#check FiniteDefects.goodDiagonal_mul
#check FiniteDefects.goodDiagonal_goodExpansion
#check FiniteDefects.fpsCompose_assoc
#check FiniteDefects.d4LiteralTilingSeriesKernelOnly
#check FiniteDefects.d4TilingSeriesKernelOnly_eq_literal
#check FiniteDefects.d4Good_generating_function_literal_kernelOnly
#check FiniteDefects.d4GeneratingFunctionKernelOnly
#check FiniteDefects.GeneralBoneCountStatement
#check FiniteDefects.cz_bone_count_kernelOnly
#check FiniteDefects.cmo_bone_count_kernelOnly
#check FiniteDefects.generalBoneCountKernelOnly
#check FiniteDefects.d3k_exact_energy_count_identity
#check FiniteDefects.d3k1_exact_energy_count_identity
#check FiniteDefects.GeneralFiniteDefectStatement
#check FiniteDefects.generalFiniteDefectKernelOnly

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

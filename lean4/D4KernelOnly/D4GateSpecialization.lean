import D4KernelOnly.D4OffsetCarrierBridge
import FiniteDefects.D4GoodFinalKernel

/-!
# Direct premise-free publication aliases for the d=4 downstream chain

The public package supplies the Conway--Lagarias specialization as a proved
theorem before elaborating the historical downstream argument.  Consequently
the publication aliases below are direct and contain no reference gate or
proof-term cloning step.
-/

namespace FiniteDefects

noncomputable def d4LiteralTilingEquivPathData_kernelOnly (m : ℕ) :
    D4LiteralTiling m ≃ D4DefectPathData m :=
  d4LiteralTilingEquivPathData m

noncomputable def d4LiteralTilingEquivSigmaArmTriple_kernelOnly (m : ℕ) :
    D4LiteralTiling m ≃ Σ defect : D4DefectPlacement m,
      D4ArmTriple m defect :=
  d4LiteralTilingEquivSigmaArmTriple m

theorem d4TilingCount_ballot_formula_kernelOnly (m : ℕ) :
    d4TilingCount m = d4A m + d4C m + 3 * d4H m :=
  d4TilingCount_ballot_formula m

theorem d4Good_A0_component_kernelOnly : d4A0Series = d4A0Closed :=
  d4Good_A0_component

theorem d4Good_C_component_kernelOnly : d4CSeries = d4CClosed :=
  d4Good_C_component

theorem d4Good_H_component_kernelOnly : d4HSeries = d4HClosed :=
  d4Good_H_component

noncomputable def d4TilingSeriesKernelOnly : PowerSeries ℚ :=
  d4TilingSeries

theorem d4Good_generating_function_kernelOnly :
    d4TilingSeriesKernelOnly =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹ := by
  exact d4Good_generating_function

theorem d4OneDefectKernelOnly : D4OneDefectStatement :=
  d4OneDefect_from_generalFiniteDefect

noncomputable def d4LiteralTilingCountKernelOnly (m : ℕ) : ℕ :=
  @Fintype.card (D4LiteralTiling m) (Fintype.ofFinite (D4LiteralTiling m))

theorem d4SpecializedTilingCount_eq_literal (m : ℕ) :
    d4TilingCount m = d4LiteralTilingCountKernelOnly m := by
  unfold d4TilingCount d4LiteralTilingCountKernelOnly
  exact @Fintype.card_congr _ _
    (d4LiteralTilingCountingFintype m)
    (Fintype.ofFinite (D4LiteralTiling m)) (Equiv.refl _)

theorem d4LiteralTilingCount_ballot_formula_kernelOnly (m : ℕ) :
    d4LiteralTilingCountKernelOnly m = d4A m + d4C m + 3 * d4H m := by
  rw [← d4SpecializedTilingCount_eq_literal]
  exact d4TilingCount_ballot_formula_kernelOnly m

noncomputable def d4LiteralTilingSeriesKernelOnly : PowerSeries ℚ :=
  PowerSeries.mk fun m => (d4LiteralTilingCountKernelOnly m : ℚ)

theorem d4TilingSeriesKernelOnly_eq_literal :
    d4TilingSeriesKernelOnly = d4LiteralTilingSeriesKernelOnly := by
  ext m
  unfold d4TilingSeriesKernelOnly d4TilingSeries
  simp only [d4LiteralTilingSeriesKernelOnly, PowerSeries.coeff_mk]
  exact_mod_cast d4SpecializedTilingCount_eq_literal m

theorem d4Good_generating_function_literal_kernelOnly :
    d4LiteralTilingSeriesKernelOnly =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹ := by
  rw [← d4TilingSeriesKernelOnly_eq_literal]
  exact d4Good_generating_function_kernelOnly

structure D4GeneratingFunctionKernelOnlyEvidence : Prop where
  small_root_constant : PowerSeries.constantCoeff ℚ ternarySeries = 1
  small_root_equation : ternarySeries = 1 + PowerSeries.X * ternarySeries ^ 3
  small_root_unique : ∀ T : PowerSeries ℚ,
    PowerSeries.constantCoeff ℚ T = 1 →
    T = 1 + PowerSeries.X * T ^ 3 → T = ternarySeries
  exact_generating_function :
    d4LiteralTilingSeriesKernelOnly =
      ternarySeries ^ 3 *
        (9 - 6 * ternarySeries + 27 * ternarySeries ^ 2 -
          35 * ternarySeries ^ 3 + 11 * ternarySeries ^ 4 +
          2 * ternarySeries ^ 5 - ternarySeries ^ 6) *
        d4GoodDenominator⁻¹

theorem d4GeneratingFunctionKernelOnly :
    D4GeneratingFunctionKernelOnlyEvidence where
  small_root_constant := constantCoeff_ternarySeries
  small_root_equation := ternarySeries_equation
  small_root_unique := ternarySeries_unique
  exact_generating_function := d4Good_generating_function_literal_kernelOnly

end FiniteDefects

#check FiniteDefects.d4GeneratingFunctionKernelOnly
#check FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly
#check FiniteDefects.d4LiteralTilingEquivSigmaArmTriple_kernelOnly
#check FiniteDefects.d4TilingCount_ballot_formula_kernelOnly

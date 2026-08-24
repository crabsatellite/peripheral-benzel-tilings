import BenzelProblem6Kernel.KernelOnlyClosure
import BenzelProblem6Kernel.ArmPrefixBounds
import BenzelProblem6Kernel.GoodResidueSpecialization
import BenzelProblem6Kernel.GoodWZCrossCheck
import BenzelProblem6Kernel.LiteralDirectedEdge
import BenzelProblem6Kernel.SpecializedGoodConstantTerm

/-!
# Exact endpoints for the numbered manuscript statements

The declarations in this file expose the mathematical statements printed in
`benzel_problem6.tex`.  A manuscript label may have several endpoints when the
printed statement has several displayed cases.  `ManuscriptFormulaMap.lean`
is the machine-readable label-to-endpoint map.
-/

namespace BenzelProblem6Kernel

open PowerSeries

/-! ## Theorem 1.1 and Equation (1) -/

theorem manuscript_thm_main {n : ℕ} (hn : 5 ≤ n) :
    (type103TilingCount n : ℚ) =
      ((3 * n + 3 : ℕ) : ℚ) * factorialQ (3 * n - 7) /
        (factorialQ (n - 5) * factorialQ (2 * n - 1)) :=
  manuscript_main_theorem_proved hn

theorem manuscript_eq_ballot_form (m : ℕ) :
    (2 * ((3 * m + 8).choose m : ℚ) - choosePred (3 * m + 8) m) =
      (3 * (m + 6) : ℚ) / (2 * m + 9) * (3 * m + 8).choose m :=
  ballot_form_eq_closed_form m

/-! ## Lemma 2.1 -/

theorem manuscript_lem_tile_counts {n : ℕ} (hn : 5 ≤ n)
    (tiling : LiteralTiling (n - 5)) :
    rightStoneCount tiling = (n - 5) * (n - 2) / 2 ∧
      boneCount tiling = 3 * (n - 2) := by
  have hstone := rightStoneCount_proved tiling
  have hbone := boneCount_of_conwayLagarias
    conwayLagariasStoneCountTarget_proved (n - 5) tiling
  have hshift : n - 5 + 3 = n - 2 := by omega
  constructor
  · simpa [hshift] using hstone
  · simpa [hshift] using hbone

/-! ## Equation (2) and Lemma 3.1 -/

theorem manuscript_eq_owner_coordinates {t : ℕ} (p : SimplexPoint t) :
    (p.u : ℚ) =
        (((t : ℕ) : ℚ) - (ownerQ p : ℚ) + (ownerR p : ℚ)) / 3 ∧
      (p.v : ℚ) =
        (((t : ℕ) : ℚ) - (ownerQ p : ℚ) - 2 * (ownerR p : ℚ)) / 3 ∧
      (p.w : ℚ) =
        (((t : ℕ) : ℚ) + 2 * (ownerQ p : ℚ) + (ownerR p : ℚ)) / 3 := by
  have hu := recover_u_numerator p
  have hv := recover_v_numerator p
  have hw := recover_w_numerator p
  constructor
  · apply (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).2
    have huQ : (3 : ℚ) * (p.u : ℚ) =
        ((t : ℕ) : ℚ) - (ownerQ p : ℚ) + (ownerR p : ℚ) := by
      exact_mod_cast hu.symm
    nlinarith
  constructor
  · apply (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).2
    have hvQ : (3 : ℚ) * (p.v : ℚ) =
        ((t : ℕ) : ℚ) - (ownerQ p : ℚ) - 2 * (ownerR p : ℚ) := by
      exact_mod_cast hv.symm
    nlinarith
  · apply (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).2
    have hwQ : (3 : ℚ) * (p.w : ℚ) =
        ((t : ℕ) : ℚ) + 2 * (ownerQ p : ℚ) + (ownerR p : ℚ) := by
      exact_mod_cast hw.symm
    nlinarith

theorem manuscript_owner_anchor_injective {t : ℕ} :
    Function.Injective fun p : SimplexPoint t => (ownerQ p, ownerR p) := by
  intro left right heq
  have hq : ownerQ left = ownerQ right := congrArg Prod.fst heq
  have hr : ownerR left = ownerR right := congrArg Prod.snd heq
  have huLeft := recover_u_numerator left
  have huRight := recover_u_numerator right
  have hvLeft := recover_v_numerator left
  have hvRight := recover_v_numerator right
  have hwLeft := recover_w_numerator left
  have hwRight := recover_w_numerator right
  apply simplexPoint_ext <;> omega

theorem manuscript_lem_owner_simplex_meets {n : ℕ} (hn : 5 ≤ n)
    (p : SimplexPoint (n - 2)) :
    ∃ label : MicroLabel, inPeripheralBenzel n (ownerCell p label) := by
  by_cases hv : p.v < n - 2
  · exact ⟨.zero, (owner_zero_mem_iff hn p).2 hv⟩
  · have hw : p.w < n - 2 := by
      have hsum := p.sum_eq
      omega
    exact ⟨.one, (owner_one_mem_iff hn p).2 hw⟩

theorem manuscript_lem_owner_simplex_partition {n : ℕ} (hn : 5 ≤ n) :
    (∀ cell : Cell, inPeripheralBenzel n cell →
      ∃! representation : SimplexPoint (n - 2) × MicroLabel,
        ownerCell representation.1 representation.2 = cell) ∧
    (∀ p : SimplexPoint (n - 2),
      (inPeripheralBenzel n (ownerCell p .zero) ↔ p.v < n - 2) ∧
      (inPeripheralBenzel n (ownerCell p .one) ↔ p.w < n - 2) ∧
      (inPeripheralBenzel n (ownerCell p .two) ↔ p.u < n - 2)) := by
  constructor
  · intro cell hcell
    obtain ⟨p, label, hrepresentation⟩ := benzel_cell_has_owner hn cell hcell
    refine ⟨(p, label), hrepresentation, ?_⟩
    rintro ⟨p', label'⟩ hrepresentation'
    obtain ⟨hp, hlabel⟩ := owner_representation_unique cell
      p' p label' label hrepresentation' hrepresentation
    exact Prod.ext hp hlabel
  · intro p
    exact ⟨owner_zero_mem_iff hn p, owner_one_mem_iff hn p,
      owner_two_mem_iff hn p⟩

/-! ## Equation (3), Lemma 3.2, and Proposition 3.3 -/

theorem manuscript_eq_cell_energy (q r : ℤ) :
    ownerPotential .zero q r = q + r ∧
      ownerPotential .one q r = -q ∧
      ownerPotential .two q r = -r := by
  simp [ownerPotential]

theorem manuscript_lem_energy_table_values (q r : ℤ) :
    (literalTileEnergy .stone q r .r0 = 0 ∧
      literalTileEnergy .stone q r .r1 = 3 ∧
      literalTileEnergy .stone q r .r2 = 3) ∧
    (literalTileEnergy .boneA q r .r0 = 1 ∧
      literalTileEnergy .boneA q r .r1 = 4 ∧
      literalTileEnergy .boneA q r .r2 = 1) ∧
    (literalTileEnergy .boneB q r .r0 = 1 ∧
      literalTileEnergy .boneB q r .r1 = 1 ∧
      literalTileEnergy .boneB q r .r2 = 4) ∧
    (literalTileEnergy .boneC q r .r0 = 1 ∧
      literalTileEnergy .boneC q r .r1 = 4 ∧
      literalTileEnergy .boneC q r .r2 = 1) := by
  exact ⟨stone_energy_by_residue q r, boneA_energy_by_residue q r,
    boneB_energy_by_residue q r, boneC_energy_by_residue q r⟩

def manuscript_lem_energy_table_profiles := all_two_owner_bone_profiles

def manuscript_lem_energy_table_directions :=
  all_two_owner_bone_directions_allowed

def IsLabelPreservingLiteralDirectedEdge {m : ℕ}
    (edge : LiteralDirectedEdge m) : Prop :=
  let source := edge.boneClass.sourceShift
  let target := edge.boneClass.targetShift
  let label := edge.boneClass.label
  (boneOwnerProfile edge.boneClass.tile edge.boneClass.residue).count
      (source, label) = 0 ∧
    (boneOwnerProfile edge.boneClass.tile edge.boneClass.residue).count
      (target, label) = 1 ∧
    (boneOwnerProfile edge.boneClass.tile edge.boneClass.residue).countP
      (fun datum => datum.1 = source) = 2

theorem manuscript_prop_energy_rigidity {m : ℕ}
    (tiling : LiteralTiling m) :
    (∀ placement : LiteralPlacement m, placement ∈ tiling.1 →
      placement.tile = .stone →
        placementBaseResidue (m + 3) placement.base = .r0) ∧
    (∀ placement : LiteralPlacement m, placement ∈ tiling.1 →
      placement.tile ≠ .stone →
        ∃ edge : LiteralDirectedEdge m,
          edge.placement = placement ∧
          allowedStep edge.boneClass.label edge.boneClass.step ∧
          IsLabelPreservingLiteralDirectedEdge edge) := by
  constructor
  · intro placement hplacement hstone
    exact every_literal_stone_in_phase
      conwayLagariasStoneCountTarget_proved tiling placement hplacement hstone
  · intro placement hplacement hbone
    have htwo := every_literal_bone_has_two_owners
      conwayLagariasStoneCountTarget_proved tiling placement hplacement
    let edge := literalDirectedEdgeOfPlacement placement hbone htwo
    exact ⟨edge, rfl, literalDirectedEdge_allowed edge,
      goodBoneClass_profile edge.boneClass⟩

/-! ## Proposition 4.1 -/

noncomputable def manuscript_prop_Y_bijection (m : ℕ) :
    LiteralTiling m ≃ PathModelConfiguration m :=
  literalTilingPathModelEquiv_proved m

/-! ## Lemma 5.1 and Equations (4)--(6) -/

theorem manuscript_lem_independent_arms_positive_count (x y z : ℕ) :
    Fintype.card (PositiveArmTriple x y z) =
      (2 * x + y + 2).choose x *
      (2 * y + z + 2).choose y *
      (2 * z + x + 2).choose z := by
  rw [card_positiveArmTriple]
  rfl

theorem ballotNumber_eq_choose_sub_choosePred (total minority : ℕ) :
    ballotNumber total minority = total.choose minority - choosePred total minority := by
  cases minority <;> simp [ballotNumber, choosePred]

theorem manuscript_lem_independent_arms_positive_factors (x y z : ℕ) :
    Fintype.card (RecursiveBallot (x + z + 1) (z + 1)) =
        (2 * z + x + 2).choose (z + 1) - (2 * z + x + 2).choose z ∧
    Fintype.card (RecursiveBallot (x + y + 1) (x + 1)) =
        (2 * x + y + 2).choose (x + 1) - (2 * x + y + 2).choose x ∧
    Fintype.card (RecursiveBallot (y + z + 1) (y + 1)) =
        (2 * y + z + 2).choose (y + 1) - (2 * y + z + 2).choose y := by
  constructor
  · rw [card_recursiveBallot_of_le _ _ (by omega)]
    simp only [ballotNumber]
    congr 2 <;> omega
  constructor
  · rw [card_recursiveBallot_of_le _ _ (by omega)]
    simp only [ballotNumber]
    congr 2 <;> omega
  · rw [card_recursiveBallot_of_le _ _ (by omega)]
    simp only [ballotNumber]
    congr 2 <;> omega

theorem manuscript_lem_independent_arms_negative_factors (x y z : ℕ) :
    Fintype.card (RecursiveBallot (x + z + 2) z) =
        (2 * z + x + 2).choose z - choosePred (2 * z + x + 2) z ∧
    Fintype.card (RecursiveBallot (x + y + 2) x) =
        (2 * x + y + 2).choose x - choosePred (2 * x + y + 2) x ∧
    Fintype.card (RecursiveBallot (y + z + 2) y) =
        (2 * y + z + 2).choose y - choosePred (2 * y + z + 2) y := by
  constructor
  · rw [card_recursiveBallot_of_le _ _ (by omega),
      ballotNumber_eq_choose_sub_choosePred]
    congr 2 <;> omega
  constructor
  · rw [card_recursiveBallot_of_le _ _ (by omega),
      ballotNumber_eq_choose_sub_choosePred]
    congr 2 <;> omega
  · rw [card_recursiveBallot_of_le _ _ (by omega),
      ballotNumber_eq_choose_sub_choosePred]
    congr 2 <;> omega

theorem manuscript_lem_independent_arms_negative_count (x y z : ℕ) :
    Fintype.card (NegativeArmTriple x y z) =
      ((2 * x + y + 2).choose x - choosePred (2 * x + y + 2) x) *
      ((2 * y + z + 2).choose y - choosePred (2 * y + z + 2) y) *
      ((2 * z + x + 2).choose z - choosePred (2 * z + x + 2) z) := by
  rw [card_negativeArmTriple]
  simp only [negativeChiralityCount, ballotNumber_eq_choose_sub_choosePred]

theorem manuscript_eq_Pxyz (x y z : ℕ) :
    Fintype.card (PositiveArmTriple x y z) =
      (2 * x + y + 2).choose x *
      (2 * y + z + 2).choose y *
      (2 * z + x + 2).choose z :=
  manuscript_lem_independent_arms_positive_count x y z

theorem manuscript_eq_Qxyz (x y z : ℕ) :
    Fintype.card (NegativeArmTriple x y z) =
      ((2 * x + y + 2).choose x - choosePred (2 * x + y + 2) x) *
      ((2 * y + z + 2).choose y - choosePred (2 * y + z + 2) y) *
      ((2 * z + x + 2).choose z - choosePred (2 * z + x + 2) z) :=
  manuscript_lem_independent_arms_negative_count x y z

theorem manuscript_eq_QoverP (x y z : ℕ) :
    (negativeChiralityCount x y z : ℚ) /
        (positiveChiralityCount x y z : ℚ) =
      (((x + 3 : ℕ) : ℚ) * (y + 3) * (z + 3)) /
        (((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3)) := by
  have hpositiveNat : 0 < positiveChiralityCount x y z := by
    simp only [positiveChiralityCount]
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))
  have hpositive : (positiveChiralityCount x y z : ℚ) ≠ 0 := by
    exact_mod_cast hpositiveNat.ne'
  have hdenNat : 0 < (x + y + 3) * (y + z + 3) * (z + x + 3) := by
    positivity
  have hden :
      (((x + y + 3 : ℕ) : ℚ) * (y + z + 3) * (z + x + 3)) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  apply (div_eq_div_iff hpositive hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    negativeChiralityCount_ratio x y z

/-! ## Proposition 6.1 and Equations (7)--(10) -/

noncomputable def manuscriptPositiveConstantTermSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    ∑ point : SimplexPoint degree,
      MvPowerSeries.coeff ℚ (goodMultiIndex point.u point.v point.w)
        ((goodPositiveNumeratorPolynomial : GoodMvSeries) *
          goodPhiA ^ point.u * goodPhiB ^ point.v * goodPhiC ^ point.w)

theorem manuscript_eq_constant_term :
    positiveChiralityGeneratingSeries = manuscriptPositiveConstantTermSeries := by
  apply PowerSeries.ext
  intro degree
  rw [coeff_positiveChiralityGeneratingSeries]
  simp only [manuscriptPositiveConstantTermSeries, PowerSeries.coeff_mk]
  rw [positiveLevelCount]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [positiveGoodNumerator_weight_factorization,
    coeff_separated_good_powers, positiveChiralityCount]
  norm_cast

theorem manuscript_eq_Pgf :
    positiveChiralityGeneratingSeries =
      ternarySeries ^ 9 *
        (goodLinearDenominator * goodQuadraticDenominator)⁻¹ := by
  rw [positiveChiralityGeneratingSeries_eq_good]
  rfl

theorem manuscript_eq_Qgf :
    negativeChiralityGeneratingSeries =
      (C ℚ 2 - ternarySeries) ^ 3 * positiveChiralityGeneratingSeries := by
  rw [negativeChiralityGeneratingSeries_eq_good,
    positiveChiralityGeneratingSeries_eq_good]
  rfl

theorem manuscript_eq_Ygf :
    pathModelGeneratingSeries =
      ternarySeries ^ 9 * (C ℚ 3 - ternarySeries) *
        goodLinearDenominator⁻¹ := by
  rw [pathModelGeneratingSeries_eq_totalGood,
    totalGoodGeneratingSeries_simplified]

theorem manuscript_prop_generating_functions :
    positiveChiralityGeneratingSeries =
        ternarySeries ^ 9 *
          (goodLinearDenominator * goodQuadraticDenominator)⁻¹ ∧
    negativeChiralityGeneratingSeries =
        (C ℚ 2 - ternarySeries) ^ 3 * positiveChiralityGeneratingSeries ∧
    pathModelGeneratingSeries =
        ternarySeries ^ 9 * (C ℚ 3 - ternarySeries) *
          goodLinearDenominator⁻¹ :=
  ⟨manuscript_eq_Pgf, manuscript_eq_Qgf, manuscript_eq_Ygf⟩

end BenzelProblem6Kernel

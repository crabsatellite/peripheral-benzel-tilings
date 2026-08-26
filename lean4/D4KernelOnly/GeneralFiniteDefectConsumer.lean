import D4KernelOnly.GeneralRegionEnergy
import FiniteDefects.DefectArithmetic

/-! # Literal finite-defect theorem from the Conway--Lagarias bone count -/

namespace FiniteDefects

def GeneralBoneCountStatement : Prop :=
  (∀ (t k : ℕ), 1 ≤ k → 2 * k ≤ t + 1 →
    ∀ tiling : OffsetLiteralTiling t (3 * k),
      offsetBoneCount tiling = 3 * k * (t + 2 - 2 * k)) ∧
  (∀ (t k : ℕ), 1 ≤ k → 2 * k ≤ t + 1 →
    ∀ tiling : OffsetLiteralTiling t (3 * k + 1),
      offsetBoneCount tiling = 3 * k * (t + 1 - 2 * k))

def GeneralFiniteDefectStatement : Prop :=
  (∀ (t k : ℕ), 1 ≤ k → 2 * k ≤ t + 1 →
    ∀ tiling : OffsetLiteralTiling t (3 * k),
      offsetWrongPhaseStoneCount tiling +
        offsetThreeOwnerBoneCount tiling = k.choose 2) ∧
  (∀ (t k : ℕ), 1 ≤ k → 2 * k ≤ t + 1 →
    ∀ tiling : OffsetLiteralTiling t (3 * k + 1),
      offsetWrongPhaseStoneCount tiling +
        offsetThreeOwnerBoneCount tiling = (k + 1).choose 2)

theorem d3k_exact_energy_count_identity
    (t k : ℕ) (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1)
    (tiling : OffsetLiteralTiling t (3 * k)) :
    (offsetBoneCount tiling : ℚ) +
        3 * ((offsetWrongPhaseStoneCount tiling : ℚ) +
          offsetThreeOwnerBoneCount tiling) =
      3 * k * ((t + 2 : ℚ) - (3 * k + 1 : ℚ) / 2) := by
  have hdouble := twice_total_d3k_literal_cell_energy t k hk hroom
  have hcount := offset_literal_tile_energy_count_formula tiling
  have henergy := offset_tiling_energy_double_count tiling
  rw [← henergy, hcount] at hdouble
  have hdoubleQ := congrArg (fun z : ℤ => (z : ℚ)) hdouble
  push_cast at hdoubleQ ⊢
  nlinarith [hdoubleQ]

theorem d3k1_exact_energy_count_identity
    (t k : ℕ) (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1)
    (tiling : OffsetLiteralTiling t (3 * k + 1)) :
    (offsetBoneCount tiling : ℚ) +
        3 * ((offsetWrongPhaseStoneCount tiling : ℚ) +
          offsetThreeOwnerBoneCount tiling) =
      3 * k * ((t + 2 : ℚ) - (3 * k + 1 : ℚ) / 2) := by
  have hdouble := twice_total_d3k1_literal_cell_energy t k hk hroom
  have hcount := offset_literal_tile_energy_count_formula tiling
  have henergy := offset_tiling_energy_double_count tiling
  rw [← henergy, hcount] at hdouble
  have hdoubleQ := congrArg (fun z : ℤ => (z : ℚ)) hdouble
  push_cast at hdoubleQ ⊢
  nlinarith [hdoubleQ]

theorem finite_defect_d3k_of_bone_count
    (hbone : GeneralBoneCountStatement)
    (t k : ℕ) (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1)
    (tiling : OffsetLiteralTiling t (3 * k)) :
    offsetWrongPhaseStoneCount tiling +
      offsetThreeOwnerBoneCount tiling = k.choose 2 := by
  have hb := hbone.1 t k hk hroom tiling
  have hboneZ : (offsetBoneCount tiling : ℤ) =
      3 * (k : ℤ) * ((t : ℤ) + 2 - 2 * k) := by
    rw [hb]
    push_cast [Nat.cast_sub (show 2 * k ≤ t + 2 by omega)]
    ring
  have hdouble := twice_total_d3k_literal_cell_energy t k hk hroom
  have hcount := offset_literal_tile_energy_count_formula tiling
  have henergy := offset_tiling_energy_double_count tiling
  rw [← henergy, hcount] at hdouble
  have hboneQ := congrArg (fun z : ℤ => (z : ℚ)) hboneZ
  have hdoubleQ := congrArg (fun z : ℤ => (z : ℚ)) hdouble
  push_cast at hboneQ hdoubleQ
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [Nat.cast_choose_two ℚ]
  nlinarith [hboneQ, hdoubleQ]

theorem finite_defect_d3k1_of_bone_count
    (hbone : GeneralBoneCountStatement)
    (t k : ℕ) (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1)
    (tiling : OffsetLiteralTiling t (3 * k + 1)) :
    offsetWrongPhaseStoneCount tiling +
      offsetThreeOwnerBoneCount tiling = (k + 1).choose 2 := by
  have hb := hbone.2 t k hk hroom tiling
  have hboneZ : (offsetBoneCount tiling : ℤ) =
      3 * (k : ℤ) * ((t : ℤ) + 1 - 2 * k) := by
    rw [hb]
    push_cast [Nat.cast_sub (show 2 * k ≤ t + 1 by omega)]
    ring
  have hdouble := twice_total_d3k1_literal_cell_energy t k hk hroom
  have hcount := offset_literal_tile_energy_count_formula tiling
  have henergy := offset_tiling_energy_double_count tiling
  rw [← henergy, hcount] at hdouble
  have hboneQ := congrArg (fun z : ℤ => (z : ℚ)) hboneZ
  have hdoubleQ := congrArg (fun z : ℤ => (z : ℚ)) hdouble
  push_cast at hboneQ hdoubleQ
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [Nat.cast_choose_two ℚ]
  push_cast
  nlinarith [hboneQ, hdoubleQ]

theorem generalFiniteDefect_of_boneCount
    (hbone : GeneralBoneCountStatement) : GeneralFiniteDefectStatement := by
  constructor
  · intro t k hk hroom tiling
    exact finite_defect_d3k_of_bone_count hbone t k hk hroom tiling
  · intro t k hk hroom tiling
    exact finite_defect_d3k1_of_bone_count hbone t k hk hroom tiling

end FiniteDefects

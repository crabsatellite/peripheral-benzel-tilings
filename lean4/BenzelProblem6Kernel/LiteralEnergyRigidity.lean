import BenzelProblem6Kernel.LiteralTileCounts
import BenzelProblem6Kernel.TilingEnergyDoubleCount
import Mathlib.Algebra.BigOperators.Ring

/-!
# Literal energy rigidity

This file classifies every actual placement by the residue computed from its
base.  The only external mathematical input still exposed is the separately
named Conway--Lagarias stone-count target.  Once that producer is proved, the
energy identity forces every bad placement filter to be empty.
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

def IsWrongPhaseStone {m : ℕ} (placement : LiteralPlacement m) : Prop :=
  placement.tile = .stone ∧
    placementBaseResidue (m + 3) placement.base ≠ .r0

noncomputable instance isWrongPhaseStoneDecidable {m : ℕ}
    (placement : LiteralPlacement m) : Decidable (IsWrongPhaseStone placement) :=
  Classical.propDecidable _

def IsThreeOwnerBone {m : ℕ} (placement : LiteralPlacement m) : Prop :=
  match placement.tile,
      placementBaseResidue (m + 3) placement.base with
  | .boneA, .r1 => True
  | .boneB, .r2 => True
  | .boneC, .r1 => True
  | _, _ => False

noncomputable instance isThreeOwnerBoneDecidable {m : ℕ}
    (placement : LiteralPlacement m) : Decidable (IsThreeOwnerBone placement) := by
  exact Classical.propDecidable _

noncomputable def wrongPhaseStoneCount {m : ℕ} (tiling : LiteralTiling m) : ℕ :=
  (tiling.1.filter IsWrongPhaseStone).card

noncomputable def threeOwnerBoneCount {m : ℕ} (tiling : LiteralTiling m) : ℕ :=
  (tiling.1.filter IsThreeOwnerBone).card

theorem literal_placement_energy_classification {m : ℕ}
    (placement : LiteralPlacement m) :
    literalPlacementEnergy placement =
      (if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((if IsWrongPhaseStone placement then (1 : ℤ) else 0) +
          if IsThreeOwnerBone placement then (1 : ℤ) else 0) := by
  rcases htile : placement.tile with _ | _ | _ | _
  all_goals
    rcases hrho : placementBaseResidue (m + 3) placement.base with _ | _ | _
  all_goals
    simp [literalPlacementEnergy, htile, hrho, IsWrongPhaseStone,
      IsThreeOwnerBone, stone_energy_by_residue, boneA_energy_by_residue,
      boneB_energy_by_residue, boneC_energy_by_residue]

theorem sum_int_indicator_eq_filter_card {α : Type*}
    [DecidableEq α] (s : Finset α) (predicate : α → Prop)
    [DecidablePred predicate] :
    ∑ x ∈ s, (if predicate x then (1 : ℤ) else 0) =
      ((s.filter predicate).card : ℤ) := by
  exact Finset.sum_boole (α := ℤ) predicate s

theorem literal_tile_energy_count_formula {m : ℕ}
    (tiling : LiteralTiling m) :
    ∑ placement ∈ tiling.1, literalPlacementEnergy placement =
      (boneCount tiling : ℤ) +
        3 * ((wrongPhaseStoneCount tiling : ℤ) +
          (threeOwnerBoneCount tiling : ℤ)) := by
  classical
  calc
    (∑ placement ∈ tiling.1, literalPlacementEnergy placement) =
        ∑ placement ∈ tiling.1,
          ((if placement.tile ≠ .stone then (1 : ℤ) else 0) +
            3 * ((if IsWrongPhaseStone placement then (1 : ℤ) else 0) +
              if IsThreeOwnerBone placement then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro placement _
      exact literal_placement_energy_classification placement
    _ = (∑ placement ∈ tiling.1,
          if placement.tile ≠ .stone then (1 : ℤ) else 0) +
        3 * ((∑ placement ∈ tiling.1,
            if IsWrongPhaseStone placement then (1 : ℤ) else 0) +
          ∑ placement ∈ tiling.1,
            if IsThreeOwnerBone placement then (1 : ℤ) else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib]
    _ = (boneCount tiling : ℤ) +
        3 * ((wrongPhaseStoneCount tiling : ℤ) +
          (threeOwnerBoneCount tiling : ℤ)) := by
      rw [sum_int_indicator_eq_filter_card,
        sum_int_indicator_eq_filter_card,
        sum_int_indicator_eq_filter_card]
      rfl

theorem literal_energy_rigidity_of_conwayLagarias
    (hstone : conwayLagariasStoneCountTarget)
    (m : ℕ) (tiling : LiteralTiling m) :
    wrongPhaseStoneCount tiling = 0 ∧ threeOwnerBoneCount tiling = 0 := by
  have hbone := boneCount_of_conwayLagarias hstone m tiling
  have hformula := literal_tile_energy_count_formula tiling
  have htotal := total_literal_tile_energy tiling
  have hboneZ :
      (boneCount tiling : ℤ) = 3 * ((m + 3 : ℕ) : ℤ) := by
    exact_mod_cast hbone
  have henergy :
      (boneCount tiling : ℤ) +
          3 * ((wrongPhaseStoneCount tiling : ℤ) +
            (threeOwnerBoneCount tiling : ℤ)) =
        (boneCount tiling : ℤ) := by
    rw [← hformula, htotal, hboneZ]
  exact bad_tile_counts_zero (boneCount tiling)
    (wrongPhaseStoneCount tiling) (threeOwnerBoneCount tiling) henergy

theorem every_literal_stone_in_phase
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : LiteralPlacement m) (hplacement : placement ∈ tiling.1)
    (htile : placement.tile = .stone) :
    placementBaseResidue (m + 3) placement.base = .r0 := by
  have hcount := (literal_energy_rigidity_of_conwayLagarias hstone m tiling).1
  have hempty : tiling.1.filter IsWrongPhaseStone = ∅ :=
    Finset.card_eq_zero.mp hcount
  by_contra hphase
  have hbad : placement ∈ tiling.1.filter IsWrongPhaseStone := by
    simp [hplacement, IsWrongPhaseStone, htile, hphase]
  rw [hempty] at hbad
  simp at hbad

theorem every_literal_bone_has_two_owners
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : LiteralPlacement m) (hplacement : placement ∈ tiling.1) :
    ¬IsThreeOwnerBone placement := by
  have hcount := (literal_energy_rigidity_of_conwayLagarias hstone m tiling).2
  have hempty : tiling.1.filter IsThreeOwnerBone = ∅ :=
    Finset.card_eq_zero.mp hcount
  intro hthree
  have hbad : placement ∈ tiling.1.filter IsThreeOwnerBone := by
    simp [hplacement, hthree]
  rw [hempty] at hbad
  simp at hbad

end BenzelProblem6Kernel

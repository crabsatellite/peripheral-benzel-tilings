import D4KernelOnly.D4ConwayLagariasExport
import Mathlib.Tactic.Linarith

/-! # Exact d=4 one-defect theorem -/

namespace FiniteDefects

def D4OneDefectStatement : Prop :=
  ∀ (m : ℕ) (tiling : D4LiteralTiling m),
    d4WrongPhaseStoneCount tiling + d4ThreeOwnerBoneCount tiling = 1

theorem d4RightStoneCount_add_boneCount {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4RightStoneCount tiling + d4BoneCount tiling = tiling.1.card := by
  simpa [d4RightStoneCount, d4BoneCount] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := tiling.1)
      (fun placement : D4LiteralPlacement m => placement.tile = .stone))

theorem two_dvd_d4StoneTargetNumerator (m : ℕ) :
    2 ∣ m * m + m + 2 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · refine ⟨2 * k * k + k + 1, ?_⟩
    ring
  · refine ⟨2 * k * k + 3 * k + 2, ?_⟩
    ring

theorem twice_d4ConwayLagariasStoneTarget (m : ℕ) :
    2 * d4ConwayLagariasStoneTarget m = m * m + m + 2 := by
  exact Nat.mul_div_cancel' (two_dvd_d4StoneTargetNumerator m)

theorem twice_choose_m4_two (m : ℕ) :
    (m + 4).choose 2 * 2 = (m + 4) * (m + 3) := by
  simpa [show m + 4 - 1 = m + 3 by omega] using
    Nat.choose_succ_right_eq (m + 4) 1

theorem d4_bone_count_of_conwayLagarias
    (hCL : D4ConwayLagariasStatement) {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4BoneCount tiling = 3 * (m + 1) := by
  have hpartition := d4RightStoneCount_add_boneCount tiling
  rw [hCL m tiling, d4_literal_tiling_card tiling] at hpartition
  have htarget := twice_d4ConwayLagariasStoneTarget m
  have hchoose := twice_choose_m4_two m
  have hchooseLower : 2 ≤ (m + 4).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ m + 4 by omega)
    norm_num at hmono ⊢
    omega
  have hrestore : (m + 4).choose 2 - 2 + 2 = (m + 4).choose 2 :=
    Nat.sub_add_cancel hchooseLower
  nlinarith

theorem d4_exactly_one_defect
    (hCL : D4ConwayLagariasStatement) {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4WrongPhaseStoneCount tiling + d4ThreeOwnerBoneCount tiling = 1 := by
  have hbone := d4_bone_count_of_conwayLagarias hCL tiling
  have henergy := d4_exact_energy_count_identity tiling
  have hboneZ : (d4BoneCount tiling : ℤ) = 3 * (m + 1 : ℤ) := by
    exact_mod_cast hbone
  rw [hboneZ] at henergy
  have hcountZ :
      (d4WrongPhaseStoneCount tiling : ℤ) +
          (d4ThreeOwnerBoneCount tiling : ℤ) = 1 := by
    nlinarith
  exact_mod_cast hcountZ

theorem d4_exactly_one_defect_reference {m : ℕ}
    (tiling : D4LiteralTiling m) :
    d4WrongPhaseStoneCount tiling + d4ThreeOwnerBoneCount tiling = 1 :=
  d4_exactly_one_defect d4ConwayLagariasReference tiling

theorem d4OneDefectKernelWithReference : D4OneDefectStatement :=
  fun _m tiling => d4_exactly_one_defect_reference tiling

end FiniteDefects

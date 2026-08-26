import FiniteDefects.D4ReversePaths

/-! # Coordinate separation of the three defect cores -/

namespace FiniteDefects

theorem d4_core_zero_w_gt_one {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4DefectCore tiling .one).w < (d4DefectCore tiling .zero).w := by
  have hzero := d4DefectCore_anchor tiling .zero
  have hone := d4DefectCore_anchor tiling .one
  have hwzero := recover_w_numerator (d4DefectCore tiling .zero)
  have hwone := recover_w_numerator (d4DefectCore tiling .one)
  generalize hk : d4DefectKind tiling = kind at hzero hone
  rcases kind <;>
    simp [D4DefectKind.ownerShift] at hzero hone
  all_goals rcases hzero with ⟨hzq, hzr⟩
  all_goals rcases hone with ⟨hoq, hor⟩
  all_goals omega

theorem d4_core_one_u_gt_two {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4DefectCore tiling .two).u < (d4DefectCore tiling .one).u := by
  have hone := d4DefectCore_anchor tiling .one
  have htwo := d4DefectCore_anchor tiling .two
  have huone := recover_u_numerator (d4DefectCore tiling .one)
  have hutwo := recover_u_numerator (d4DefectCore tiling .two)
  generalize hk : d4DefectKind tiling = kind at hone htwo
  rcases kind <;>
    simp [D4DefectKind.ownerShift] at hone htwo
  all_goals rcases hone with ⟨hoq, hor⟩
  all_goals rcases htwo with ⟨htq, htr⟩
  all_goals omega

theorem d4_core_two_v_gt_zero {m : ℕ} (tiling : D4LiteralTiling m) :
    (d4DefectCore tiling .zero).v < (d4DefectCore tiling .two).v := by
  have hzero := d4DefectCore_anchor tiling .zero
  have htwo := d4DefectCore_anchor tiling .two
  have hvzero := recover_v_numerator (d4DefectCore tiling .zero)
  have hvtwo := recover_v_numerator (d4DefectCore tiling .two)
  generalize hk : d4DefectKind tiling = kind at hzero htwo
  rcases kind <;>
    simp [D4DefectKind.ownerShift] at hzero htwo
  all_goals rcases hzero with ⟨hzq, hzr⟩
  all_goals rcases htwo with ⟨htq, htr⟩
  all_goals omega

end FiniteDefects

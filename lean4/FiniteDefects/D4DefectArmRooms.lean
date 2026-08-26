import FiniteDefects.D4ArmCard

/-! # Every literal defect core has room for its three decoded arms -/

namespace FiniteDefects

theorem D4DefectPlacement.arm_room {m : ℕ}
    (defect : D4DefectPlacement m) (label : MicroLabel) :
    d4ArmRoom label (defect.core label) := by
  rcases label with _ | _ | _
  · have hsum := (defect.core .zero).sum_eq
    have hpositive := defect.core_zero_w_gt_one
    simp only [d4ArmRoom, d4ArmMajority]
    omega
  · have hsum := (defect.core .one).sum_eq
    have hpositive := defect.core_one_u_gt_two
    simp only [d4ArmRoom, d4ArmMajority]
    omega
  · have hsum := (defect.core .two).sum_eq
    have hpositive := defect.core_two_v_gt_zero
    simp only [d4ArmRoom, d4ArmMajority]
    omega

end FiniteDefects

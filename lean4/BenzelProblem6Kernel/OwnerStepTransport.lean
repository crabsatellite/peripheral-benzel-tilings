import BenzelProblem6Kernel.OwnerCoordinates
import BenzelProblem6Kernel.NoCycles

/-!
# Transport of anchor steps to simplex-coordinate steps
-/

namespace BenzelProblem6Kernel

theorem stepA_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepA = (ownerQ q, ownerR q)) :
    q.u + 1 = p.u ∧ q.v = p.v ∧ q.w = p.w + 1 := by
  have hq : ownerQ p + 2 = ownerQ q := congrArg Prod.fst hstep
  have hr : ownerR p - 1 = ownerR q := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepA] at hq hr
  constructor
  · omega
  constructor <;> omega

theorem stepB_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepB = (ownerQ q, ownerR q)) :
    q.u = p.u ∧ q.v = p.v + 1 ∧ q.w + 1 = p.w := by
  have hq : ownerQ p - 1 = ownerQ q := congrArg Prod.fst hstep
  have hr : ownerR p - 1 = ownerR q := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepB] at hq hr
  constructor
  · omega
  constructor <;> omega

theorem stepC_simplex_coordinates {t : ℕ} (p q : SimplexPoint t)
    (hstep : addCell (ownerQ p, ownerR p) stepC = (ownerQ q, ownerR q)) :
    q.u = p.u + 1 ∧ q.v + 1 = p.v ∧ q.w = p.w := by
  have hq : ownerQ p - 1 = ownerQ q := congrArg Prod.fst hstep
  have hr : ownerR p + 2 = ownerR q := congrArg Prod.snd hstep
  have hu := recover_u_numerator p
  have hu' := recover_u_numerator q
  have hv := recover_v_numerator p
  have hv' := recover_v_numerator q
  have hw := recover_w_numerator p
  have hw' := recover_w_numerator q
  simp [addCell, stepC] at hq hr
  constructor
  · omega
  constructor <;> omega

end BenzelProblem6Kernel

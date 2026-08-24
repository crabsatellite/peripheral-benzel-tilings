import BenzelProblem6Kernel.WZSimplexEquiv
import BenzelProblem6Kernel.ClosedFormUniqueness

/-!
# Finite simplex telescoping of the WZ certificate
-/

namespace BenzelProblem6Kernel

open scoped BigOperators

theorem wzIncomingX_zero_of_u_zero (m : ℕ) (p : SimplexPoint m)
    (hu : p.u = 0) : wzIncomingX m p.u p.v p.w = 0 := by
  simp [wzIncomingX, wzB₀, hu]

theorem wzIncomingY_zero_of_v_zero (m : ℕ) (p : SimplexPoint m)
    (hv : p.v = 0) : wzIncomingY m p.u p.v p.w = 0 := by
  simp [wzIncomingY, wzB₁, hv]

theorem wzBoundaryIncomingX_zero_of_u_zero (m : ℕ) (p : ZeroWPoint (m + 1))
    (hu : p.1.u = 0) : wzBoundaryIncomingX m p.1.u p.1.v = 0 := by
  simp [wzBoundaryIncomingX, wzB₀, hu]

theorem wzBoundaryIncomingY_zero_of_v_zero (m : ℕ) (p : ZeroWPoint (m + 1))
    (hv : p.1.v = 0) : wzBoundaryIncomingY m p.1.u p.1.v = 0 := by
  simp [wzBoundaryIncomingY, wzB₁, hv]

theorem wz_sum_outgoing_sub_incoming_X (m : ℕ) :
    (∑ p : SimplexPoint m, wzOutgoingX m p.u p.v p.w) -
        (∑ p : SimplexPoint m, wzIncomingX m p.u p.v p.w) =
      ∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w := by
  classical
  have hincoming :
      (∑ p : SimplexPoint m, wzIncomingX m p.u p.v p.w) =
        ∑ p : PositiveUPoint m, wzIncomingX m p.1.u p.1.v p.1.w := by
    apply sum_eq_subtype_of_zero
    intro p hp
    apply wzIncomingX_zero_of_u_zero
    omega
  have hreindex :
      (∑ p : PositiveWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w) =
        ∑ p : PositiveUPoint m, wzIncomingX m p.1.u p.1.v p.1.w := by
    apply Fintype.sum_equiv (shiftWToUEquiv m)
    intro p
    simpa [shiftWToUEquiv] using
      (wzOutgoingX_eq_nextIncomingX m p.1.u p.1.v p.1.w
        p.1.sum_eq.symm p.2)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : SimplexPoint m => 0 < p.w)
    (fun p => wzOutgoingX m p.u p.v p.w)
  have hzero :
      (∑ p : {p : SimplexPoint m // ¬0 < p.w},
          wzOutgoingX m p.1.u p.1.v p.1.w) =
        ∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w := by
    apply Fintype.sum_equiv (notPositiveWEquivZeroW m)
    intro p
    rfl
  rw [hincoming, ← hreindex]
  linarith

theorem wz_sum_outgoing_sub_incoming_Y (m : ℕ) :
    (∑ p : SimplexPoint m, wzOutgoingY m p.u p.v p.w) -
        (∑ p : SimplexPoint m, wzIncomingY m p.u p.v p.w) =
      ∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w := by
  classical
  have hincoming :
      (∑ p : SimplexPoint m, wzIncomingY m p.u p.v p.w) =
        ∑ p : PositiveVPoint m, wzIncomingY m p.1.u p.1.v p.1.w := by
    apply sum_eq_subtype_of_zero
    intro p hp
    apply wzIncomingY_zero_of_v_zero
    omega
  have hreindex :
      (∑ p : PositiveWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w) =
        ∑ p : PositiveVPoint m, wzIncomingY m p.1.u p.1.v p.1.w := by
    apply Fintype.sum_equiv (shiftWToVEquiv m)
    intro p
    simpa [shiftWToVEquiv] using
      (wzOutgoingY_eq_nextIncomingY m p.1.u p.1.v p.1.w
        p.1.sum_eq.symm p.2)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : SimplexPoint m => 0 < p.w)
    (fun p => wzOutgoingY m p.u p.v p.w)
  have hzero :
      (∑ p : {p : SimplexPoint m // ¬0 < p.w},
          wzOutgoingY m p.1.u p.1.v p.1.w) =
        ∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w := by
    apply Fintype.sum_equiv (notPositiveWEquivZeroW m)
    intro p
    rfl
  rw [hincoming, ← hreindex]
  linarith

theorem wz_boundary_reindex_X (m : ℕ) :
    (∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w) =
      ∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingX m q.1.u q.1.v := by
  classical
  have hshift :
      (∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w) =
        ∑ q : ZeroWPositiveUPoint (m + 1),
          wzBoundaryIncomingX m q.1.u q.1.v := by
    apply Fintype.sum_equiv (boundaryShiftUEquiv m)
    intro p
    have hm : m = p.1.u + p.1.v := by
      have := p.1.sum_eq
      omega
    rw [p.2]
    simpa [boundaryShiftUEquiv] using
      (wzOutgoingX_eq_boundaryIncomingX m p.1.u p.1.v hm)
  have hall :
      (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingX m q.1.u q.1.v) =
        ∑ q : {q : ZeroWPoint (m + 1) // 0 < q.1.u},
          wzBoundaryIncomingX m q.1.1.u q.1.1.v := by
    apply sum_eq_subtype_of_zero
    intro q hq
    apply wzBoundaryIncomingX_zero_of_u_zero
    omega
  have hnested :
      (∑ q : {q : ZeroWPoint (m + 1) // 0 < q.1.u},
          wzBoundaryIncomingX m q.1.1.u q.1.1.v) =
        ∑ q : ZeroWPositiveUPoint (m + 1),
          wzBoundaryIncomingX m q.1.u q.1.v := by
    apply Fintype.sum_equiv (nestedZeroWPositiveUEquiv (m + 1))
    intro q
    rfl
  rw [hshift, hall, hnested]

theorem wz_boundary_reindex_Y (m : ℕ) :
    (∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w) =
      ∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingY m q.1.u q.1.v := by
  classical
  have hshift :
      (∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w) =
        ∑ q : ZeroWPositiveVPoint (m + 1),
          wzBoundaryIncomingY m q.1.u q.1.v := by
    apply Fintype.sum_equiv (boundaryShiftVEquiv m)
    intro p
    have hm : m = p.1.u + p.1.v := by
      have := p.1.sum_eq
      omega
    rw [p.2]
    simpa [boundaryShiftVEquiv] using
      (wzOutgoingY_eq_boundaryIncomingY m p.1.u p.1.v hm)
  have hall :
      (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingY m q.1.u q.1.v) =
        ∑ q : {q : ZeroWPoint (m + 1) // 0 < q.1.v},
          wzBoundaryIncomingY m q.1.1.u q.1.1.v := by
    apply sum_eq_subtype_of_zero
    intro q hq
    apply wzBoundaryIncomingY_zero_of_v_zero
    omega
  have hnested :
      (∑ q : {q : ZeroWPoint (m + 1) // 0 < q.1.v},
          wzBoundaryIncomingY m q.1.1.u q.1.1.v) =
        ∑ q : ZeroWPositiveVPoint (m + 1),
          wzBoundaryIncomingY m q.1.u q.1.v := by
    apply Fintype.sum_equiv (nestedZeroWPositiveVEquiv (m + 1))
    intro q
    rfl
  rw [hshift, hall, hnested]

theorem wz_kernel_level_split (m : ℕ) :
    (∑ p : SimplexPoint (m + 1), rationalKernelTerm p.u p.v p.w) =
      (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v (p.w + 1)) +
        ∑ q : ZeroWPoint (m + 1), rationalKernelTerm q.1.u q.1.v q.1.w := by
  classical
  have hlift :
      (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v (p.w + 1)) =
        ∑ q : PositiveWPoint (m + 1),
          rationalKernelTerm q.1.u q.1.v q.1.w := by
    apply Fintype.sum_equiv (liftWEquiv m)
    intro p
    rfl
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : SimplexPoint (m + 1) => 0 < p.w)
    (fun p => rationalKernelTerm p.u p.v p.w)
  have hzero :
      (∑ p : {p : SimplexPoint (m + 1) // ¬0 < p.w},
          rationalKernelTerm p.1.u p.1.v p.1.w) =
        ∑ q : ZeroWPoint (m + 1),
          rationalKernelTerm q.1.u q.1.v q.1.w := by
    apply Fintype.sum_equiv (notPositiveWEquivZeroW (m + 1))
    intro p
    rfl
  rw [hlift, ← hzero]
  linarith

theorem pathModelCount_cast_eq_kernel_sum (m : ℕ) :
    (pathModelCount m : ℚ) =
      ∑ p : SimplexPoint m, rationalKernelTerm p.u p.v p.w := by
  classical
  simp only [pathModelCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact fixedSinkCount_eq_rationalKernelTerm p.u p.v p.w

theorem wz_summed_point_recurrence (m : ℕ) :
    wzLeadingCoefficient m *
          (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v (p.w + 1)) -
        wzTrailingCoefficient m *
          (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v p.w) =
      (∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w) +
        ∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w := by
  classical
  calc
    wzLeadingCoefficient m *
          (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v (p.w + 1)) -
        wzTrailingCoefficient m *
          (∑ p : SimplexPoint m, rationalKernelTerm p.u p.v p.w) =
      ∑ p : SimplexPoint m,
        (wzLeadingCoefficient m * rationalKernelTerm p.u p.v (p.w + 1) -
          wzTrailingCoefficient m * rationalKernelTerm p.u p.v p.w) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ p : SimplexPoint m,
        ((wzOutgoingX m p.u p.v p.w - wzIncomingX m p.u p.v p.w) +
          (wzOutgoingY m p.u p.v p.w - wzIncomingY m p.u p.v p.w)) := by
      apply Finset.sum_congr rfl
      intro p _
      exact wz_point_recurrence m p.u p.v p.w p.sum_eq.symm
    _ = ((∑ p : SimplexPoint m, wzOutgoingX m p.u p.v p.w) -
          ∑ p : SimplexPoint m, wzIncomingX m p.u p.v p.w) +
        ((∑ p : SimplexPoint m, wzOutgoingY m p.u p.v p.w) -
          ∑ p : SimplexPoint m, wzIncomingY m p.u p.v p.w) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]
    _ = (∑ p : ZeroWPoint m, wzOutgoingX m p.1.u p.1.v p.1.w) +
        ∑ p : ZeroWPoint m, wzOutgoingY m p.1.u p.1.v p.1.w := by
      rw [wz_sum_outgoing_sub_incoming_X, wz_sum_outgoing_sub_incoming_Y]

theorem wz_summed_boundary_cancellation (m : ℕ) :
    wzLeadingCoefficient m *
          (∑ q : ZeroWPoint (m + 1),
            rationalKernelTerm q.1.u q.1.v q.1.w) +
        (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingX m q.1.u q.1.v) +
        (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingY m q.1.u q.1.v) = 0 := by
  classical
  calc
    wzLeadingCoefficient m *
          (∑ q : ZeroWPoint (m + 1),
            rationalKernelTerm q.1.u q.1.v q.1.w) +
        (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingX m q.1.u q.1.v) +
        (∑ q : ZeroWPoint (m + 1), wzBoundaryIncomingY m q.1.u q.1.v) =
      ∑ q : ZeroWPoint (m + 1),
        (wzLeadingCoefficient m * rationalKernelTerm q.1.u q.1.v q.1.w +
          wzBoundaryIncomingX m q.1.u q.1.v +
          wzBoundaryIncomingY m q.1.u q.1.v) := by
      rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      have hboundary : m + 1 = q.1.u + q.1.v := by
        have := q.1.sum_eq
        have := q.2
        omega
      simpa [q.2] using wz_boundary_cancellation m q.1.u q.1.v hboundary

theorem pathModelCount_recurrence (m : ℕ) :
    recurrenceLeft m * (pathModelCount (m + 1) : ℚ) =
      recurrenceRight m * (pathModelCount m : ℚ) := by
  have hpoint := wz_summed_point_recurrence m
  rw [wz_boundary_reindex_X, wz_boundary_reindex_Y] at hpoint
  have hboundary := wz_summed_boundary_cancellation m
  have hsplit := wz_kernel_level_split m
  have hnext := pathModelCount_cast_eq_kernel_sum (m + 1)
  have hcurrent := pathModelCount_cast_eq_kernel_sum m
  have hleft : wzLeadingCoefficient (m : ℚ) = recurrenceLeft m := by
    simp [wzLeadingCoefficient, recurrenceLeft]
  have hright : wzTrailingCoefficient (m : ℚ) = recurrenceRight m := by
    simp [wzTrailingCoefficient, recurrenceRight]
  rw [← hleft, ← hright, hnext, hcurrent]
  rw [hsplit]
  linear_combination hpoint + hboundary

theorem pathModelRecurrenceTarget_proved : pathModelRecurrenceTarget :=
  pathModelCount_recurrence

end BenzelProblem6Kernel

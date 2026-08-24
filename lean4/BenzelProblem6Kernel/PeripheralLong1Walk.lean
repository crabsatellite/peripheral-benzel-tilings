import BenzelProblem6Kernel.PeripheralIncidenceWalk

/-! # Continuous clockwise walk along the first long peripheral side -/

namespace BenzelProblem6Kernel

def peripheralLong₁WalkStart (m r : ℕ) : HexVertex :=
  if r = 0 then ((m : ℤ) + 2, -((m : ℤ)) - 4)
  else ((m : ℤ) + 2 - 3 * r, -((m : ℤ)) - 5)

def peripheralLong₁WalkEnd (m r : ℕ) : HexVertex :=
  ((m : ℤ) - 1 - 3 * r, -((m : ℤ)) - 5)

theorem peripheralLong₁Entry_continuous (m r : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₁WalkStart m r)
      (clockwiseIncidenceEdges (peripheralLong₁Entry m r))
      (peripheralLong₁WalkEnd m r) := by
  by_cases hr : r = 0
  · subst r
    convert walkLabeledHexEdges_continuous
        ((m : ℤ) + 2, -((m : ℤ)) - 4)
        [(shadowA.neg, .a), (shadowC, .c), (shadowA.neg, .a)] using 1 <;>
      simp [peripheralLong₁WalkStart, peripheralLong₁WalkEnd,
      peripheralLong₁Entry, clockwiseIncidenceEdges,
      clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
      reverseLabeledHexEdge, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    convert walkLabeledHexEdges_continuous
        ((m : ℤ) + 2 - 3 * (k + 1), -((m : ℤ)) - 5)
        [(shadowB, .b), (shadowA.neg, .a),
          (shadowC, .c), (shadowA.neg, .a)] using 1 <;>
      simp [peripheralLong₁WalkStart, peripheralLong₁WalkEnd,
      peripheralLong₁Entry, clockwiseIncidenceEdges,
      clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
      reverseLabeledHexEdge, walkLabeledHexEdges,
      advanceLabeledHexEdge, addHexStep,
      hexCellStartVertex, hexCellCenter, ShadowStep.neg,
      shadowA, shadowB, shadowC, labeledHexWalkEnd] <;>
      push_cast <;> ring <;> simp

def peripheralLong₁PrefixEnd (m k : ℕ) : HexVertex :=
  if k = 0 then ((m : ℤ) + 2, -((m : ℤ)) - 4)
  else ((m : ℤ) + 2 - 3 * k, -((m : ℤ)) - 5)

theorem peripheralLong₁_prefix_continuous (m k : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₁PrefixEnd m 0)
      (clockwiseIncidenceEdges
        ((List.range k).flatMap (peripheralLong₁Entry m)))
      (peripheralLong₁PrefixEnd m k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append,
        clockwiseIncidenceEdges_append]
      simp only [List.flatMap_singleton, List.append_nil]
      apply ih.append
      have hentry := peripheralLong₁Entry_continuous m k
      convert hentry using 1 <;>
        simp [peripheralLong₁PrefixEnd,
          peripheralLong₁WalkStart, peripheralLong₁WalkEnd] <;>
        push_cast <;> ring

theorem peripheralLong₁_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 2, -((m : ℤ)) - 4)
      (clockwiseIncidenceEdges (peripheralLong₁ m))
      (-2 * (m : ℤ) - 7, -((m : ℤ)) - 5) := by
  convert peripheralLong₁_prefix_continuous m (m + 3) using 1 <;>
    simp [peripheralLong₁, peripheralLong₁PrefixEnd] <;>
    push_cast <;> ring

end BenzelProblem6Kernel

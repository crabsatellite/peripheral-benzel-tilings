import BenzelProblem6Kernel.PeripheralIncidenceWalk

/-! # Continuous clockwise walk along the third long peripheral side -/

namespace BenzelProblem6Kernel

def peripheralLong₃WalkStart (m r : ℕ) : HexVertex :=
  if r = 0 then (-2 * (m : ℤ) - 6, -((m : ℤ)) - 2)
  else (-2 * (m : ℤ) - 7 + 3 * r,
    -((m : ℤ)) - 2 + 3 * r)

def peripheralLong₃WalkEnd (m r : ℕ) : HexVertex :=
  (-2 * (m : ℤ) - 4 + 3 * r,
    -((m : ℤ)) + 1 + 3 * r)

theorem peripheralLong₃Entry_continuous (m r : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₃WalkStart m r)
      (clockwiseIncidenceEdges (peripheralLong₃Entry m r))
      (peripheralLong₃WalkEnd m r) := by
  by_cases hr : r = 0
  · subst r
    convert walkLabeledHexEdges_continuous
        (-2 * (m : ℤ) - 6, -((m : ℤ)) - 2)
        [(shadowC.neg, .c), (shadowB, .b), (shadowC.neg, .c)] using 1 <;>
      simp [peripheralLong₃WalkStart, peripheralLong₃WalkEnd,
        peripheralLong₃Entry, clockwiseIncidenceEdges,
        clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
        reverseLabeledHexEdge, walkLabeledHexEdges,
        advanceLabeledHexEdge, addHexStep,
        hexCellStartVertex, hexCellCenter, ShadowStep.neg,
        shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    convert walkLabeledHexEdges_continuous
        (-2 * (m : ℤ) - 7 + 3 * (k + 1),
          -((m : ℤ)) - 2 + 3 * (k + 1))
        [(shadowA, .a), (shadowC.neg, .c),
          (shadowB, .b), (shadowC.neg, .c)] using 1 <;>
      simp [peripheralLong₃WalkStart, peripheralLong₃WalkEnd,
        peripheralLong₃Entry, clockwiseIncidenceEdges,
        clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
        reverseLabeledHexEdge, walkLabeledHexEdges,
        advanceLabeledHexEdge, addHexStep,
        hexCellStartVertex, hexCellCenter, ShadowStep.neg,
        shadowA, shadowB, shadowC, labeledHexWalkEnd] <;>
      push_cast <;> ring <;> simp

def peripheralLong₃PrefixEnd (m k : ℕ) : HexVertex :=
  if k = 0 then (-2 * (m : ℤ) - 6, -((m : ℤ)) - 2)
  else (-2 * (m : ℤ) - 7 + 3 * k,
    -((m : ℤ)) - 2 + 3 * k)

theorem peripheralLong₃_prefix_continuous (m k : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₃PrefixEnd m 0)
      (clockwiseIncidenceEdges
        ((List.range k).flatMap (peripheralLong₃Entry m)))
      (peripheralLong₃PrefixEnd m k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append,
        clockwiseIncidenceEdges_append]
      simp only [List.flatMap_singleton, List.append_nil]
      apply ih.append
      have hentry := peripheralLong₃Entry_continuous m k
      convert hentry using 1 <;>
        simp [peripheralLong₃PrefixEnd,
          peripheralLong₃WalkStart, peripheralLong₃WalkEnd] <;>
        push_cast <;> ring <;> simp

theorem peripheralLong₃_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      (-2 * (m : ℤ) - 6, -((m : ℤ)) - 2)
      (clockwiseIncidenceEdges (peripheralLong₃ m))
      ((m : ℤ) + 2, 2 * (m : ℤ) + 7) := by
  convert peripheralLong₃_prefix_continuous m (m + 3) using 1 <;>
    simp [peripheralLong₃, peripheralLong₃PrefixEnd] <;>
    push_cast <;> ring <;> simp

end BenzelProblem6Kernel

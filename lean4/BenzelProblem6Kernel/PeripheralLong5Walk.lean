import BenzelProblem6Kernel.PeripheralIncidenceWalk

/-! # Continuous clockwise walk along the fifth long peripheral side -/

namespace BenzelProblem6Kernel

def peripheralLong₅WalkStart (m r : ℕ) : HexVertex :=
  if r = 0 then ((m : ℤ) + 4, 2 * (m : ℤ) + 6)
  else ((m : ℤ) + 5, 2 * (m : ℤ) + 7 - 3 * r)

def peripheralLong₅WalkEnd (m r : ℕ) : HexVertex :=
  ((m : ℤ) + 5, 2 * (m : ℤ) + 4 - 3 * r)

theorem peripheralLong₅Entry_continuous (m r : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₅WalkStart m r)
      (clockwiseIncidenceEdges (peripheralLong₅Entry m r))
      (peripheralLong₅WalkEnd m r) := by
  by_cases hr : r = 0
  · subst r
    convert walkLabeledHexEdges_continuous
        ((m : ℤ) + 4, 2 * (m : ℤ) + 6)
        [(shadowB.neg, .b), (shadowA, .a), (shadowB.neg, .b)] using 1 <;>
      simp [peripheralLong₅WalkStart, peripheralLong₅WalkEnd,
        peripheralLong₅Entry, clockwiseIncidenceEdges,
        clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
        reverseLabeledHexEdge, walkLabeledHexEdges,
        advanceLabeledHexEdge, addHexStep,
        hexCellStartVertex, hexCellCenter, ShadowStep.neg,
        shadowA, shadowB, shadowC, labeledHexWalkEnd] <;> ring <;> simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    convert walkLabeledHexEdges_continuous
        ((m : ℤ) + 5, 2 * (m : ℤ) + 7 - 3 * (k + 1))
        [(shadowC, .c), (shadowB.neg, .b),
          (shadowA, .a), (shadowB.neg, .b)] using 1 <;>
      simp [peripheralLong₅WalkStart, peripheralLong₅WalkEnd,
        peripheralLong₅Entry, clockwiseIncidenceEdges,
        clockwiseCellSideEdge, cellSideBoundaryEdge, cellBoundaryEdgeAt,
        reverseLabeledHexEdge, walkLabeledHexEdges,
        advanceLabeledHexEdge, addHexStep,
        hexCellStartVertex, hexCellCenter, ShadowStep.neg,
        shadowA, shadowB, shadowC, labeledHexWalkEnd] <;>
      push_cast <;> ring <;> simp

def peripheralLong₅PrefixEnd (m k : ℕ) : HexVertex :=
  if k = 0 then ((m : ℤ) + 4, 2 * (m : ℤ) + 6)
  else ((m : ℤ) + 5, 2 * (m : ℤ) + 7 - 3 * k)

theorem peripheralLong₅_prefix_continuous (m k : ℕ) :
    ContinuousLabeledEdgePath (peripheralLong₅PrefixEnd m 0)
      (clockwiseIncidenceEdges
        ((List.range k).flatMap (peripheralLong₅Entry m)))
      (peripheralLong₅PrefixEnd m k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append,
        clockwiseIncidenceEdges_append]
      simp only [List.flatMap_singleton, List.append_nil]
      apply ih.append
      have hentry := peripheralLong₅Entry_continuous m k
      convert hentry using 1 <;>
        simp [peripheralLong₅PrefixEnd,
          peripheralLong₅WalkStart, peripheralLong₅WalkEnd] <;>
        push_cast <;> ring <;> simp

theorem peripheralLong₅_continuous (m : ℕ) :
    ContinuousLabeledEdgePath
      ((m : ℤ) + 4, 2 * (m : ℤ) + 6)
      (clockwiseIncidenceEdges (peripheralLong₅ m))
      ((m : ℤ) + 5, -((m : ℤ)) - 2) := by
  convert peripheralLong₅_prefix_continuous m (m + 3) using 1 <;>
    simp [peripheralLong₅, peripheralLong₅PrefixEnd] <;>
    push_cast <;> ring <;> simp

end BenzelProblem6Kernel

import BenzelProblem6Kernel.PrefixEdgeSteps

/-!
# Region membership of cells carried by adjacent arm prefixes
-/

namespace BenzelProblem6Kernel

private theorem appended_prefix_majority_positive {up down : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path) :
    0 < majorityCount (pre ++ [move]) := by
  have hballot := (recursiveBallotWord_isBallot path).prefix_closed hp
  have hcount := hballot.count_le
  rcases move with _ | _
  · simp [majorityCount]
  · have hstrict : minorityCount pre + 1 ≤ majorityCount pre := by
      simpa [majorityCount, minorityCount] using hcount
    have hpositive : 0 < majorityCount pre := by omega
    simpa [majorityCount] using hpositive

theorem labelZeroPrefix_source_cells_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .zero →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelZeroPrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hp) (by omega)) label) := by
  intro label hne
  have hpSource := (List.prefix_append pre [move]).trans hp
  have hmajor := majorityCount_prefix_le hpSource
  have hminor := minorityCount_prefix_le hpSource
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · exact (hne rfl).elim
  · rw [owner_one_mem_iff (by omega)]
    have hcoord :
        ((labelZeroPrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).w : ℤ) = minorityCount pre := by
      simpa only [labelZeroPrefixPoint] using
        (labelZeroPrefixSimplexPoint_w (t := m + 3)
          path pre hpSource (by omega))
    omega
  · rw [owner_two_mem_iff (by omega)]
    have hcoord :
        ((labelZeroPrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).u : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelZeroPrefixPoint] using
        (labelZeroPrefixSimplexPoint_u (t := m + 3)
          path pre hpSource (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hpSource
    omega

theorem labelZeroPrefix_target_cell_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) :
    inPeripheralBenzel (m + 5)
      (ownerCell (labelZeroPrefixSimplexPoint (t := m + 3)
        path (pre ++ [move]) hp
        (by omega)) .zero) := by
  rw [owner_zero_mem_iff (by omega)]
  have hpositive := appended_prefix_majority_positive path pre move hp
  have hcoord :
      ((labelZeroPrefixSimplexPoint (t := m + 3) path
        (pre ++ [move]) hp (by omega)).v : ℤ) =
          (m + 3 : ℤ) - majorityCount (pre ++ [move]) := by
    simpa only [labelZeroPrefixPoint] using
      (labelZeroPrefixSimplexPoint_v (t := m + 3)
        path (pre ++ [move]) hp (by omega))
  omega

theorem labelOnePrefix_source_cells_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .one →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelOnePrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hp) (by omega)) label) := by
  intro label hne
  have hpSource := (List.prefix_append pre [move]).trans hp
  have hmajor := majorityCount_prefix_le hpSource
  have hminor := minorityCount_prefix_le hpSource
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · rw [owner_zero_mem_iff (by omega)]
    have hcoord :
        ((labelOnePrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).v : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelOnePrefixPoint] using
        (labelOnePrefixSimplexPoint_v (t := m + 3)
          path pre hpSource (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hpSource
    omega
  · exact (hne rfl).elim
  · rw [owner_two_mem_iff (by omega)]
    have hcoord :
        ((labelOnePrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).u : ℤ) = minorityCount pre := by
      simpa only [labelOnePrefixPoint] using
        (labelOnePrefixSimplexPoint_u (t := m + 3)
          path pre hpSource (by omega))
    omega

theorem labelOnePrefix_target_cell_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) :
    inPeripheralBenzel (m + 5)
      (ownerCell (labelOnePrefixSimplexPoint (t := m + 3)
        path (pre ++ [move]) hp
        (by omega)) .one) := by
  rw [owner_one_mem_iff (by omega)]
  have hpositive := appended_prefix_majority_positive path pre move hp
  have hcoord :
      ((labelOnePrefixSimplexPoint (t := m + 3) path
        (pre ++ [move]) hp (by omega)).w : ℤ) =
          (m + 3 : ℤ) - majorityCount (pre ++ [move]) := by
    simpa only [labelOnePrefixPoint] using
      (labelOnePrefixSimplexPoint_w (t := m + 3)
        path (pre ++ [move]) hp (by omega))
  omega

theorem labelTwoPrefix_source_cells_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) (hdown : down < m + 3) :
    ∀ label, label ≠ .two →
      inPeripheralBenzel (m + 5)
        (ownerCell (labelTwoPrefixSimplexPoint (t := m + 3) path pre
          ((List.prefix_append pre [move]).trans hp) (by omega)) label) := by
  intro label hne
  have hpSource := (List.prefix_append pre [move]).trans hp
  have hmajor := majorityCount_prefix_le hpSource
  have hminor := minorityCount_prefix_le hpSource
  rw [recursiveBallotWord_majority path] at hmajor
  rw [recursiveBallotWord_minority path] at hminor
  rcases label with _ | _ | _
  · rw [owner_zero_mem_iff (by omega)]
    have hcoord :
        ((labelTwoPrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).v : ℤ) = minorityCount pre := by
      simpa only [labelTwoPrefixPoint] using
        (labelTwoPrefixSimplexPoint_v (t := m + 3)
          path pre hpSource (by omega))
    omega
  · rw [owner_one_mem_iff (by omega)]
    have hcoord :
        ((labelTwoPrefixSimplexPoint (t := m + 3) path pre hpSource
          (by omega)).w : ℤ) =
            (majorityCount pre : ℤ) - minorityCount pre := by
      simpa only [labelTwoPrefixPoint] using
        (labelTwoPrefixSimplexPoint_w (t := m + 3)
          path pre hpSource (by omega))
    have hcount := recursiveBallotPrefix_count_le path pre hpSource
    omega
  · exact (hne rfl).elim

theorem labelTwoPrefix_target_cell_mem {up down m : ℕ}
    (path : RecursiveBallot up down) (pre : List BallotMove)
    (move : BallotMove)
    (hp : pre ++ [move] <+: recursiveBallotWord path)
    (hup : up < m + 3) :
    inPeripheralBenzel (m + 5)
      (ownerCell (labelTwoPrefixSimplexPoint (t := m + 3)
        path (pre ++ [move]) hp
        (by omega)) .two) := by
  rw [owner_two_mem_iff (by omega)]
  have hpositive := appended_prefix_majority_positive path pre move hp
  have hcoord :
      ((labelTwoPrefixSimplexPoint (t := m + 3) path
        (pre ++ [move]) hp (by omega)).u : ℤ) =
          (m + 3 : ℤ) - majorityCount (pre ++ [move]) := by
    simpa only [labelTwoPrefixPoint] using
      (labelTwoPrefixSimplexPoint_u (t := m + 3)
        path (pre ++ [move]) hp (by omega))
  omega

end BenzelProblem6Kernel

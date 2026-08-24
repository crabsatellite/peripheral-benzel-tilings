import BenzelProblem6Kernel.LiteralYPathData

/-!
# Ballot certificates carried by data-valued literal paths
-/

namespace BenzelProblem6Kernel

theorem labelZero_class_move_cases (boneClass : GoodBoneClass)
    (hlabel : boneClass.label = .zero) :
    (boneClass.ballotMove = .majority ∧ boneClass.step = stepC) ∨
      (boneClass.ballotMove = .minority ∧ boneClass.step = stepA) := by
  rcases boneClass <;>
    simp [GoodBoneClass.label, GoodBoneClass.ballotMove, GoodBoneClass.step] at hlabel ⊢

theorem LiteralEdgePathData.labelZero_ballot
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .zero)
    (hstart : first.source.u = 0) :
    IsBallotSequence (LiteralEdgePathData.ballotWord first last path) ∧
      majorityCount (LiteralEdgePathData.ballotWord first last path) -
        minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.u := by
  induction path with
  | single hedge =>
      rcases labelZero_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepC_simplex_coordinates first.source first.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority IsBallotSequence.nil
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepA_simplex_coordinates first.source first.target hanchor
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpreviousLabel : previous.boneClass.label = .zero := hsame.trans hlabel
      have ih' := ih hpreviousLabel
      simp only [majorityCount, minorityCount] at ih'
      rcases labelZero_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepC_simplex_coordinates next.source next.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority ih'.1
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepA_simplex_coordinates next.source next.target hanchor
        have hstrict :
            minorityCount (LiteralEdgePathData.ballotWord first previous path) <
              majorityCount (LiteralEdgePathData.ballotWord first previous path) := by
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          change List.count .minority
              (LiteralEdgePathData.ballotWord first previous path) <
            List.count .majority
              (LiteralEdgePathData.ballotWord first previous path)
          rw [← hmeet] at hcoords
          omega
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hminor.1] using
            IsBallotSequence.appendMinority ih'.1 hstrict
        · simp [LiteralEdgePathData.ballotWord, hminor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega

theorem labelOne_class_move_cases (boneClass : GoodBoneClass)
    (hlabel : boneClass.label = .one) :
    (boneClass.ballotMove = .majority ∧ boneClass.step = stepB) ∨
      (boneClass.ballotMove = .minority ∧ boneClass.step = stepC) := by
  rcases boneClass <;>
    simp [GoodBoneClass.label, GoodBoneClass.ballotMove, GoodBoneClass.step] at hlabel ⊢

theorem LiteralEdgePathData.labelOne_ballot
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .one)
    (hstart : first.source.v = 0) :
    IsBallotSequence (LiteralEdgePathData.ballotWord first last path) ∧
      majorityCount (LiteralEdgePathData.ballotWord first last path) -
        minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.v := by
  induction path with
  | single hedge =>
      rcases labelOne_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepB_simplex_coordinates first.source first.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority IsBallotSequence.nil
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepC_simplex_coordinates first.source first.target hanchor
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpreviousLabel : previous.boneClass.label = .one := hsame.trans hlabel
      have ih' := ih hpreviousLabel
      simp only [majorityCount, minorityCount] at ih'
      rcases labelOne_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepB_simplex_coordinates next.source next.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority ih'.1
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepC_simplex_coordinates next.source next.target hanchor
        have hstrict :
            minorityCount (LiteralEdgePathData.ballotWord first previous path) <
              majorityCount (LiteralEdgePathData.ballotWord first previous path) := by
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          change List.count .minority
              (LiteralEdgePathData.ballotWord first previous path) <
            List.count .majority
              (LiteralEdgePathData.ballotWord first previous path)
          rw [← hmeet] at hcoords
          omega
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hminor.1] using
            IsBallotSequence.appendMinority ih'.1 hstrict
        · simp [LiteralEdgePathData.ballotWord, hminor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega

theorem labelTwo_class_move_cases (boneClass : GoodBoneClass)
    (hlabel : boneClass.label = .two) :
    (boneClass.ballotMove = .majority ∧ boneClass.step = stepA) ∨
      (boneClass.ballotMove = .minority ∧ boneClass.step = stepB) := by
  rcases boneClass <;>
    simp [GoodBoneClass.label, GoodBoneClass.ballotMove, GoodBoneClass.step] at hlabel ⊢

theorem LiteralEdgePathData.labelTwo_ballot
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .two)
    (hstart : first.source.w = 0) :
    IsBallotSequence (LiteralEdgePathData.ballotWord first last path) ∧
      majorityCount (LiteralEdgePathData.ballotWord first last path) -
        minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.w := by
  induction path with
  | single hedge =>
      rcases labelTwo_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepA_simplex_coordinates first.source first.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority IsBallotSequence.nil
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepB_simplex_coordinates first.source first.target hanchor
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have hpreviousLabel : previous.boneClass.label = .two := hsame.trans hlabel
      have ih' := ih hpreviousLabel
      simp only [majorityCount, minorityCount] at ih'
      rcases labelTwo_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepA_simplex_coordinates next.source next.target hanchor
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hmajor.1] using
            IsBallotSequence.appendMajority ih'.1
        · simp [LiteralEdgePathData.ballotWord, hmajor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepB_simplex_coordinates next.source next.target hanchor
        have hstrict :
            minorityCount (LiteralEdgePathData.ballotWord first previous path) <
              majorityCount (LiteralEdgePathData.ballotWord first previous path) := by
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          change List.count .minority
              (LiteralEdgePathData.ballotWord first previous path) <
            List.count .majority
              (LiteralEdgePathData.ballotWord first previous path)
          rw [← hmeet] at hcoords
          omega
        constructor
        · simpa [LiteralEdgePathData.ballotWord, hminor.1] using
            IsBallotSequence.appendMinority ih'.1 hstrict
        · simp [LiteralEdgePathData.ballotWord, hminor.1, majorityCount,
            minorityCount]
          have hle := ih'.1.count_le
          simp only [majorityCount, minorityCount] at hle
          rw [← hmeet] at hcoords
          omega

theorem LiteralEdgePathData.labelZero_minorityCount
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .zero)
    (hstart : first.source.w = 0) :
    minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.w := by
  induction path with
  | single hedge =>
      rcases labelZero_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepC_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepA_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have ih' := ih (hsame.trans hlabel)
      simp only [minorityCount] at ih'
      rcases labelZero_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepC_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepA_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega

theorem LiteralEdgePathData.labelOne_minorityCount
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .one)
    (hstart : first.source.u = 0) :
    minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.u := by
  induction path with
  | single hedge =>
      rcases labelOne_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepB_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepC_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have ih' := ih (hsame.trans hlabel)
      simp only [minorityCount] at ih'
      rcases labelOne_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepB_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepC_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega

theorem LiteralEdgePathData.labelTwo_minorityCount
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hlabel : last.boneClass.label = .two)
    (hstart : first.source.v = 0) :
    minorityCount (LiteralEdgePathData.ballotWord first last path) =
      last.target.v := by
  induction path with
  | single hedge =>
      rcases labelTwo_class_move_cases first.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hmajor.2] at hanchor
        have hcoords := stepA_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        omega
      · have hanchor := literalDirectedEdge_anchor_step first
        rw [hminor.2] at hanchor
        have hcoords := stepB_simplex_coordinates first.source first.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        omega
  | @snoc previous next path hnext hmeet hsame ih =>
      have ih' := ih (hsame.trans hlabel)
      simp only [minorityCount] at ih'
      rcases labelTwo_class_move_cases next.boneClass hlabel with hmajor | hminor
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hmajor.2] at hanchor
        have hcoords := stepA_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hmajor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega
      · have hanchor := literalDirectedEdge_anchor_step next
        rw [hminor.2] at hanchor
        have hcoords := stepB_simplex_coordinates next.source next.target hanchor
        simp [LiteralEdgePathData.ballotWord, hminor.1, minorityCount]
        rw [← hmeet] at hcoords
        omega

end BenzelProblem6Kernel

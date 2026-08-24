import BenzelProblem6Kernel.PrefixBoneEdges

/-!
# A generic left-to-right builder for data-valued literal edge paths
-/

namespace BenzelProblem6Kernel

structure WordEdgeSystem
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (word : List BallotMove) (label : MicroLabel) where
  edge : ∀ (pre : List BallotMove) (move : BallotMove),
    pre ++ [move] <+: word → LiteralDirectedEdge m
  mem : ∀ pre move hp, edge pre move hp ∈ literalDirectedEdges hstone tiling
  edgeLabel : ∀ pre move hp, (edge pre move hp).boneClass.label = label
  edgeMove : ∀ pre move hp, (edge pre move hp).boneClass.ballotMove = move
  meet : ∀ (pre₀ : List BallotMove) (move₀ : BallotMove)
    (hp₀ : pre₀ ++ [move₀] <+: word)
    (pre₁ : List BallotMove) (move₁ : BallotMove)
    (hp₁ : pre₁ ++ [move₁] <+: word),
    pre₁ = pre₀ ++ [move₀] →
      (edge pre₀ move₀ hp₀).target = (edge pre₁ move₁ hp₁).source

theorem WordEdgeSystem.extend
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {word : List BallotMove} {label : MicroLabel}
    (system : WordEdgeSystem hstone tiling word label)
    (done rest : List BallotMove) (hword : word = done ++ rest)
    {first last : LiteralDirectedEdge m}
    (path : LiteralEdgePathData hstone tiling first last)
    (hpathWord : LiteralEdgePathData.ballotWord first last path = done)
    (hlast : ∃ (lastPre : List BallotMove) (lastMove : BallotMove)
        (hp : lastPre ++ [lastMove] <+: word),
      done = lastPre ++ [lastMove] ∧ last = system.edge lastPre lastMove hp) :
    ∃ (final : LiteralDirectedEdge m)
        (finalPath : LiteralEdgePathData hstone tiling first final),
      LiteralEdgePathData.ballotWord first final finalPath = word ∧
      ∃ (lastPre : List BallotMove) (lastMove : BallotMove)
          (hp : lastPre ++ [lastMove] <+: word),
        word = lastPre ++ [lastMove] ∧ final = system.edge lastPre lastMove hp := by
  classical
  induction rest generalizing done last with
  | nil =>
      have hdone : word = done := by simpa using hword
      obtain ⟨lastPre, lastMove, hp, hdoneLast, hlastEdge⟩ := hlast
      refine ⟨last, path, ?_, ?_⟩
      · rw [hpathWord]
        exact hdone.symm
      · exact ⟨lastPre, lastMove, hp,
          hdone.trans hdoneLast, hlastEdge⟩
  | cons move tail ih =>
      have hpNext : done ++ [move] <+: word := by
        rw [hword]
        simp [List.append_assoc]
      let next := system.edge done move hpNext
      have hnextMem : next ∈ literalDirectedEdges hstone tiling :=
        system.mem done move hpNext
      obtain ⟨lastPre, lastMove, hpLast, hdoneLast, hlastEdge⟩ := hlast
      have hmeet : last.target = next.source := by
        rw [hlastEdge]
        exact system.meet lastPre lastMove hpLast done move hpNext
          hdoneLast
      have hlabel : last.boneClass.label = next.boneClass.label := by
        rw [hlastEdge, system.edgeLabel lastPre lastMove hpLast,
          system.edgeLabel done move hpNext]
      let nextPath := LiteralEdgePathData.snoc path hnextMem hmeet hlabel
      have hnextWord : LiteralEdgePathData.ballotWord first next nextPath =
          done ++ [move] := by
        simp [nextPath, LiteralEdgePathData.ballotWord, hpathWord,
          next, system.edgeMove done move hpNext]
      have hwordNext : word = (done ++ [move]) ++ tail := by
        simpa [List.append_assoc] using hword
      have hlastNext : ∃ (lastPre : List BallotMove)
          (lastMove : BallotMove)
          (hp : lastPre ++ [lastMove] <+: word),
          done ++ [move] = lastPre ++ [lastMove] ∧
            next = system.edge lastPre lastMove hp :=
        ⟨done, move, hpNext, rfl, rfl⟩
      exact ih (done ++ [move]) hwordNext nextPath hnextWord hlastNext

theorem WordEdgeSystem.nonempty_path
    {hstone : conwayLagariasStoneCountTarget}
    {m : ℕ} {tiling : LiteralTiling m}
    {word : List BallotMove} {label : MicroLabel}
    (system : WordEdgeSystem hstone tiling word label)
    (hne : word ≠ []) :
    ∃ first last : LiteralDirectedEdge m,
      Nonempty (LiteralEdgePathData hstone tiling first last) ∧
      ∃ path : LiteralEdgePathData hstone tiling first last,
        LiteralEdgePathData.ballotWord first last path = word ∧
        ∃ (firstMove : BallotMove)
            (hpFirst : [] ++ [firstMove] <+: word),
          first = system.edge [] firstMove hpFirst ∧
        ∃ (lastPre : List BallotMove) (lastMove : BallotMove)
            (hpLast : lastPre ++ [lastMove] <+: word),
          word = lastPre ++ [lastMove] ∧
            last = system.edge lastPre lastMove hpLast := by
  classical
  have hdecomp : ∃ firstMove rest, word = firstMove :: rest := by
    cases word with
    | nil => exact (hne rfl).elim
    | cons firstMove rest => exact ⟨firstMove, rest, rfl⟩
  obtain ⟨firstMove, rest, hword⟩ := hdecomp
  have hpFirst : [] ++ [firstMove] <+: word := by rw [hword]; simp
  let first := system.edge [] firstMove hpFirst
  let firstPath := LiteralEdgePathData.single first
    (system.mem [] firstMove hpFirst)
  have hfirstWord : LiteralEdgePathData.ballotWord first first firstPath =
      [firstMove] := by
    simp [firstPath, LiteralEdgePathData.ballotWord, first,
      system.edgeMove [] firstMove hpFirst]
  have hwordTail : word = [firstMove] ++ rest := by simpa using hword
  have hlast : ∃ (lastPre : List BallotMove) (lastMove : BallotMove)
      (hp : lastPre ++ [lastMove] <+: word),
      [firstMove] = lastPre ++ [lastMove] ∧
        first = system.edge lastPre lastMove hp :=
    ⟨[], firstMove, hpFirst, rfl, rfl⟩
  obtain ⟨last, path, hpathWord, lastPre, lastMove, hpLast,
      hlastWord, hlastEdge⟩ :=
    system.extend [firstMove] rest hwordTail firstPath hfirstWord hlast
  refine ⟨first, last, ⟨path⟩, path, ?_, firstMove, hpFirst, rfl,
    lastPre, lastMove, hpLast, hlastWord, hlastEdge⟩
  exact hpathWord

end BenzelProblem6Kernel

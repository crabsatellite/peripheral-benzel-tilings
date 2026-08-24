import BenzelProblem6Kernel.PrefixBonePlacements

/-!
# Finite enumeration of all adjacent prefixes of a word
-/

namespace BenzelProblem6Kernel

def wordPrefixEdgesAux {α : Type} (pre : List α) :
    List α → List (List α × α)
  | [] => []
  | move :: rest =>
      (pre, move) :: wordPrefixEdgesAux (pre ++ [move]) rest

def wordPrefixEdges {α : Type} (word : List α) : List (List α × α) :=
  wordPrefixEdgesAux [] word

theorem wordPrefixEdgesAux_length {α : Type} (pre rest : List α) :
    (wordPrefixEdgesAux pre rest).length = rest.length := by
  induction rest generalizing pre with
  | nil => rfl
  | cons move rest ih =>
      simp [wordPrefixEdgesAux, ih]

@[simp] theorem wordPrefixEdges_length {α : Type} (word : List α) :
    (wordPrefixEdges word).length = word.length := by
  simp [wordPrefixEdges, wordPrefixEdgesAux_length]

theorem wordPrefixEdgesAux_target_prefix {α : Type} (pre rest : List α)
    (datum : List α × α)
    (hmem : datum ∈ wordPrefixEdgesAux pre rest) :
    datum.1 ++ [datum.2] <+: pre ++ rest := by
  induction rest generalizing pre with
  | nil => simp [wordPrefixEdgesAux] at hmem
  | cons move rest ih =>
      simp only [wordPrefixEdgesAux, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp
      · have hprefix := ih (pre ++ [move]) hmem
        simpa [List.append_assoc] using hprefix

theorem wordPrefixEdges_target_prefix {α : Type} (word : List α)
    (datum : List α × α) (hmem : datum ∈ wordPrefixEdges word) :
    datum.1 ++ [datum.2] <+: word := by
  simpa [wordPrefixEdges] using
    wordPrefixEdgesAux_target_prefix [] word datum hmem

theorem wordPrefixEdgesAux_mem_of_decomposition {α : Type}
    (initial middle suffix : List α) (move : α) :
    (initial ++ middle, move) ∈
      wordPrefixEdgesAux initial (middle ++ move :: suffix) := by
  induction middle generalizing initial with
  | nil => simp [wordPrefixEdgesAux]
  | cons head middle ih =>
      simp only [List.cons_append, wordPrefixEdgesAux, List.mem_cons]
      right
      simpa [List.append_assoc] using ih (initial ++ [head])

theorem wordPrefixEdges_mem_of_decomposition {α : Type}
    (word middle suffix : List α) (move : α)
    (hdecomp : word = middle ++ move :: suffix) :
    (middle, move) ∈ wordPrefixEdges word := by
  subst word
  simpa [wordPrefixEdges] using
    wordPrefixEdgesAux_mem_of_decomposition [] middle suffix move

end BenzelProblem6Kernel

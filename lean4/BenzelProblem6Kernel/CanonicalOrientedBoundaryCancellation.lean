import BenzelProblem6Kernel.OrientedBoundaryChain

/-!
# Canonical oriented trihex boundary cancellation

The three cell boundaries of each prototile are a permutation of its literal
outer boundary plus two or three exact directed-edge/reverse-edge pairs.
These are finite kernel certificates at base `(0,0)`.
-/

namespace BenzelProblem6Kernel

theorem reversePair_same_empty (edge : LabeledHexEdge) :
    SameOrientedBoundaryChain [edge, reverseLabeledHexEdge edge] [] := by
  intro target
  by_cases hforward : target = edge
  · subst target
    by_cases hloop : reverseLabeledHexEdge edge = edge
    · simp [directedEdgeCoefficient, hloop]
    · simp [directedEdgeCoefficient, hloop, Ne.symm hloop,
        reverseLabeledHexEdge_involutive]
  · by_cases hreverse : target = reverseLabeledHexEdge edge
    · subst target
      simp [directedEdgeCoefficient, hforward, Ne.symm hforward,
        reverseLabeledHexEdge_involutive]
    · have hreverseForward : reverseLabeledHexEdge target ≠ edge := by
        intro h
        apply hreverse
        simpa [reverseLabeledHexEdge_involutive] using
          congrArg reverseLabeledHexEdge h
      have hreverseReverse :
          reverseLabeledHexEdge target ≠ reverseLabeledHexEdge edge := by
        intro h
        exact hforward (reverseLabeledHexEdge_injective h)
      simp [directedEdgeCoefficient, hforward, hreverse,
        hreverseForward, hreverseReverse]

def canonicalStoneInternalPairs : List LabeledHexEdge :=
  let edge₀ : LabeledHexEdge := ⟨(0, 0), (0, 1), .b⟩
  let edge₁ : LabeledHexEdge := ⟨(-1, -1), (0, 0), .c⟩
  let edge₂ : LabeledHexEdge := ⟨(1, 0), (0, 0), .a⟩
  [edge₀, reverseLabeledHexEdge edge₀,
    edge₁, reverseLabeledHexEdge edge₁,
    edge₂, reverseLabeledHexEdge edge₂]

def canonicalBoneAInternalPairs : List LabeledHexEdge :=
  let edge₀ : LabeledHexEdge := ⟨(-1, -1), (0, 0), .c⟩
  let edge₁ : LabeledHexEdge := ⟨(0, -2), (1, -1), .c⟩
  [edge₀, reverseLabeledHexEdge edge₀,
    edge₁, reverseLabeledHexEdge edge₁]

def canonicalBoneBInternalPairs : List LabeledHexEdge :=
  let edge₀ : LabeledHexEdge := ⟨(0, 0), (0, 1), .b⟩
  let edge₁ : LabeledHexEdge := ⟨(2, 1), (2, 2), .b⟩
  [edge₀, reverseLabeledHexEdge edge₀,
    edge₁, reverseLabeledHexEdge edge₁]

def canonicalBoneCInternalPairs : List LabeledHexEdge :=
  let edge₀ : LabeledHexEdge := ⟨(-2, -1), (-1, -1), .a⟩
  let edge₁ : LabeledHexEdge := ⟨(-3, -3), (-2, -3), .a⟩
  [edge₀, reverseLabeledHexEdge edge₀,
    edge₁, reverseLabeledHexEdge edge₁]

def canonicalInternalPairs : ProtoTile → List LabeledHexEdge
  | .stone => canonicalStoneInternalPairs
  | .boneA => canonicalBoneAInternalPairs
  | .boneB => canonicalBoneBInternalPairs
  | .boneC => canonicalBoneCInternalPairs

theorem canonicalInternalPairs_same_empty (tile : ProtoTile) :
    SameOrientedBoundaryChain (canonicalInternalPairs tile) [] := by
  cases tile
  · exact (reversePair_same_empty
      ⟨(0, 0), (0, 1), .b⟩).append
        ((reversePair_same_empty
          ⟨(-1, -1), (0, 0), .c⟩).append
          (reversePair_same_empty ⟨(1, 0), (0, 0), .a⟩))
  · exact (reversePair_same_empty
      ⟨(-1, -1), (0, 0), .c⟩).append
        (reversePair_same_empty ⟨(0, -2), (1, -1), .c⟩)
  · exact (reversePair_same_empty
      ⟨(0, 0), (0, 1), .b⟩).append
        (reversePair_same_empty ⟨(2, 1), (2, 2), .b⟩)
  · exact (reversePair_same_empty
      ⟨(-2, -1), (-1, -1), .a⟩).append
        (reversePair_same_empty ⟨(-3, -3), (-2, -3), .a⟩)

theorem canonical_stone_oriented_perm :
    List.Perm (orientedPrototypeCellBoundaryList .stone (0, 0))
      (literalPrototypeBoundary .stone (0, 0) ++
        canonicalInternalPairs .stone) := by
  decide

theorem canonical_boneA_oriented_perm :
    List.Perm (orientedPrototypeCellBoundaryList .boneA (0, 0))
      (literalPrototypeBoundary .boneA (0, 0) ++
        canonicalInternalPairs .boneA) := by
  decide

theorem canonical_boneB_oriented_perm :
    List.Perm (orientedPrototypeCellBoundaryList .boneB (0, 0))
      (literalPrototypeBoundary .boneB (0, 0) ++
        canonicalInternalPairs .boneB) := by
  decide

theorem canonical_boneC_oriented_perm :
    List.Perm (orientedPrototypeCellBoundaryList .boneC (0, 0))
      (literalPrototypeBoundary .boneC (0, 0) ++
        canonicalInternalPairs .boneC) := by
  decide

theorem canonical_oriented_perm (tile : ProtoTile) :
    List.Perm (orientedPrototypeCellBoundaryList tile (0, 0))
      (literalPrototypeBoundary tile (0, 0) ++
        canonicalInternalPairs tile) := by
  cases tile
  · exact canonical_stone_oriented_perm
  · exact canonical_boneA_oriented_perm
  · exact canonical_boneB_oriented_perm
  · exact canonical_boneC_oriented_perm

theorem canonical_oriented_boundary_cancel (tile : ProtoTile) :
    SameOrientedBoundaryChain
      (orientedPrototypeCellBoundaryList tile (0, 0))
      (literalPrototypeBoundary tile (0, 0)) := by
  have htail := (SameOrientedBoundaryChain.refl
    (literalPrototypeBoundary tile (0, 0))).append
      (canonicalInternalPairs_same_empty tile)
  exact (SameOrientedBoundaryChain.perm
    (canonical_oriented_perm tile)).trans (by simpa using htail)

end BenzelProblem6Kernel

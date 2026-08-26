import FiniteDefects.D4DefectParameterEquiv

/-! # Explicit finite carriers for the exact d=4 count -/

namespace FiniteDefects

abbrev D4DefectParameterSum (m : ℕ) :=
  SimplexPoint m ⊕
    (SimplexPoint (m + 1) ⊕
      (SimplexPoint m ⊕ (SimplexPoint m ⊕ SimplexPoint m)))

def d4DefectParameterEquivSum (m : ℕ) :
    D4DefectParameter m ≃ D4DefectParameterSum m where
  toFun
    | .stone1 p => .inl p
    | .stone2 p => .inr (.inl p)
    | .boneA p => .inr (.inr (.inl p))
    | .boneB p => .inr (.inr (.inr (.inl p)))
    | .boneC p => .inr (.inr (.inr (.inr p)))
  invFun
    | .inl p => .stone1 p
    | .inr (.inl p) => .stone2 p
    | .inr (.inr (.inl p)) => .boneA p
    | .inr (.inr (.inr (.inl p))) => .boneB p
    | .inr (.inr (.inr (.inr p))) => .boneC p
  left_inv := by intro parameter; rcases parameter <;> rfl
  right_inv := by
    intro parameter
    rcases parameter with p | p
    · rfl
    · rcases p with p | p
      · rfl
      · rcases p with p | p
        · rfl
        · rcases p <;> rfl

noncomputable def d4DefectParameterFintype (m : ℕ) :
    Fintype (D4DefectParameter m) :=
  Fintype.ofEquiv (D4DefectParameterSum m)
    (d4DefectParameterEquivSum m).symm

noncomputable def d4DefectPlacementFintype (m : ℕ) :
    Fintype (D4DefectPlacement m) := by
  letI := d4DefectParameterFintype m
  exact Fintype.ofEquiv (D4DefectParameter m)
    (d4DefectPlacementEquivParameter m).symm

noncomputable def d4SigmaArmTripleFintype (m : ℕ) :
    Fintype (Σ defect : D4DefectPlacement m, D4ArmTriple m defect) := by
  letI := d4DefectPlacementFintype m
  letI (defect : D4DefectPlacement m) := d4ArmTripleFintype defect
  exact inferInstance

noncomputable def d4LiteralTilingCountingFintype (m : ℕ) :
    Fintype (D4LiteralTiling m) := by
  letI := d4SigmaArmTripleFintype m
  exact Fintype.ofEquiv
    (Σ defect : D4DefectPlacement m, D4ArmTriple m defect)
    (d4LiteralTilingEquivSigmaArmTriple m).symm

end FiniteDefects

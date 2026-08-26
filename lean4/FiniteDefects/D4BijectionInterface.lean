import FiniteDefects.D4PathSeparation

/-! # Exact public interface for the literal d=4 bijection -/

namespace FiniteDefects

structure D4LiteralBijectionEvidence : Prop where
  literal_equiv : ∀ m : ℕ, Nonempty (D4LiteralTiling m ≃ D4DefectPathData m)
  zero_one_disjoint : ∀ {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2)),
    D4AbstractPathVisits (d4BoundaryOwner m .zero)
      (data.defect.core .zero) (data.paths .zero) p →
    D4AbstractPathVisits (d4BoundaryOwner m .one)
      (data.defect.core .one) (data.paths .one) p → False
  one_two_disjoint : ∀ {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2)),
    D4AbstractPathVisits (d4BoundaryOwner m .one)
      (data.defect.core .one) (data.paths .one) p →
    D4AbstractPathVisits (d4BoundaryOwner m .two)
      (data.defect.core .two) (data.paths .two) p → False
  two_zero_disjoint : ∀ {m : ℕ} (data : D4DefectPathData m)
    (p : SimplexPoint (m + 2)),
    D4AbstractPathVisits (d4BoundaryOwner m .two)
      (data.defect.core .two) (data.paths .two) p →
    D4AbstractPathVisits (d4BoundaryOwner m .zero)
      (data.defect.core .zero) (data.paths .zero) p → False

end FiniteDefects

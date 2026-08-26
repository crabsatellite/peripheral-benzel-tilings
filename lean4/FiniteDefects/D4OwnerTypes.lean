import FiniteDefects.D4CoveringRoles

/-! # Full owners and the three one-cell boundary endpoints -/

namespace FiniteDefects

def d4BoundaryOwner (m : ℕ) : MicroLabel → SimplexPoint (m + 2)
  | .zero => cornerW (m + 2)
  | .one => cornerU (m + 2)
  | .two => cornerV (m + 2)

theorem d4BoundaryOwner_present_iff (m : ℕ)
    (endpointLabel label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4)
        (ownerCell (d4BoundaryOwner m endpointLabel) label) ↔
      label = endpointLabel := by
  rw [d4_owner_label_mem_iff]
  rcases endpointLabel <;> rcases label <;>
    simp [d4BoundaryOwner, d3k1LabelPresent, cornerU, cornerV, cornerW]

theorem d4BoundaryOwner_present (m : ℕ) (label : MicroLabel) :
    inBenzel (m + 4) (2 * m + 4)
      (ownerCell (d4BoundaryOwner m label) label) :=
  (d4BoundaryOwner_present_iff m label label).2 rfl

theorem d4BoundaryOwner_injective (m : ℕ) :
    Function.Injective (d4BoundaryOwner m) := by
  intro left right h
  rcases left <;> rcases right <;>
    simp_all [d4BoundaryOwner, cornerU, cornerV, cornerW]

def IsD4FullOwner {m : ℕ} (p : SimplexPoint (m + 2)) : Prop :=
  ∀ label, inBenzel (m + 4) (2 * m + 4) (ownerCell p label)

theorem d4_interior_is_full {m : ℕ} (p : SimplexPoint (m + 2))
    (hu : p.u < m + 2) (hv : p.v < m + 2) (hw : p.w < m + 2) :
    IsD4FullOwner p := by
  intro label
  rw [d4_owner_label_mem_iff]
  have hu' : p.u ≤ m + 1 := by omega
  have hv' : p.v ≤ m + 1 := by omega
  have hw' : p.w ≤ m + 1 := by omega
  have hsub : m + 2 - 1 = m + 1 := by omega
  rcases label <;> simp [d3k1LabelPresent, hsub, hu', hv', hw'] <;> omega

theorem d4_owner_full_or_boundary {m : ℕ}
    (p : SimplexPoint (m + 2)) :
    IsD4FullOwner p ∨ ∃ label, p = d4BoundaryOwner m label := by
  rcases simplex_corner_or_interior p with rfl | rfl | rfl | hinterior
  · right
    exact ⟨.one, rfl⟩
  · right
    exact ⟨.two, rfl⟩
  · right
    exact ⟨.zero, rfl⟩
  · left
    exact d4_interior_is_full p hinterior.1 hinterior.2.1 hinterior.2.2

theorem d4_not_full_iff_boundary {m : ℕ}
    (p : SimplexPoint (m + 2)) :
    ¬IsD4FullOwner p ↔ ∃ label, p = d4BoundaryOwner m label := by
  constructor
  · intro hnotfull
    rcases d4_owner_full_or_boundary p with hfull | hboundary
    · exact (hnotfull hfull).elim
    · exact hboundary
  · rintro ⟨endpointLabel, rfl⟩ hfull
    obtain ⟨other, hne⟩ : ∃ other : MicroLabel, other ≠ endpointLabel := by
      rcases endpointLabel
      · exact ⟨.one, by decide⟩
      · exact ⟨.two, by decide⟩
      · exact ⟨.zero, by decide⟩
    exact hne ((d4BoundaryOwner_present_iff m endpointLabel other).1
      (hfull other))

theorem d4_boundary_owner_label_unique {m : ℕ}
    (p : SimplexPoint (m + 2)) (endpointLabel label : MicroLabel)
    (hp : p = d4BoundaryOwner m endpointLabel)
    (hpresent : inBenzel (m + 4) (2 * m + 4) (ownerCell p label)) :
    label = endpointLabel := by
  subst p
  exact (d4BoundaryOwner_present_iff m endpointLabel label).1 hpresent

end FiniteDefects

import BenzelProblem6Kernel.ReverseBonePlacement

/-!
# Reconstructing one in-phase stone at an unused full owner
-/

namespace BenzelProblem6Kernel

theorem stone_local_cell_eq_owner {t : ℕ} (owner : SimplexPoint t)
    (localCell : LocalCell) (hlocal : localCell ∈ protoCells .stone) :
    translateLocalCell (ownerQ owner, ownerR owner) localCell =
      ownerCell owner (localLabel .r0 localCell) := by
  rw [ownerCell_eq_cellForOwnerAnchor]
  simp [protoCells] at hlocal
  rcases hlocal with rfl | rfl | rfl <;>
    simp [translateLocalCell, localLabel, Res3.add, Res3.toLabel,
      cellForOwnerAnchor, c00, c10, c01]

noncomputable def reverseStonePlacement {m : ℕ}
    (owner : SimplexPoint (m + 3))
    (hu : owner.u < m + 3) (hv : owner.v < m + 3) (hw : owner.w < m + 3) :
    LiteralPlacement m := by
  let base : Cell := (ownerQ owner, ownerR owner)
  have hzero := (owner_zero_mem_iff (n := m + 5) (by omega) owner).2 hv
  have hone := (owner_one_mem_iff (n := m + 5) (by omega) owner).2 hw
  have htwo := (owner_two_mem_iff (n := m + 5) (by omega) owner).2 hu
  have hall : ∀ localCell ∈ protoCells .stone,
      inPeripheralBenzel (m + 5) (translateLocalCell base localCell) := by
    intro localCell hlocal
    rw [stone_local_cell_eq_owner owner localCell hlocal]
    rcases hlabel : localLabel .r0 localCell with _ | _ | _
    · exact hzero
    · exact hone
    · exact htwo
  have hbaseMem : inPeripheralBenzel (m + 5) base := by
    have h := hall c00 (by simp [protoCells])
    simpa [base, translateLocalCell, c00] using h
  let baseCell : BenzelCell (m + 5) := ⟨base, hbaseMem⟩
  let candidate : PlacementCandidate m := (.stone, baseCell)
  exact ⟨candidate, by
    intro cell hcell
    change cell ∈ (protoCells .stone).map (translateLocalCell base) at hcell
    simp only [List.mem_map] at hcell
    obtain ⟨localCell, hlocal, rfl⟩ := hcell
    exact hall localCell hlocal⟩

end BenzelProblem6Kernel

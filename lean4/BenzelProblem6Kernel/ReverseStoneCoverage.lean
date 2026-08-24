import BenzelProblem6Kernel.ReverseBoneCoverage
import BenzelProblem6Kernel.ReverseStonePlacement

/-!
# Exact owner role of a reconstructed stone
-/

namespace BenzelProblem6Kernel

@[simp] theorem reverseStonePlacement_tile {m : ℕ}
    (owner : SimplexPoint (m + 3))
    (hu : owner.u < m + 3) (hv : owner.v < m + 3)
    (hw : owner.w < m + 3) :
    (reverseStonePlacement owner hu hv hw).tile = .stone := by
  rfl

@[simp] theorem reverseStonePlacement_base {m : ℕ}
    (owner : SimplexPoint (m + 3))
    (hu : owner.u < m + 3) (hv : owner.v < m + 3)
    (hw : owner.w < m + 3) :
    (reverseStonePlacement owner hu hv hw).base =
      (ownerQ owner, ownerR owner) := by
  rfl

theorem reverseStonePlacement_covers_label {m : ℕ}
    (owner : SimplexPoint (m + 3))
    (hu : owner.u < m + 3) (hv : owner.v < m + 3)
    (hw : owner.w < m + 3) (label : MicroLabel) :
    let hmem : inPeripheralBenzel (m + 5) (ownerCell owner label) := by
      rcases label with _ | _ | _
      · exact (owner_zero_mem_iff (n := m + 5) (by omega) owner).2 hv
      · exact (owner_one_mem_iff (n := m + 5) (by omega) owner).2 hw
      · exact (owner_two_mem_iff (n := m + 5) (by omega) owner).2 hu
    PlacementCovers (reverseStonePlacement owner hu hv hw)
      ⟨ownerCell owner label, hmem⟩ := by
  dsimp
  change ownerCell owner label ∈
    (protoCells ProtoTile.stone).map
      (translateLocalCell (ownerQ owner, ownerR owner))
  rcases label with _ | _ | _
  · have heq := stone_local_cell_eq_owner owner c00 (by simp [protoCells])
    have heq' : translateLocalCell (ownerQ owner, ownerR owner) c00 =
        ownerCell owner .zero := by
      simpa [localLabel, Res3.add, Res3.toLabel, c00] using heq
    rw [← heq']
    simp [protoCells]
  · have heq := stone_local_cell_eq_owner owner c10 (by simp [protoCells])
    have heq' : translateLocalCell (ownerQ owner, ownerR owner) c10 =
        ownerCell owner .one := by
      simpa [localLabel, Res3.add, Res3.toLabel, c10] using heq
    rw [← heq']
    simp [protoCells]
  · have heq := stone_local_cell_eq_owner owner c01 (by simp [protoCells])
    have heq' : translateLocalCell (ownerQ owner, ownerR owner) c01 =
        ownerCell owner .two := by
      simpa [localLabel, Res3.add, Res3.toLabel, c01] using heq
    rw [← heq']
    simp [protoCells]

theorem reverseStonePlacement_cover_role {m : ℕ}
    (owner : SimplexPoint (m + 3))
    (hu : owner.u < m + 3) (hv : owner.v < m + 3)
    (hw : owner.w < m + 3) (cell : Cell)
    (hcover : cell ∈ (reverseStonePlacement owner hu hv hw).cells) :
    ∃ label, cell = ownerCell owner label := by
  change cell ∈ (protoCells ProtoTile.stone).map
    (translateLocalCell (ownerQ owner, ownerR owner)) at hcover
  simp only [List.mem_map] at hcover
  obtain ⟨localCell, hlocal, rfl⟩ := hcover
  exact ⟨localLabel .r0 localCell,
    stone_local_cell_eq_owner owner localCell hlocal⟩

theorem reverseStonePlacement_eq_stoneOwner
    (hstone : conwayLagariasStoneCountTarget)
    {m : ℕ} (tiling : LiteralTiling m)
    (placement : {p // p ∈ stonePlacementFinset tiling})
    (owner : SimplexPoint (m + 3))
    (howner : stoneOwner hstone tiling placement = owner)
    (hu : owner.u < m + 3) (hv : owner.v < m + 3)
    (hw : owner.w < m + 3) :
    reverseStonePlacement owner hu hv hw = placement.1 := by
  apply Subtype.ext
  apply Prod.ext
  · have hp := placement.2
    simp only [stonePlacementFinset, Finset.mem_filter] at hp
    exact hp.2.symm
  · apply Subtype.ext
    change (ownerQ owner, ownerR owner) = placement.1.base
    rw [← howner, (stoneOwner_anchor hstone tiling placement).1,
      (stoneOwner_anchor hstone tiling placement).2]

end BenzelProblem6Kernel

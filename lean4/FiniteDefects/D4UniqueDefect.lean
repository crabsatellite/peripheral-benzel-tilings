import FiniteDefects.D4BoneEdges
import Mathlib.Data.Finset.Card

/-! # The unique bad placement in every d=4 tiling -/

namespace FiniteDefects

def IsD4BadPlacement {m : ℕ} (placement : D4LiteralPlacement m) : Prop :=
  IsD4WrongPhaseStone placement ∨ IsD4ThreeOwnerBone placement

noncomputable instance isD4BadPlacementDecidable {m : ℕ}
    (placement : D4LiteralPlacement m) :
    Decidable (IsD4BadPlacement placement) := Classical.propDecidable _

theorem d4_wrong_not_three_owner {m : ℕ}
    (placement : D4LiteralPlacement m) :
    IsD4WrongPhaseStone placement → ¬IsD4ThreeOwnerBone placement := by
  intro hwrong
  rcases htile : placement.tile with _ | _ | _ | _
  · simp [IsD4ThreeOwnerBone, htile]
  all_goals simp [IsD4WrongPhaseStone, htile] at hwrong

theorem d4_bad_filter_card
    (hCL : D4ConwayLagariasStatement) {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (tiling.1.filter IsD4BadPlacement).card = 1 := by
  have hdisjoint :
      Disjoint (tiling.1.filter IsD4WrongPhaseStone)
        (tiling.1.filter IsD4ThreeOwnerBone) := by
    rw [Finset.disjoint_left]
    intro placement hwrong hthree
    simp only [Finset.mem_filter] at hwrong hthree
    exact d4_wrong_not_three_owner placement hwrong.2 hthree.2
  rw [show tiling.1.filter IsD4BadPlacement =
      tiling.1.filter IsD4WrongPhaseStone ∪
        tiling.1.filter IsD4ThreeOwnerBone by
    ext placement
    simp only [Finset.mem_filter, Finset.mem_union, IsD4BadPlacement]
    constructor
    · rintro ⟨hmem, hwrong | hthree⟩
      · exact Or.inl ⟨hmem, hwrong⟩
      · exact Or.inr ⟨hmem, hthree⟩
    · rintro (⟨hmem, hwrong⟩ | ⟨hmem, hthree⟩)
      · exact ⟨hmem, Or.inl hwrong⟩
      · exact ⟨hmem, Or.inr hthree⟩]
  rw [Finset.card_union_of_disjoint hdisjoint]
  exact d4_exactly_one_defect hCL tiling

theorem d4_bad_filter_card_reference {m : ℕ}
    (tiling : D4LiteralTiling m) :
    (tiling.1.filter IsD4BadPlacement).card = 1 :=
  d4_bad_filter_card d4ConwayLagariasReference tiling

noncomputable def d4BadPlacement {m : ℕ}
    (tiling : D4LiteralTiling m) : D4LiteralPlacement m :=
  (Finset.card_eq_one.mp (d4_bad_filter_card_reference tiling)).choose

theorem d4_bad_filter_eq_singleton {m : ℕ}
    (tiling : D4LiteralTiling m) :
    tiling.1.filter IsD4BadPlacement = {d4BadPlacement tiling} :=
  (Finset.card_eq_one.mp (d4_bad_filter_card_reference tiling)).choose_spec

theorem d4BadPlacement_mem {m : ℕ} (tiling : D4LiteralTiling m) :
    d4BadPlacement tiling ∈ tiling.1 := by
  have hmem : d4BadPlacement tiling ∈
      tiling.1.filter IsD4BadPlacement := by
    rw [d4_bad_filter_eq_singleton]
    simp
  exact (Finset.mem_filter.mp hmem).1

theorem d4BadPlacement_isBad {m : ℕ} (tiling : D4LiteralTiling m) :
    IsD4BadPlacement (d4BadPlacement tiling) := by
  have hmem : d4BadPlacement tiling ∈
      tiling.1.filter IsD4BadPlacement := by
    rw [d4_bad_filter_eq_singleton]
    simp
  exact (Finset.mem_filter.mp hmem).2

theorem d4BadPlacement_unique {m : ℕ} (tiling : D4LiteralTiling m)
    (placement : D4LiteralPlacement m)
    (hmem : placement ∈ tiling.1)
    (hbad : IsD4BadPlacement placement) :
    placement = d4BadPlacement tiling := by
  have hfilter : placement ∈ tiling.1.filter IsD4BadPlacement :=
    Finset.mem_filter.mpr ⟨hmem, hbad⟩
  rw [d4_bad_filter_eq_singleton] at hfilter
  simpa using hfilter

theorem d4_nonbad_is_good_bone_or_stone {m : ℕ}
    (placement : D4LiteralPlacement m)
    (hnotbad : ¬IsD4BadPlacement placement) :
    (placement.tile = .stone ∧
      placementBaseResidue (m + 2) placement.base = .r0) ∨
    (placement.tile ≠ .stone ∧ ¬IsD4ThreeOwnerBone placement) := by
  by_cases hstone : placement.tile = .stone
  · left
    refine ⟨hstone, ?_⟩
    by_contra hphase
    exact hnotbad (Or.inl ⟨hstone, hphase⟩)
  · right
    refine ⟨hstone, ?_⟩
    intro hthree
    exact hnotbad (Or.inr hthree)

end FiniteDefects

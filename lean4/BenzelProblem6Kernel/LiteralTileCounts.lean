import BenzelProblem6Kernel.TilingIncidence
import Mathlib.Data.Finset.Card

/-!
# Stone and bone counts in a literal tiling
-/

namespace BenzelProblem6Kernel

def rightStoneCount {m : ℕ} (tiling : LiteralTiling m) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = .stone).card

def boneCount {m : ℕ} (tiling : LiteralTiling m) : ℕ :=
  (tiling.1.filter fun placement => placement.tile ≠ .stone).card

theorem rightStoneCount_add_boneCount {m : ℕ} (tiling : LiteralTiling m) :
    rightStoneCount tiling + boneCount tiling = tiling.1.card := by
  simpa [rightStoneCount, boneCount] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := tiling.1)
      (fun placement : LiteralPlacement m => placement.tile = .stone))

def conwayLagariasStoneCountTarget : Prop :=
  ∀ (m : ℕ) (tiling : LiteralTiling m),
    rightStoneCount tiling = m * (m + 3) / 2

theorem two_dvd_stone_product (m : ℕ) : 2 ∣ m * (m + 3) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · refine ⟨k * (2 * k + 3), ?_⟩
    ring
  · refine ⟨(2 * k + 1) * (k + 2), ?_⟩
    ring

theorem boneCount_of_conwayLagarias
    (hstone : conwayLagariasStoneCountTarget)
    (m : ℕ) (tiling : LiteralTiling m) :
    boneCount tiling = 3 * (m + 3) := by
  have hpartition := rightStoneCount_add_boneCount tiling
  rw [hstone m tiling, literal_tiling_card tiling] at hpartition
  have hevenStone := two_dvd_stone_product m
  have hevenTotal := two_dvd_tile_product m
  apply Nat.cast_injective (R := ℚ)
  have hpartitionQ :
      ((m * (m + 3) / 2 : ℕ) : ℚ) + (boneCount tiling : ℚ) =
        (((m + 3) * (m + 6) / 2 : ℕ) : ℚ) := by
    exact_mod_cast hpartition
  rw [Nat.cast_div hevenStone (by norm_num : (2 : ℚ) ≠ 0),
    Nat.cast_div hevenTotal (by norm_num : (2 : ℚ) ≠ 0)] at hpartitionQ
  push_cast at hpartitionQ ⊢
  nlinarith

end BenzelProblem6Kernel

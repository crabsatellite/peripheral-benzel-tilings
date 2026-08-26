import D4KernelOnly.GeneralBoneCountKernelOnly
import FiniteDefects.D4FiniteDefect

/-! # Exact bridge from the arbitrary-offset carrier to the d=4 carrier -/

namespace FiniteDefects

theorem offsetD4LiteralTiling_type_eq (m : ℕ) :
    OffsetLiteralTiling (m + 2) 4 = D4LiteralTiling m := by
  rfl

def offsetD4LiteralTilingEquiv (m : ℕ) :
    OffsetLiteralTiling (m + 2) 4 ≃ D4LiteralTiling m :=
  Equiv.cast (offsetD4LiteralTiling_type_eq m)

@[simp] theorem offsetD4LiteralTilingEquiv_apply
    {m : ℕ} (tiling : OffsetLiteralTiling (m + 2) 4) :
    offsetD4LiteralTilingEquiv m tiling = tiling := by
  rfl

@[simp] theorem offsetD4LiteralTilingEquiv_symm_apply
    {m : ℕ} (tiling : D4LiteralTiling m) :
    (offsetD4LiteralTilingEquiv m).symm tiling = tiling := by
  rfl

theorem offsetD4_wrongPhaseStoneCount_eq
    {m : ℕ} (tiling : D4LiteralTiling m) :
    offsetWrongPhaseStoneCount ((offsetD4LiteralTilingEquiv m).symm tiling) =
      d4WrongPhaseStoneCount tiling := by
  rfl

theorem offsetD4_threeOwnerBoneCount_eq
    {m : ℕ} (tiling : D4LiteralTiling m) :
    offsetThreeOwnerBoneCount ((offsetD4LiteralTilingEquiv m).symm tiling) =
      d4ThreeOwnerBoneCount tiling := by
  rfl

theorem d4OneDefect_from_generalFiniteDefect : D4OneDefectStatement := by
  intro m tiling
  have h := generalFiniteDefectKernelOnly.2 (m + 2) 1 (by omega) (by omega)
    ((offsetD4LiteralTilingEquiv m).symm tiling)
  rw [offsetD4_wrongPhaseStoneCount_eq,
    offsetD4_threeOwnerBoneCount_eq] at h
  norm_num at h
  exact h

end FiniteDefects

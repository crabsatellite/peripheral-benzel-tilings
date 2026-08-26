import D4KernelOnly.GeneralClassZeroBoneCount
import D4KernelOnly.GeneralFiniteDefectConsumer

/-! # Premise-free producer for the full Conway--Lagarias bone count -/

namespace FiniteDefects

theorem offsetBoneCount_transport
    {t t' d : ℕ} (h : t = t') (tiling : OffsetLiteralTiling t d) :
    offsetBoneCount (h ▸ tiling) = offsetBoneCount tiling := by
  subst t'
  rfl

theorem generalBoneCountKernelOnly : GeneralBoneCountStatement := by
  constructor
  · intro t k hk hroom tiling
    let r := t + 2 - 2 * k
    have hr : 1 ≤ r := by
      dsimp [r]
      omega
    have ht : 2 * k + r - 2 = t := by
      dsimp [r]
      omega
    let tiling' : CZLiteralTiling k r :=
      @Eq.ndrec ℕ t (fun n => OffsetLiteralTiling n (3 * k))
        tiling (2 * k + r - 2) ht.symm
    have hb := cz_bone_count_kernelOnly hk hr tiling'
    have htransport : offsetBoneCount tiling' = offsetBoneCount tiling := by
      simpa [tiling'] using offsetBoneCount_transport ht.symm tiling
    calc
      offsetBoneCount tiling = offsetBoneCount tiling' := htransport.symm
      _ = 3 * k * r := hb
      _ = 3 * k * (t + 2 - 2 * k) := by rfl
  · intro t k hk hroom tiling
    let r := t + 1 - 2 * k
    have ht : 2 * k + r - 1 = t := by
      dsimp [r]
      omega
    let tiling' : CMOLiteralTiling k r :=
      @Eq.ndrec ℕ t (fun n => OffsetLiteralTiling n (3 * k + 1))
        tiling (2 * k + r - 1) ht.symm
    have hb := cmo_bone_count_kernelOnly hk tiling'
    have htransport : offsetBoneCount tiling' = offsetBoneCount tiling := by
      simpa [tiling'] using offsetBoneCount_transport ht.symm tiling
    calc
      offsetBoneCount tiling = offsetBoneCount tiling' := htransport.symm
      _ = 3 * k * r := hb
      _ = 3 * k * (t + 1 - 2 * k) := by rfl

theorem generalFiniteDefectKernelOnly : GeneralFiniteDefectStatement :=
  generalFiniteDefect_of_boneCount generalBoneCountKernelOnly

end FiniteDefects

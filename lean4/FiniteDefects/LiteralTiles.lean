import FiniteDefects.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-! # Literal type-103 prototiles and their phase energy table -/

namespace FiniteDefects

inductive Res3
  | r0
  | r1
  | r2
  deriving DecidableEq, Repr

def Res3.add : Res3 → Res3 → Res3
  | .r0, b => b
  | a, .r0 => a
  | .r1, .r1 => .r2
  | .r1, .r2 => .r0
  | .r2, .r1 => .r0
  | .r2, .r2 => .r1

def Res3.toLabel : Res3 → MicroLabel
  | .r0 => .zero
  | .r1 => .one
  | .r2 => .two

def Res3.value : Res3 → ℤ
  | .r0 => 0
  | .r1 => 1
  | .r2 => 2

structure LocalCell where
  dx : ℤ
  dy : ℤ
  deltaResidue : Res3
  deriving DecidableEq, Repr

def c00 : LocalCell := ⟨0, 0, .r0⟩
def c10 : LocalCell := ⟨1, 0, .r1⟩
def c20 : LocalCell := ⟨2, 0, .r2⟩
def c01 : LocalCell := ⟨0, 1, .r2⟩
def c02 : LocalCell := ⟨0, 2, .r1⟩
def c1m1 : LocalCell := ⟨1, -1, .r2⟩
def c2m2 : LocalCell := ⟨2, -2, .r1⟩

inductive ProtoTile
  | stone
  | boneA
  | boneB
  | boneC
  deriving DecidableEq, Repr

def protoCells : ProtoTile → List LocalCell
  | .stone => [c00, c10, c01]
  | .boneA => [c00, c10, c20]
  | .boneB => [c00, c01, c02]
  | .boneC => [c00, c1m1, c2m2]

def translateLocalCell (base : Cell) (offset : LocalCell) : Cell :=
  (base.1 + offset.dx, base.2 + offset.dy)

def localLabel (baseResidue : Res3) (cell : LocalCell) : MicroLabel :=
  (Res3.add baseResidue cell.deltaResidue).toLabel

def ownerShift (baseResidue : Res3) (cell : LocalCell) : Cell :=
  match localLabel baseResidue cell with
  | .zero => (cell.dx, cell.dy)
  | .one => (cell.dx - 1, cell.dy)
  | .two => (cell.dx, cell.dy - 1)

def localCellEnergy (baseQ baseR : ℤ) (baseResidue : Res3)
    (cell : LocalCell) : ℤ :=
  let shift := ownerShift baseResidue cell
  ownerPotential (localLabel baseResidue cell)
    (baseQ + shift.1) (baseR + shift.2)

def literalTileEnergy (tile : ProtoTile) (baseQ baseR : ℤ)
    (baseResidue : Res3) : ℤ :=
  ((protoCells tile).map (localCellEnergy baseQ baseR baseResidue)).sum

theorem stone_energy_by_residue (q r : ℤ) :
    literalTileEnergy .stone q r .r0 = 0 ∧
    literalTileEnergy .stone q r .r1 = 3 ∧
    literalTileEnergy .stone q r .r2 = 3 := by
  simp [literalTileEnergy, protoCells, localCellEnergy, ownerShift,
    localLabel, Res3.add, Res3.toLabel, c00, c10, c01, ownerPotential]
  ring_nf
  simp

theorem boneA_energy_by_residue (q r : ℤ) :
    literalTileEnergy .boneA q r .r0 = 1 ∧
    literalTileEnergy .boneA q r .r1 = 4 ∧
    literalTileEnergy .boneA q r .r2 = 1 := by
  simp [literalTileEnergy, protoCells, localCellEnergy, ownerShift,
    localLabel, Res3.add, Res3.toLabel, c00, c10, c20, ownerPotential]
  ring_nf
  simp

theorem boneB_energy_by_residue (q r : ℤ) :
    literalTileEnergy .boneB q r .r0 = 1 ∧
    literalTileEnergy .boneB q r .r1 = 1 ∧
    literalTileEnergy .boneB q r .r2 = 4 := by
  simp [literalTileEnergy, protoCells, localCellEnergy, ownerShift,
    localLabel, Res3.add, Res3.toLabel, c00, c01, c02, ownerPotential]
  ring_nf
  simp

theorem boneC_energy_by_residue (q r : ℤ) :
    literalTileEnergy .boneC q r .r0 = 1 ∧
    literalTileEnergy .boneC q r .r1 = 4 ∧
    literalTileEnergy .boneC q r .r2 = 1 := by
  simp [literalTileEnergy, protoCells, localCellEnergy, ownerShift,
    localLabel, Res3.add, Res3.toLabel, c00, c1m1, c2m2, ownerPotential]
  ring_nf
  simp

def residueOfInt (x : ℤ) : Res3 :=
  if x % 3 = 0 then .r0 else if x % 3 = 1 then .r1 else .r2

def placementBaseResidue (t : ℕ) (base : Cell) : Res3 :=
  residueOfInt (base.1 - base.2 - (t : ℤ))

def BaseHasResidue (t : ℕ) (base : Cell) (rho : Res3) : Prop :=
  base.1 - base.2 ≡ (t : ℤ) + rho.value [ZMOD 3]

theorem base_residue_of_remainder {t : ℕ} {q r k : ℤ}
    (hrem : (q - r - (t : ℤ)) % 3 = k) (hk : k % 3 = k) :
    q - r ≡ (t : ℤ) + k [ZMOD 3] := by
  have hx : q - r - (t : ℤ) ≡ k [ZMOD 3] := by
    rw [Int.ModEq]
    simp [hrem, hk]
  have hadd := hx.add_right (t : ℤ)
  convert hadd using 1 <;> ring

theorem placementBaseResidue_spec (t : ℕ) (base : Cell) :
    BaseHasResidue t base (placementBaseResidue t base) := by
  let x : ℤ := base.1 - base.2 - (t : ℤ)
  have hx_nonneg : 0 ≤ x % 3 := Int.emod_nonneg _ (by norm_num)
  have hx_lt : x % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  by_cases hzero : x % 3 = 0
  · simpa [placementBaseResidue, residueOfInt, BaseHasResidue,
      Res3.value, x, hzero] using
      (base_residue_of_remainder (t := t) (q := base.1) (r := base.2)
        (k := 0) (by simpa [x] using hzero) (by norm_num))
  · by_cases hone : x % 3 = 1
    · simpa [placementBaseResidue, residueOfInt, BaseHasResidue,
        Res3.value, x, hzero, hone] using
        (base_residue_of_remainder (t := t) (q := base.1) (r := base.2)
          (k := 1) (by simpa [x] using hone) (by norm_num))
    · have htwo : x % 3 = 2 := by omega
      simpa [placementBaseResidue, residueOfInt, BaseHasResidue,
        Res3.value, x, hzero, hone] using
        (base_residue_of_remainder (t := t) (q := base.1) (r := base.2)
          (k := 2) (by simpa [x] using htwo) (by norm_num))

end FiniteDefects

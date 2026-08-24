import BenzelProblem6Kernel.LiteralCellEnergy
import BenzelProblem6Kernel.LiteralTilingCarrier
import Mathlib.Data.Int.ModEq

/-!
# Actual phase of a translated prototile

The residue used by the finite local table is derived here from the literal
placement base and the benzel owner phase.  No residue choice is supplied as
an external premise.
-/

namespace BenzelProblem6Kernel

def Res3.value : Res3 → ℤ
  | .r0 => 0
  | .r1 => 1
  | .r2 => 2

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

theorem shifted_anchor_is_phase {t : ℕ} {q r k dq dr : ℤ}
    (hbase : q - r ≡ (t : ℤ) + k [ZMOD 3])
    (hdiv : (3 : ℤ) ∣ k + dq - dr) :
    IsOwnerPhase t (q + dq, r + dr) := by
  unfold IsOwnerPhase
  have hshift := hbase.add (Int.ModEq.refl (dq - dr))
  have hzero : k + dq - dr ≡ 0 [ZMOD 3] := hdiv.modEq_zero_int
  have htarget := (Int.ModEq.refl (t : ℤ)).add hzero
  have hmiddle : (t : ℤ) + k + (dq - dr) ≡ (t : ℤ) [ZMOD 3] := by
    convert htarget using 1; ring
  have hfinal := hshift.trans hmiddle
  convert hfinal using 1; ring

theorem translated_local_owner_is_phase (t : ℕ) (base : Cell)
    (tile : ProtoTile) (localCell : LocalCell)
    (hlocal : localCell ∈ protoCells tile) :
    IsOwnerPhase t
      (base.1 + (ownerShift (placementBaseResidue t base) localCell).1,
        base.2 + (ownerShift (placementBaseResidue t base) localCell).2) := by
  have hbase := placementBaseResidue_spec t base
  unfold BaseHasResidue at hbase
  rcases hrho : placementBaseResidue t base with _ | _ | _
  all_goals simp only [hrho, Res3.value] at hbase
  all_goals
    rcases tile with _ | _ | _ | _ <;>
      simp [protoCells] at hlocal
  all_goals
    rcases hlocal with rfl | rfl | rfl <;>
      simp only [ownerShift, localLabel, Res3.add, Res3.toLabel,
        c00, c10, c20, c01, c02, c1m1, c2m2]
  all_goals
    apply shifted_anchor_is_phase hbase; norm_num

noncomputable def phaseOwnerLabel (t : ℕ) (cell : Cell) : MicroLabel :=
  (unique_phase_owner_label t cell).choose

theorem phaseOwnerLabel_is_phase (t : ℕ) (cell : Cell) :
    IsOwnerPhase t (ownerAnchorForCell cell (phaseOwnerLabel t cell)) :=
  (unique_phase_owner_label t cell).choose_spec.1

theorem phaseOwnerLabel_unique (t : ℕ) (cell : Cell) (label : MicroLabel)
    (hlabel : IsOwnerPhase t (ownerAnchorForCell cell label)) :
    phaseOwnerLabel t cell = label :=
  ((unique_phase_owner_label t cell).choose_spec.2 label hlabel).symm

noncomputable def phaseCellEnergy (t : ℕ) (cell : Cell) : ℤ :=
  ownerPotential (phaseOwnerLabel t cell)
    (ownerAnchorForCell cell (phaseOwnerLabel t cell)).1
    (ownerAnchorForCell cell (phaseOwnerLabel t cell)).2

theorem ownerAnchorForCell_translate_eq (base : Cell) (rho : Res3)
    (localCell : LocalCell) :
    ownerAnchorForCell (translateLocalCell base localCell)
        (localLabel rho localCell) =
      (base.1 + (ownerShift rho localCell).1,
        base.2 + (ownerShift rho localCell).2) := by
  rcases hlabel : localLabel rho localCell with _ | _ | _ <;>
    simp [translateLocalCell, ownerShift, hlabel, ownerAnchorForCell]
  all_goals ring

theorem phaseCellEnergy_translate (t : ℕ) (base : Cell)
    (tile : ProtoTile) (localCell : LocalCell)
    (hlocal : localCell ∈ protoCells tile) :
    phaseCellEnergy t (translateLocalCell base localCell) =
      localCellEnergy base.1 base.2 (placementBaseResidue t base) localCell := by
  let rho := placementBaseResidue t base
  have hanchor := ownerAnchorForCell_translate_eq base rho localCell
  have hphase :
      IsOwnerPhase t
        (ownerAnchorForCell (translateLocalCell base localCell)
          (localLabel rho localCell)) := by
    rw [hanchor]
    exact translated_local_owner_is_phase t base tile localCell hlocal
  have hlabel := phaseOwnerLabel_unique t (translateLocalCell base localCell)
    (localLabel rho localCell) hphase
  simp only [phaseCellEnergy, localCellEnergy]
  rw [hlabel, hanchor]

theorem literalCellEnergy_eq_phaseCellEnergy {n : ℕ} (hn : 5 ≤ n)
    (cell : BenzelCell n) :
    literalCellEnergy hn cell = phaseCellEnergy (n - 2) cell.1 := by
  let pair := chosenOwnerPair hn cell
  have hcell : ownerCell pair.1.1 pair.1.2 = cell.1 :=
    chosenOwnerPair_spec hn cell
  have hanchor :
      ownerAnchorForCell cell.1 pair.1.2 =
        (ownerQ pair.1.1, ownerR pair.1.1) := by
    rw [← hcell, ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip (ownerQ pair.1.1, ownerR pair.1.1) pair.1.2
  have hpairPhase :
      IsOwnerPhase (n - 2) (ownerAnchorForCell cell.1 pair.1.2) := by
    rw [hanchor]
    exact owner_anchor_is_phase pair.1.1
  have hlabel := phaseOwnerLabel_unique (n - 2) cell.1 pair.1.2 hpairPhase
  simp only [literalCellEnergy, phaseCellEnergy]
  change ownerLabelEnergy pair.1.1 pair.1.2 = _
  rw [hlabel, hanchor]
  rfl

def literalPlacementEnergy {m : ℕ} (placement : LiteralPlacement m) : ℤ :=
  literalTileEnergy placement.tile placement.base.1 placement.base.2
    (placementBaseResidue (m + 3) placement.base)

theorem phase_energy_sum_of_placement {m : ℕ}
    (placement : LiteralPlacement m) :
    (placement.cells.map (phaseCellEnergy (m + 3))).sum =
      literalPlacementEnergy placement := by
  change
    (((protoCells placement.tile).map
      (translateLocalCell placement.base)).map
      (phaseCellEnergy (m + 3))).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro localCell hlocal
  exact phaseCellEnergy_translate (m + 3) placement.base
    placement.tile localCell hlocal

end BenzelProblem6Kernel

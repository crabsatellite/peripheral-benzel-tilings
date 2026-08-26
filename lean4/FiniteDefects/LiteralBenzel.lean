import FiniteDefects.Basic
import Mathlib.Data.Int.ModEq

/-! # Literal two-parameter benzel and its periodic owner partition -/

namespace FiniteDefects

def inBenzel (a b : ℕ) (cell : Cell) : Prop :=
  let i := cell.1
  let j := cell.2
  let k : ℤ := 1 - i - j
  let lower : ℤ := 1 - a
  let upper : ℤ := b - 1
  lower ≤ j - i ∧ j - i ≤ upper ∧
  lower ≤ k - j ∧ k - j ≤ upper ∧
  lower ≤ i - k ∧ i - k ≤ upper

def ownerCell {t : ℕ} (p : SimplexPoint t) : MicroLabel → Cell
  | .zero => (ownerQ p, ownerR p)
  | .one => (ownerQ p + 1, ownerR p)
  | .two => (ownerQ p, ownerR p + 1)

theorem owner_cell_zero_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .zero
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t ∧
    k - j = 3 * (p.v : ℤ) - t + 1 ∧
    i - k = 3 * (p.w : ℤ) - t - 1 := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

theorem owner_cell_one_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .one
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t - 1 ∧
    k - j = 3 * (p.v : ℤ) - t ∧
    i - k = 3 * (p.w : ℤ) - t + 1 := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

theorem owner_cell_two_differences {t : ℕ} (p : SimplexPoint t) :
    let cell := ownerCell p .two
    let i := cell.1
    let j := cell.2
    let k : ℤ := 1 - i - j
    j - i = 3 * (p.u : ℤ) - t + 1 ∧
    k - j = 3 * (p.v : ℤ) - t - 1 ∧
    i - k = 3 * (p.w : ℤ) - t := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerCell, ownerQ, ownerR]
  omega

def ownerAnchorForCell (cell : Cell) : MicroLabel → Cell
  | .zero => cell
  | .one => (cell.1 - 1, cell.2)
  | .two => (cell.1, cell.2 - 1)

def cellForOwnerAnchor (anchor : Cell) : MicroLabel → Cell
  | .zero => anchor
  | .one => (anchor.1 + 1, anchor.2)
  | .two => (anchor.1, anchor.2 + 1)

def IsOwnerPhase (t : ℕ) (anchor : Cell) : Prop :=
  anchor.1 - anchor.2 ≡ (t : ℤ) [ZMOD 3]

@[simp] theorem cell_anchor_roundtrip (cell : Cell) (label : MicroLabel) :
    cellForOwnerAnchor (ownerAnchorForCell cell label) label = cell := by
  rcases label with _ | _ | _ <;>
    simp [cellForOwnerAnchor, ownerAnchorForCell]

@[simp] theorem anchor_cell_roundtrip (anchor : Cell) (label : MicroLabel) :
    ownerAnchorForCell (cellForOwnerAnchor anchor label) label = anchor := by
  rcases label with _ | _ | _ <;>
    simp [cellForOwnerAnchor, ownerAnchorForCell]

theorem ownerCell_eq_cellForOwnerAnchor {t : ℕ}
    (p : SimplexPoint t) (label : MicroLabel) :
    ownerCell p label = cellForOwnerAnchor (ownerQ p, ownerR p) label := by
  rcases label with _ | _ | _ <;>
    simp [ownerCell, cellForOwnerAnchor]

theorem owner_anchor_is_phase {t : ℕ} (p : SimplexPoint t) :
    IsOwnerPhase t (ownerQ p, ownerR p) := by
  rw [IsOwnerPhase, Int.modEq_iff_dvd]
  refine ⟨p.u, ?_⟩
  simp [owner_phase_identity]

theorem unique_phase_owner_label (t : ℕ) (cell : Cell) :
    ∃! label, IsOwnerPhase t (ownerAnchorForCell cell label) := by
  let d : ℤ := (cell.1 - cell.2 - (t : ℤ)) % 3
  have hd_nonneg : 0 ≤ d := Int.emod_nonneg _ (by norm_num)
  have hd_lt : d < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hd_cases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd_cases with hd | hd | hd
  · refine ⟨.zero, ?_, ?_⟩
    · simp only [IsOwnerPhase, ownerAnchorForCell]
      rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
      dsimp [d] at hd
      omega
    · intro label hlabel
      rcases label with _ | _ | _
      · rfl
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
  · refine ⟨.one, ?_, ?_⟩
    · simp only [IsOwnerPhase, ownerAnchorForCell]
      rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
      dsimp [d] at hd
      omega
    · intro label hlabel
      rcases label with _ | _ | _
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
      · rfl
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
  · refine ⟨.two, ?_, ?_⟩
    · simp only [IsOwnerPhase, ownerAnchorForCell]
      rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero]
      dsimp [d] at hd
      omega
    · intro label hlabel
      rcases label with _ | _ | _
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
      · simp only [IsOwnerPhase, ownerAnchorForCell] at hlabel
        rw [Int.modEq_iff_dvd, Int.dvd_iff_emod_eq_zero] at hlabel
        dsimp [d] at hd
        omega
      · rfl

theorem recover_u_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) - ownerQ p + ownerR p = 3 * p.u := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem recover_v_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) - ownerQ p - 2 * ownerR p = 3 * p.v := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem recover_w_numerator {t : ℕ} (p : SimplexPoint t) :
    (t : ℤ) + 2 * ownerQ p + ownerR p = 3 * p.w := by
  have hsum : (p.u : ℤ) + p.v + p.w = t := by
    exact_mod_cast p.sum_eq
  simp [ownerQ, ownerR]
  omega

theorem phase_anchor_has_simplex (t b : ℕ)
    (anchor : Cell) (label : MicroLabel)
    (hphase : IsOwnerPhase t anchor)
    (hmem : inBenzel (t + 2) b (cellForOwnerAnchor anchor label)) :
    ∃ p : SimplexPoint t,
      ownerQ p = anchor.1 ∧ ownerR p = anchor.2 := by
  let uZ : ℤ := (t : ℤ) - anchor.1 + anchor.2
  have hu_dvd : (3 : ℤ) ∣ uZ := by
    rw [IsOwnerPhase, Int.modEq_iff_dvd] at hphase
    dsimp [uZ]
    convert hphase using 1
    ring
  obtain ⟨u0, hu0⟩ := hu_dvd
  have hu_eq : uZ = 3 * u0 := hu0
  let v0 : ℤ := u0 - anchor.2
  let w0 : ℤ := u0 + anchor.1
  have hv_eq : (t : ℤ) - anchor.1 - 2 * anchor.2 = 3 * v0 := by
    dsimp [uZ] at hu_eq
    dsimp [v0]
    omega
  have hw_eq : (t : ℤ) + 2 * anchor.1 + anchor.2 = 3 * w0 := by
    dsimp [uZ] at hu_eq
    dsimp [w0]
    omega
  have hnonneg : 0 ≤ u0 ∧ 0 ≤ v0 ∧ 0 ≤ w0 := by
    rcases label with _ | _ | _ <;>
      dsimp [inBenzel, cellForOwnerAnchor] at hmem <;>
      dsimp [uZ] at hu_eq <;>
      dsimp [v0, w0] at hv_eq hw_eq ⊢ <;>
      omega
  have hsumZ : u0 + v0 + w0 = (t : ℤ) := by
    dsimp [uZ] at hu_eq
    dsimp [v0, w0]
    omega
  let p : SimplexPoint t :=
    { u := u0.toNat
      v := v0.toNat
      w := w0.toNat
      sum_eq := by
        have hu_cast : (u0.toNat : ℤ) = u0 := Int.toNat_of_nonneg hnonneg.1
        have hv_cast : (v0.toNat : ℤ) = v0 := Int.toNat_of_nonneg hnonneg.2.1
        have hw_cast : (w0.toNat : ℤ) = w0 := Int.toNat_of_nonneg hnonneg.2.2
        omega }
  refine ⟨p, ?_, ?_⟩
  · have hu_cast : (u0.toNat : ℤ) = u0 := Int.toNat_of_nonneg hnonneg.1
    have hw_cast : (w0.toNat : ℤ) = w0 := Int.toNat_of_nonneg hnonneg.2.2
    simp [p, ownerQ, hu_cast, hw_cast, w0]
  · have hu_cast : (u0.toNat : ℤ) = u0 := Int.toNat_of_nonneg hnonneg.1
    have hv_cast : (v0.toNat : ℤ) = v0 := Int.toNat_of_nonneg hnonneg.2.1
    simp [p, ownerR, hu_cast, hv_cast, v0]

theorem benzel_cell_has_owner (t b : ℕ) (cell : Cell)
    (hmem : inBenzel (t + 2) b cell) :
    ∃ (p : SimplexPoint t) (label : MicroLabel),
      ownerCell p label = cell := by
  obtain ⟨label, hphase, _⟩ := unique_phase_owner_label t cell
  let anchor := ownerAnchorForCell cell label
  have hmem' : inBenzel (t + 2) b (cellForOwnerAnchor anchor label) := by
    simpa [anchor] using hmem
  obtain ⟨p, hq, hr⟩ :=
    phase_anchor_has_simplex t b anchor label hphase hmem'
  refine ⟨p, label, ?_⟩
  rw [ownerCell_eq_cellForOwnerAnchor, hq, hr]
  exact cell_anchor_roundtrip cell label

theorem owner_representation_unique {t : ℕ}
    (cell : Cell) (p p' : SimplexPoint t)
    (label label' : MicroLabel)
    (hp : ownerCell p label = cell)
    (hp' : ownerCell p' label' = cell) :
    p = p' ∧ label = label' := by
  have hanchor (r : SimplexPoint t) (ell : MicroLabel)
      (hcell : ownerCell r ell = cell) :
      ownerAnchorForCell cell ell = (ownerQ r, ownerR r) := by
    rw [← hcell, ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip (ownerQ r, ownerR r) ell
  obtain ⟨phaseLabel, _, hphaseUnique⟩ :=
    unique_phase_owner_label t cell
  have hlabelPhase : IsOwnerPhase t (ownerAnchorForCell cell label) := by
    rw [hanchor p label hp]
    exact owner_anchor_is_phase p
  have hlabelPhase' : IsOwnerPhase t (ownerAnchorForCell cell label') := by
    rw [hanchor p' label' hp']
    exact owner_anchor_is_phase p'
  have hlabel : label = label' :=
    (hphaseUnique label hlabelPhase).trans
      (hphaseUnique label' hlabelPhase').symm
  subst label'
  have hanchors : (ownerQ p, ownerR p) = (ownerQ p', ownerR p') := by
    rw [← hanchor p label hp, ← hanchor p' label hp']
  have hq : ownerQ p = ownerQ p' := congrArg Prod.fst hanchors
  have hr : ownerR p = ownerR p' := congrArg Prod.snd hanchors
  have huZ := recover_u_numerator p
  have huZ' := recover_u_numerator p'
  have hvZ := recover_v_numerator p
  have hvZ' := recover_v_numerator p'
  have hwZ := recover_w_numerator p
  have hwZ' := recover_w_numerator p'
  have hu : p.u = p'.u := by omega
  have hv : p.v = p'.v := by omega
  have hw : p.w = p'.w := by omega
  constructor
  · exact simplexPoint_ext hu hv hw
  · rfl

end FiniteDefects

import D4KernelOnly.GeneralOwnerEnergyCases

/-! # Closed region-energy formulas for the two finite-defect residue classes -/

namespace FiniteDefects

open scoped BigOperators

theorem sum_u_boundary_indicator (t k : ℕ) (f : SimplexPoint t → ℤ) :
    (∑ p : SimplexPoint t, if p.u = t - k + 1 then f p else 0) =
      ∑ p : BoundaryU t k, f p.1 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro p
  simp

theorem sum_v_boundary_indicator (t k : ℕ) (f : SimplexPoint t → ℤ) :
    (∑ p : SimplexPoint t, if p.v = t - k + 1 then f p else 0) =
      ∑ p : BoundaryV t k, f p.1 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro p
  simp

theorem sum_w_boundary_indicator (t k : ℕ) (f : SimplexPoint t → ℤ) :
    (∑ p : SimplexPoint t, if p.w = t - k + 1 then f p else 0) =
      ∑ p : BoundaryW t k, f p.1 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro p
  simp

theorem twice_fin_boundary_linear_sum (t k : ℕ)
    (hk : 1 ≤ k) (hkt : k ≤ t) :
    2 * (∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ))) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  rw [show (∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ))) =
      ∑ j ∈ Finset.range k,
        (((t - k + 1 : ℕ) : ℤ) - (j : ℤ)) by
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (((t - k + 1 : ℕ) : ℤ) - (j : ℤ))) k]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum2 :
      2 * (∑ x ∈ Finset.range k, (x : ℤ)) =
        (k : ℤ) * ((k : ℤ) - 1) := by
    have h := Finset.sum_range_id_mul_two k
    have hz := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hk] at hz
    convert hz using 1
    all_goals ring
  push_cast [Nat.cast_sub hkt]
  nlinarith [hsum2]

theorem twice_d3k_boundaryU_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryU t k,
      (offsetOwnerLabelEnergy p.1 .zero +
        offsetOwnerLabelEnergy p.1 .one)) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  have htransport :
      (∑ p : BoundaryU t k,
        (offsetOwnerLabelEnergy p.1 .zero +
          offsetOwnerLabelEnergy p.1 .one)) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv (boundaryUEquivFin t k hroom)
    intro p
    have hsum := p.1.sum_eq
    have hu := p.2
    simp [offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR,
      boundaryUEquivFin]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_d3k_boundaryV_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryV t k,
      (offsetOwnerLabelEnergy p.1 .one +
        offsetOwnerLabelEnergy p.1 .two)) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  let e := (boundaryVEquivBoundaryU t k).trans (boundaryUEquivFin t k hroom)
  have htransport :
      (∑ p : BoundaryV t k,
        (offsetOwnerLabelEnergy p.1 .one +
          offsetOwnerLabelEnergy p.1 .two)) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv e
    intro p
    have hsum := p.1.sum_eq
    have hv := p.2
    simp [e, boundaryVEquivBoundaryU, boundaryUEquivFin,
      rotateOwner, offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_d3k_boundaryW_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryW t k,
      (offsetOwnerLabelEnergy p.1 .zero +
        offsetOwnerLabelEnergy p.1 .two)) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  let e := (boundaryWEquivBoundaryU t k).trans (boundaryUEquivFin t k hroom)
  have htransport :
      (∑ p : BoundaryW t k,
        (offsetOwnerLabelEnergy p.1 .zero +
          offsetOwnerLabelEnergy p.1 .two)) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv e
    intro p
    have hsum := p.1.sum_eq
    have hw := p.2
    simp [e, boundaryWEquivBoundaryU, boundaryUEquivFin,
      rotateOwner, offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_d3k1_boundaryU_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryU t k, offsetOwnerLabelEnergy p.1 .one) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  let e := (boundaryUEquivFin t k hroom).trans Fin.revPerm
  have htransport :
      (∑ p : BoundaryU t k, offsetOwnerLabelEnergy p.1 .one) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv e
    intro p
    have hsum := p.1.sum_eq
    have hu := p.2
    simp [e, boundaryUEquivFin, Fin.revPerm, Fin.rev,
      offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_d3k1_boundaryV_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryV t k, offsetOwnerLabelEnergy p.1 .two) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  let e := ((boundaryVEquivBoundaryU t k).trans
    (boundaryUEquivFin t k hroom)).trans Fin.revPerm
  have htransport :
      (∑ p : BoundaryV t k, offsetOwnerLabelEnergy p.1 .two) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv e
    intro p
    have hsum := p.1.sum_eq
    have hv := p.2
    simp [e, boundaryVEquivBoundaryU, boundaryUEquivFin,
      rotateOwner, Fin.revPerm, Fin.rev,
      offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_d3k1_boundaryW_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : BoundaryW t k, offsetOwnerLabelEnergy p.1 .zero) =
      (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  let e := ((boundaryWEquivBoundaryU t k).trans
    (boundaryUEquivFin t k hroom)).trans Fin.revPerm
  have htransport :
      (∑ p : BoundaryW t k, offsetOwnerLabelEnergy p.1 .zero) =
      ∑ j : Fin k, (((t - k + 1 : ℕ) : ℤ) - (j.1 : ℤ)) := by
    apply Fintype.sum_equiv e
    intro p
    have hsum := p.1.sum_eq
    have hw := p.2
    simp [e, boundaryWEquivBoundaryU, boundaryUEquivFin,
      rotateOwner, Fin.revPerm, Fin.rev,
      offsetOwnerLabelEnergy, ownerPotential, ownerQ, ownerR]
    omega
  rw [htransport]
  exact twice_fin_boundary_linear_sum t k hk (by omega)

theorem twice_total_d3k_owner_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : SimplexPoint t, offsetOwnerPresentEnergy t (3 * k) p) =
      3 * (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  simp_rw [d3k_owner_energy_cases t k hroom]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_u_boundary_indicator, sum_v_boundary_indicator,
    sum_w_boundary_indicator]
  have hu := twice_d3k_boundaryU_energy t k hk hroom
  have hv := twice_d3k_boundaryV_energy t k hk hroom
  have hw := twice_d3k_boundaryW_energy t k hk hroom
  nlinarith

theorem twice_total_d3k1_owner_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ p : SimplexPoint t, offsetOwnerPresentEnergy t (3 * k + 1) p) =
      3 * (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  simp_rw [d3k1_owner_energy_cases t k hroom]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_u_boundary_indicator, sum_v_boundary_indicator,
    sum_w_boundary_indicator]
  have hu := twice_d3k1_boundaryU_energy t k hk hroom
  have hv := twice_d3k1_boundaryV_energy t k hk hroom
  have hw := twice_d3k1_boundaryW_energy t k hk hroom
  nlinarith

theorem phaseCellEnergy_ownerCell {t : ℕ}
    (p : SimplexPoint t) (label : MicroLabel) :
    phaseCellEnergy t (ownerCell p label) = offsetOwnerLabelEnergy p label := by
  have hanchor : ownerAnchorForCell (ownerCell p label) label =
      (ownerQ p, ownerR p) := by
    rw [ownerCell_eq_cellForOwnerAnchor]
    exact anchor_cell_roundtrip (ownerQ p, ownerR p) label
  have hphase : IsOwnerPhase t
      (ownerAnchorForCell (ownerCell p label) label) := by
    rw [hanchor]
    exact owner_anchor_is_phase p
  have hlabel := phaseOwnerLabel_unique t (ownerCell p label) label hphase
  simp only [phaseCellEnergy, offsetOwnerLabelEnergy]
  rw [hlabel, hanchor]

theorem offset_present_owner_label_energy_sum (t d : ℕ) :
    ∑ pair : PresentOffsetOwnerLabel t d,
        offsetOwnerLabelEnergy pair.1.1 pair.1.2 =
      ∑ p : SimplexPoint t, offsetOwnerPresentEnergy t d p := by
  classical
  calc
    (∑ pair : PresentOffsetOwnerLabel t d,
        offsetOwnerLabelEnergy pair.1.1 pair.1.2) =
        ∑ pair : OffsetOwnerLabelPair t,
          if IsPresentOffsetOwnerLabel t d pair then
            offsetOwnerLabelEnergy pair.1 pair.2 else 0 := by
      symm
      calc
        (∑ pair : OffsetOwnerLabelPair t,
            if IsPresentOffsetOwnerLabel t d pair then
              offsetOwnerLabelEnergy pair.1 pair.2 else 0) =
            ∑ pair ∈ Finset.univ.filter (IsPresentOffsetOwnerLabel t d),
              offsetOwnerLabelEnergy pair.1 pair.2 := by
          rw [Finset.sum_filter]
        _ = ∑ pair : PresentOffsetOwnerLabel t d,
              offsetOwnerLabelEnergy pair.1.1 pair.1.2 := by
          apply Finset.sum_subtype
          intro pair
          simp
    _ = ∑ p : SimplexPoint t,
          ∑ label : MicroLabel,
            if IsPresentOffsetOwnerLabel t d (p, label) then
              offsetOwnerLabelEnergy p label else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p : SimplexPoint t, offsetOwnerPresentEnergy t d p := by
      apply Finset.sum_congr rfl
      intro p _
      unfold offsetOwnerPresentEnergy IsPresentOffsetOwnerLabel
      apply Finset.sum_congr rfl
      intro label _
      by_cases hmem :
          inBenzel (t + 2) (offsetB t d) (ownerCell p label) <;>
        simp [hmem]

theorem total_offset_literal_cell_energy (t d : ℕ) :
    ∑ cell : OffsetCell t d, offsetLiteralCellEnergy cell =
      ∑ p : SimplexPoint t, offsetOwnerPresentEnergy t d p := by
  calc
    (∑ cell : OffsetCell t d, offsetLiteralCellEnergy cell) =
        ∑ pair : PresentOffsetOwnerLabel t d,
          offsetOwnerLabelEnergy pair.1.1 pair.1.2 := by
      apply Fintype.sum_equiv (offsetOwnerCellEquiv t d).symm
      intro cell
      let pair := (offsetOwnerCellEquiv t d).symm cell
      have hmap : offsetOwnerCellMap t d pair = cell :=
        (offsetOwnerCellEquiv t d).apply_symm_apply cell
      have hcell : ownerCell pair.1.1 pair.1.2 = cell.1 :=
        congrArg Subtype.val hmap
      change phaseCellEnergy t cell.1 = _
      rw [← hcell, phaseCellEnergy_ownerCell]
    _ = _ := offset_present_owner_label_energy_sum t d

theorem twice_total_d3k_literal_cell_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ cell : OffsetCell t (3 * k), offsetLiteralCellEnergy cell) =
      3 * (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  rw [total_offset_literal_cell_energy]
  exact twice_total_d3k_owner_energy t k hk hroom

theorem twice_total_d3k1_literal_cell_energy (t k : ℕ)
    (hk : 1 ≤ k) (hroom : 2 * k ≤ t + 1) :
    2 * (∑ cell : OffsetCell t (3 * k + 1), offsetLiteralCellEnergy cell) =
      3 * (k : ℤ) * (2 * (t : ℤ) - 3 * (k : ℤ) + 3) := by
  rw [total_offset_literal_cell_energy]
  exact twice_total_d3k1_owner_energy t k hk hroom

end FiniteDefects

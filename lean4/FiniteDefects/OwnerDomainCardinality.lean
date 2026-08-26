import FiniteDefects.OwnerDomain
import FiniteDefects.SimplexCardinality

/-! # Boundary and removed-corner cardinalities -/

namespace FiniteDefects

abbrev BoundaryU (t k : ℕ) :=
  {p : SimplexPoint t // p.u = t - k + 1}

def boundaryUEquivFin (t k : ℕ) (hroom : 2 * k ≤ t + 1) :
    BoundaryU t k ≃ Fin k where
  toFun p := ⟨p.1.v, by have := p.1.sum_eq; have := p.2; omega⟩
  invFun j :=
    ⟨boundaryU t k j.1 (by omega) j.2, by simp [boundaryU]⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    · exact p.2.symm.trans (by simp [boundaryU])
    · rfl
    · have hsum := p.1.sum_eq
      have hu := p.2
      simp [boundaryU]
      omega
  right_inv := by
    intro j
    apply Fin.ext
    rfl

theorem card_boundaryU (t k : ℕ) (hroom : 2 * k ≤ t + 1) :
    Fintype.card (BoundaryU t k) = k := by
  rw [Fintype.card_congr (boundaryUEquivFin t k hroom), Fintype.card_fin]

abbrev BoundaryV (t k : ℕ) :=
  {p : SimplexPoint t // p.v = t - k + 1}

abbrev BoundaryW (t k : ℕ) :=
  {p : SimplexPoint t // p.w = t - k + 1}

abbrev RemovedU (t k : ℕ) :=
  {p : SimplexPoint t // t - k + 1 < p.u}

def removedUEquivSimplex (t k : ℕ) (hk : 2 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    RemovedU t k ≃ SimplexPoint (k - 2) where
  toFun p :=
    { u := k - 2 - p.1.v - p.1.w
      v := p.1.v
      w := p.1.w
      sum_eq := by
        have hsum := p.1.sum_eq
        have hremoved := p.2
        omega }
  invFun q :=
    ⟨{ u := t - q.v - q.w
       v := q.v
       w := q.w
       sum_eq := by have hsum := q.sum_eq; omega },
      by
        change t - k + 1 < t - q.v - q.w
        have hsum := q.sum_eq
        omega⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply simplexPoint_ext
    · change t - p.1.v - p.1.w = p.1.u
      have hsum := p.1.sum_eq
      omega
    · rfl
    · rfl
  right_inv := by
    intro q
    apply simplexPoint_ext
    · have hsum := q.sum_eq
      simp
      omega
    · rfl
    · rfl

theorem card_removedU_of_two_le (t k : ℕ) (hk : 2 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedU t k) = k.choose 2 := by
  rw [Fintype.card_congr (removedUEquivSimplex t k hk hroom),
    card_simplexPoint]
  congr 1
  omega

theorem card_removedU_one (t : ℕ) :
    Fintype.card (RemovedU t 1) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => by
    have hsum := p.1.sum_eq
    have hremoved := p.2
    omega⟩

def rotateOwner (t : ℕ) : SimplexPoint t ≃ SimplexPoint t where
  toFun p :=
    { u := p.v
      v := p.w
      w := p.u
      sum_eq := by have := p.sum_eq; omega }
  invFun p :=
    { u := p.w
      v := p.u
      w := p.v
      sum_eq := by have := p.sum_eq; omega }
  left_inv := by intro p; apply simplexPoint_ext <;> rfl
  right_inv := by intro p; apply simplexPoint_ext <;> rfl

def boundaryVEquivBoundaryU (t k : ℕ) : BoundaryV t k ≃ BoundaryU t k where
  toFun p := ⟨rotateOwner t p.1, p.2⟩
  invFun p := ⟨(rotateOwner t).symm p.1, p.2⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; simp

def boundaryWEquivBoundaryU (t k : ℕ) : BoundaryW t k ≃ BoundaryU t k where
  toFun p := ⟨rotateOwner t (rotateOwner t p.1), p.2⟩
  invFun p := ⟨(rotateOwner t).symm ((rotateOwner t).symm p.1), p.2⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; simp

theorem card_boundaryV (t k : ℕ) (hroom : 2 * k ≤ t + 1) :
    Fintype.card (BoundaryV t k) = k := by
  rw [Fintype.card_congr (boundaryVEquivBoundaryU t k),
    card_boundaryU t k hroom]

theorem card_boundaryW (t k : ℕ) (hroom : 2 * k ≤ t + 1) :
    Fintype.card (BoundaryW t k) = k := by
  rw [Fintype.card_congr (boundaryWEquivBoundaryU t k),
    card_boundaryU t k hroom]

abbrev RemovedV (t k : ℕ) :=
  {p : SimplexPoint t // t - k + 1 < p.v}

abbrev RemovedW (t k : ℕ) :=
  {p : SimplexPoint t // t - k + 1 < p.w}

def removedVEquivRemovedU (t k : ℕ) : RemovedV t k ≃ RemovedU t k where
  toFun p := ⟨rotateOwner t p.1, p.2⟩
  invFun p := ⟨(rotateOwner t).symm p.1, p.2⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; simp

def removedWEquivRemovedU (t k : ℕ) : RemovedW t k ≃ RemovedU t k where
  toFun p := ⟨rotateOwner t (rotateOwner t p.1), p.2⟩
  invFun p := ⟨(rotateOwner t).symm ((rotateOwner t).symm p.1), p.2⟩
  left_inv := by intro p; apply Subtype.ext; simp
  right_inv := by intro p; apply Subtype.ext; simp

theorem card_removedV_of_two_le (t k : ℕ) (hk : 2 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedV t k) = k.choose 2 := by
  rw [Fintype.card_congr (removedVEquivRemovedU t k),
    card_removedU_of_two_le t k hk hroom]

theorem card_removedW_of_two_le (t k : ℕ) (hk : 2 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedW t k) = k.choose 2 := by
  rw [Fintype.card_congr (removedWEquivRemovedU t k),
    card_removedU_of_two_le t k hk hroom]

theorem card_removedU_of_pos (t k : ℕ) (hk : 1 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedU t k) = k.choose 2 := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk
  · simpa using card_removedU_one t
  · exact card_removedU_of_two_le t k hk hroom

theorem card_removedV_of_pos (t k : ℕ) (hk : 1 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedV t k) = k.choose 2 := by
  rw [Fintype.card_congr (removedVEquivRemovedU t k),
    card_removedU_of_pos t k hk hroom]

theorem card_removedW_of_pos (t k : ℕ) (hk : 1 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (RemovedW t k) = k.choose 2 := by
  rw [Fintype.card_congr (removedWEquivRemovedU t k),
    card_removedU_of_pos t k hk hroom]

theorem removedU_not_removedV (t k : ℕ) (hroom : 2 * k ≤ t + 1)
    (p : SimplexPoint t) :
    ¬ (t - k + 1 < p.u ∧ t - k + 1 < p.v) := by
  have hsum := p.sum_eq
  omega

theorem removedV_not_removedW (t k : ℕ) (hroom : 2 * k ≤ t + 1)
    (p : SimplexPoint t) :
    ¬ (t - k + 1 < p.v ∧ t - k + 1 < p.w) := by
  have hsum := p.sum_eq
  omega

theorem removedW_not_removedU (t k : ℕ) (hroom : 2 * k ≤ t + 1)
    (p : SimplexPoint t) :
    ¬ (t - k + 1 < p.w ∧ t - k + 1 < p.u) := by
  have hsum := p.sum_eq
  omega

abbrev OutsideTruncatedOwnerDomain (t k : ℕ) :=
  {p : SimplexPoint t // ¬ inTruncatedOwnerDomain k p}

noncomputable instance outsideTruncatedOwnerDomainFintype (t k : ℕ) :
    Fintype (OutsideTruncatedOwnerDomain t k) :=
  Fintype.ofFinite (OutsideTruncatedOwnerDomain t k)

def outsideEquivRemovedCorners (t k : ℕ) (hroom : 2 * k ≤ t + 1) :
    OutsideTruncatedOwnerDomain t k ≃
      (RemovedU t k ⊕ (RemovedV t k ⊕ RemovedW t k)) where
  toFun p :=
    if hu : t - k + 1 < p.1.u then
      Sum.inl ⟨p.1, hu⟩
    else if hv : t - k + 1 < p.1.v then
      Sum.inr (Sum.inl ⟨p.1, hv⟩)
    else
      Sum.inr (Sum.inr ⟨p.1, by
        have hout := p.2
        simp only [inTruncatedOwnerDomain] at hout
        omega⟩)
  invFun s :=
    match s with
    | Sum.inl p => ⟨p.1, by simp [inTruncatedOwnerDomain]; omega⟩
    | Sum.inr (Sum.inl p) => ⟨p.1, by simp [inTruncatedOwnerDomain]; omega⟩
    | Sum.inr (Sum.inr p) => ⟨p.1, by simp [inTruncatedOwnerDomain]; omega⟩
  left_inv := by
    intro p
    simp only
    split_ifs <;> rfl
  right_inv := by
    intro s
    rcases s with p | p
    · simp [p.2]
    · rcases p with p | p
      · have hnotu : ¬ t - k + 1 < p.1.u := by
          intro hu
          exact removedU_not_removedV t k hroom p.1 ⟨hu, p.2⟩
        simp [hnotu, p.2]
      · have hnotu : ¬ t - k + 1 < p.1.u := by
          intro hu
          exact removedW_not_removedU t k hroom p.1 ⟨p.2, hu⟩
        have hnotv : ¬ t - k + 1 < p.1.v := by
          intro hv
          exact removedV_not_removedW t k hroom p.1 ⟨hv, p.2⟩
        simp [hnotu, hnotv, p.2]

theorem card_outsideTruncatedOwnerDomain (t k : ℕ) (hk : 1 ≤ k)
    (hroom : 2 * k ≤ t + 1) :
    Fintype.card (OutsideTruncatedOwnerDomain t k) =
      3 * k.choose 2 := by
  classical
  rw [Fintype.card_congr (outsideEquivRemovedCorners t k hroom)]
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [card_removedU_of_pos t k hk hroom,
    card_removedV_of_pos t k hk hroom,
    card_removedW_of_pos t k hk hroom]
  omega

end FiniteDefects

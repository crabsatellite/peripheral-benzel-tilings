import D4KernelOnly.GeneralClassZeroUpVertexCount

/-! # Cardinality of the class-zero up-type vertex carrier -/

namespace FiniteDefects

theorem czUpException_mem_truncated
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    {p : SimplexPoint (2 * s + r)}
    (hp : p ∈ czUpPhase2Exceptions s r) :
    inTruncatedOwnerDomain (s + 1) p := by
  simp only [czUpPhase2Exceptions, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [inTruncatedOwnerDomain, czUpException0,
      czUpException1, czUpException2] <;> omega

def czUpPhase2ExcludedEquivExceptions
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    {p : CMOTruncatedPoint (2 * s + r) (s + 1) //
      p.1 ∈ czUpPhase2Exceptions s r} ≃
      ↥(czUpPhase2Exceptions s r) where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p := ⟨⟨p.1, czUpException_mem_truncated s r hs hr p.2⟩, p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem card_czUpPhase2Exceptions
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (czUpPhase2Exceptions s r).card = 3 := by
  have h01 : czUpException0 s r ≠ czUpException1 s r := by
    intro h; have hu := congrArg SimplexPoint.u h
    simp [czUpException0, czUpException1] at hu
    omega
  have h02 : czUpException0 s r ≠ czUpException2 s r := by
    intro h; have hu := congrArg SimplexPoint.u h
    simp [czUpException0, czUpException2] at hu
    omega
  have h12 : czUpException1 s r ≠ czUpException2 s r := by
    intro h; have hv := congrArg SimplexPoint.v h
    simp [czUpException1, czUpException2] at hv
    omega
  simp [czUpPhase2Exceptions, h01, h02, h12]

noncomputable instance czUpPhase2ParameterFintype (s r : ℕ) :
    Fintype (CZUpPhase2Parameter s r) := Fintype.ofFinite _

theorem card_czUpPhase2Parameter
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    Fintype.card (CZUpPhase2Parameter s r) =
      Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 3 := by
  have hpartition := Fintype.card_subtype_compl
    (fun p : CMOTruncatedPoint (2 * s + r) (s + 1) =>
      p.1 ∈ czUpPhase2Exceptions s r)
  rw [Fintype.card_congr (czUpPhase2ExcludedEquivExceptions s r hs hr),
    Fintype.card_coe, card_czUpPhase2Exceptions s r hs hr] at hpartition
  exact hpartition

abbrev CZUpVertexParameterSum (s r : ℕ) :=
  CMOTruncatedPoint (2 * s + r - 2) s ⊕
    (CMOTruncatedPoint (2 * s + r - 1) (s + 1) ⊕ CZUpPhase2Parameter s r)

def czUpVertexParameterEquivSum (s r : ℕ) :
    CZUpVertexParameter s r ≃ CZUpVertexParameterSum s r where
  toFun
    | .phase0 p => .inl p
    | .phase1 p => .inr (.inl p)
    | .phase2 p => .inr (.inr p)
  invFun
    | .inl p => .phase0 p
    | .inr (.inl p) => .phase1 p
    | .inr (.inr p) => .phase2 p
  left_inv := by intro p; cases p <;> rfl
  right_inv := by intro p; rcases p with p | p; rfl; rcases p <;> rfl

noncomputable def czUpVertexParameterFintype (s r : ℕ) :
    Fintype (CZUpVertexParameter s r) :=
  Fintype.ofEquiv (CZUpVertexParameterSum s r)
    (czUpVertexParameterEquivSum s r).symm

noncomputable def czUpVertexParameterEquiv
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    CZUpVertexParameter s r ≃
      ↥(offsetUpAnchorFinset (2 * s + r - 2) (3 * s)) :=
  Equiv.ofBijective (czUpParameterToAnchor s r hs hr)
    ⟨by
      intro left right h
      exact czUpParameterAnchor_injective s r hs hr (congrArg Subtype.val h),
      czUpParameterToAnchor_surjective s r hs hr⟩

theorem card_czUpAnchor_as_truncated
    (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    (offsetUpAnchorFinset (2 * s + r - 2) (3 * s)).card =
      Fintype.card (CMOTruncatedPoint (2 * s + r - 2) s) +
      Fintype.card (CMOTruncatedPoint (2 * s + r - 1) (s + 1)) +
      (Fintype.card (CMOTruncatedPoint (2 * s + r) (s + 1)) - 3) := by
  letI := czUpVertexParameterFintype s r
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (czUpVertexParameterEquiv s r hs hr),
    Fintype.card_congr (czUpVertexParameterEquivSum s r),
    Fintype.card_sum, Fintype.card_sum, card_czUpPhase2Parameter s r hs hr]
  omega

theorem card_czUpAnchor_r_one
    (s : ℕ) (hs : 1 ≤ s) :
    (offsetUpAnchorFinset (2 * s + 1 - 2) (3 * s)).card =
      ((2 * s + 1).choose 2 - 3 * s.choose 2) +
        (s + 2).choose 2 +
          (((2 * s + 3).choose 2 - 3 * (s + 1).choose 2) - 3) := by
  rw [card_czUpAnchor_as_truncated s 1 hs (by omega)]
  rw [show 2 * s + 1 - 2 = 2 * s - 1 by omega,
    show 2 * s + 1 - 1 = 2 * s by omega]
  rw [card_cmoTruncatedPoint_of_room (2 * s - 1) s hs (by omega),
    card_cmoCentralTruncated s hs,
    card_cmoTruncatedPoint_of_room (2 * s + 1) (s + 1) (by omega) (by omega)]
  rw [show 2 * s - 1 + 2 = 2 * s + 1 by omega,
    show 2 * s + 1 + 2 = 2 * s + 3 by omega]

theorem card_czUpAnchor_r_ge_two
    (s r : ℕ) (hs : 1 ≤ s) (hr : 2 ≤ r) :
    (offsetUpAnchorFinset (2 * s + r - 2) (3 * s)).card =
      ((2 * s + r).choose 2 - 3 * s.choose 2) +
        ((2 * s + r + 1).choose 2 - 3 * (s + 1).choose 2) +
          (((2 * s + r + 2).choose 2 - 3 * (s + 1).choose 2) - 3) := by
  rw [card_czUpAnchor_as_truncated s r hs (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + r - 2) s hs (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + r - 1) (s + 1) (by omega) (by omega),
    card_cmoTruncatedPoint_of_room (2 * s + r) (s + 1) (by omega) (by omega)]
  rw [show 2 * s + r - 2 + 2 = 2 * s + r by omega,
    show 2 * s + r - 1 + 2 = 2 * s + r + 1 by omega]

end FiniteDefects

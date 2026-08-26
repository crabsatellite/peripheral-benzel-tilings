import FiniteDefects.D4ArmDecodeInverse

/-! # Exact cardinality of one literal defect arm -/

namespace FiniteDefects

noncomputable def concreteBallotWordFintype (up down : ℕ) :
    Fintype (ConcreteBallotWord up down) :=
  Fintype.ofEquiv (RecursiveBallot up down)
    (recursiveBallotEquivConcrete up down)

noncomputable def d4ArmPathFintype {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core) :
    Fintype (D4ArmPath m label core) := by
  letI := concreteBallotWordFintype (d4ArmMajority label core)
    (d4ArmMinority label core)
  exact Fintype.ofEquiv
    (ConcreteBallotWord (d4ArmMajority label core)
      (d4ArmMinority label core))
    (d4ArmPathEquivConcrete label core hroom).symm

theorem d4ArmMinority_le_majority {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) :
    d4ArmMinority label core ≤ d4ArmMajority label core := by
  rcases label <;> simp [d4ArmMinority, d4ArmMajority]

theorem card_concreteBallotWord (up down : ℕ) (h : down ≤ up) :
    @Fintype.card (ConcreteBallotWord up down)
      (concreteBallotWordFintype up down) = ballotNumber (up + down) down := by
  letI := concreteBallotWordFintype up down
  rw [← card_recursiveBallot_of_le up down h]
  exact Fintype.card_congr (recursiveBallotEquivConcrete up down).symm

theorem card_d4ArmPath {m : ℕ} (label : MicroLabel)
    (core : SimplexPoint (m + 2)) (hroom : d4ArmRoom label core) :
    @Fintype.card (D4ArmPath m label core)
      (d4ArmPathFintype label core hroom) =
      ballotNumber
        (d4ArmMajority label core + d4ArmMinority label core)
        (d4ArmMinority label core) := by
  letI := d4ArmPathFintype label core hroom
  letI := concreteBallotWordFintype (d4ArmMajority label core)
    (d4ArmMinority label core)
  rw [← card_concreteBallotWord _ _
    (d4ArmMinority_le_majority label core)]
  exact Fintype.card_congr (d4ArmPathEquivConcrete label core hroom)

theorem card_d4ArmPath_zero {m : ℕ} (core : SimplexPoint (m + 2))
    (hroom : d4ArmRoom .zero core) :
    @Fintype.card (D4ArmPath m .zero core)
      (d4ArmPathFintype .zero core hroom) =
      ballotNumber (core.u + 2 * core.v) core.v := by
  rw [card_d4ArmPath]
  simp [d4ArmMajority, d4ArmMinority]
  congr 1
  omega

theorem card_d4ArmPath_one {m : ℕ} (core : SimplexPoint (m + 2))
    (hroom : d4ArmRoom .one core) :
    @Fintype.card (D4ArmPath m .one core)
      (d4ArmPathFintype .one core hroom) =
      ballotNumber (core.v + 2 * core.w) core.w := by
  rw [card_d4ArmPath]
  simp [d4ArmMajority, d4ArmMinority]
  congr 1
  omega

theorem card_d4ArmPath_two {m : ℕ} (core : SimplexPoint (m + 2))
    (hroom : d4ArmRoom .two core) :
    @Fintype.card (D4ArmPath m .two core)
      (d4ArmPathFintype .two core hroom) =
      ballotNumber (core.w + 2 * core.u) core.u := by
  rw [card_d4ArmPath]
  simp [d4ArmMajority, d4ArmMinority]
  congr 1
  omega

end FiniteDefects

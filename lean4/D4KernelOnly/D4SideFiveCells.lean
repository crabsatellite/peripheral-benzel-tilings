import D4KernelOnly.D4PlacementBoundaryCancellation
import BenzelProblem6Kernel.HexCellDirectedEdgeIncidence

/-! # Explicit inside cells on the d=4 side-five boundary -/

namespace FiniteDefects

open BenzelProblem6Kernel

def d4SideFiveFixedCells (m : ℕ) : List Cell :=
  [((m : ℤ) + 1, 1), ((m : ℤ) + 2, -1), ((m : ℤ) + 2, 0)]

def d4SideFiveFirstFamily (m : ℕ) : List Cell :=
  (List.range m).map fun r =>
    ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1)

def d4SideFiveSecondFamily (m : ℕ) : List Cell :=
  (List.range (m + 1)).map fun r =>
    (-((m : ℤ)) + 2 * (r : ℤ), (m : ℤ) + 2 - r)

def d4SideFiveCells (m : ℕ) : List Cell :=
  (List.range (m + 1)).map (fun r =>
    ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1)) ++
  [((m : ℤ) + 2, 0), ((m : ℤ) + 1, 1)] ++
  (List.range (m + 1)).map (fun r =>
    ((m : ℤ) - 2 * (r : ℤ), (r : ℤ) + 2))

theorem mem_d4SideFiveCells_explicit (m : ℕ) (cell : Cell) :
    cell ∈ d4SideFiveCells m ↔
      (∃ r : ℕ, r < m + 1 ∧
        cell = ((r : ℤ) + 2, (r : ℤ) - (m : ℤ) - 1)) ∨
      cell = ((m : ℤ) + 2, 0) ∨
      cell = ((m : ℤ) + 1, 1) ∨
      (∃ r : ℕ, r < m + 1 ∧
        cell = ((m : ℤ) - 2 * (r : ℤ), (r : ℤ) + 2)) := by
  simp [d4SideFiveCells]
  aesop

theorem mem_d4SideFiveCells_iff (m : ℕ) (cell : Cell) :
    cell ∈ d4SideFiveCells m ↔
      inBenzel (m + 4) (2 * m + 4) cell ∧
        ¬inBenzel (m + 4) (2 * m + 4)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  rw [mem_d4SideFiveCells_explicit]
  simp only [inBenzel, neighboringCell]
  constructor
  · intro hmem
    rcases hmem with h | h | h | h
    · obtain ⟨r, hr, hcell⟩ := h
      simp only [Prod.mk.injEq] at hcell
      rcases hcell with ⟨rfl, rfl⟩
      omega
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      omega
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      omega
    · obtain ⟨r, hr, hcell⟩ := h
      simp only [Prod.mk.injEq] at hcell
      rcases hcell with ⟨rfl, rfl⟩
      omega
  · intro hboundary
    have hcases :
        j - i = -((m : ℤ)) - 3 ∨
        1 - i - 2 * j = -((m : ℤ)) - 3 ∨
        2 * i + j - 1 ≥ 2 * (m : ℤ) + 2 := by
      omega
    rcases hcases with hfirst | hsecond | hupper
    · left
      have hnonneg : 0 ≤ i - 2 := by omega
      let r : ℕ := Int.toNat (i - 2)
      have hrCast : (r : ℤ) = i - 2 := by
        dsimp [r]
        rw [Int.toNat_of_nonneg hnonneg]
      refine ⟨r, ?_, ?_⟩
      · exact_mod_cast (show (r : ℤ) < m + 1 by omega)
      · apply Prod.ext
        · simp [hrCast]
        · simp [hrCast]
          omega
    · right; right; right
      have hnonneg : 0 ≤ j - 2 := by omega
      let r : ℕ := Int.toNat (j - 2)
      have hrCast : (r : ℤ) = j - 2 := by
        dsimp [r]
        rw [Int.toNat_of_nonneg hnonneg]
      refine ⟨r, ?_, ?_⟩
      · exact_mod_cast (show (r : ℤ) < m + 1 by omega)
      · apply Prod.ext
        · simp [hrCast]
          omega
        · simp [hrCast]
    · by_cases hi : i = (m : ℤ) + 1
      · exact Or.inr (Or.inr (Or.inl (by apply Prod.ext <;> omega)))
      · by_cases hi2 : i = (m : ℤ) + 2
        · by_cases hj : j = -1
          · left
            refine ⟨m, by omega, ?_⟩
            apply Prod.ext <;> simp [hi2, hj]
          · exact Or.inr (Or.inl (by apply Prod.ext <;> omega))
        · omega

def d4SideFiveNegativeFixedCells (m : ℕ) : List Cell :=
  [(-((m : ℤ)) - 2, (m : ℤ)),
    (-((m : ℤ)) - 2, (m : ℤ) + 1),
    (-((m : ℤ)) - 2, (m : ℤ) + 2)]

def d4SideFiveNegativePairs (m : ℕ) : List Cell :=
  (List.range m).flatMap fun r =>
    [(-((m : ℤ)) - 1 + r, (m : ℤ) - 2 - 2 * (r : ℤ)),
      (-((m : ℤ)) - 1 + r, (m : ℤ) - 1 - 2 * (r : ℤ))]

def d4SideFiveNegativeCells (m : ℕ) : List Cell :=
  ((List.range (m + 1)).flatMap fun r =>
    [(-((m : ℤ)) - 2 + (r : ℤ),
        (m : ℤ) + 1 - 2 * (r : ℤ)),
      (-((m : ℤ)) - 2 + (r : ℤ),
        (m : ℤ) - 2 * (r : ℤ))]) ++
  [(-1, -((m : ℤ)) - 1), (-((m : ℤ)) - 2, (m : ℤ) + 2)]

theorem mem_d4SideFiveNegativeCells_explicit (m : ℕ) (cell : Cell) :
    cell ∈ d4SideFiveNegativeCells m ↔
      (∃ r : ℕ, r < m + 1 ∧
        (cell = (-((m : ℤ)) - 2 + (r : ℤ),
          (m : ℤ) + 1 - 2 * (r : ℤ)) ∨
        cell = (-((m : ℤ)) - 2 + (r : ℤ),
          (m : ℤ) - 2 * (r : ℤ)))) ∨
      cell = (-1, -((m : ℤ)) - 1) ∨
      cell = (-((m : ℤ)) - 2, (m : ℤ) + 2) := by
  simp [d4SideFiveNegativeCells]

theorem mem_d4SideFiveNegativeCells_iff (m : ℕ) (cell : Cell) :
    cell ∈ d4SideFiveNegativeCells m ↔
      ¬inBenzel (m + 4) (2 * m + 4) cell ∧
        inBenzel (m + 4) (2 * m + 4)
          (neighboringCell cell .side₅) := by
  rcases cell with ⟨i, j⟩
  rw [mem_d4SideFiveNegativeCells_explicit]
  simp only [inBenzel, neighboringCell]
  constructor
  · intro hmem
    rcases hmem with h | h | h
    · obtain ⟨r, hr, h | h⟩ := h
      · simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        omega
      · simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        omega
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      omega
    · simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      omega
  · intro hboundary
    by_cases hend : i = -1 ∧ j = -((m : ℤ)) - 1
    · right; left
      exact Prod.ext hend.1 hend.2
    · by_cases hlast : i = -((m : ℤ)) - 2 ∧ j = (m : ℤ) + 2
      · right; right
        exact Prod.ext hlast.1 hlast.2
      · left
        have hnonneg : 0 ≤ i + (m : ℤ) + 2 := by omega
        let r : ℕ := Int.toNat (i + (m : ℤ) + 2)
        have hrCast : (r : ℤ) = i + (m : ℤ) + 2 := by
          dsimp [r]
          rw [Int.toNat_of_nonneg hnonneg]
        refine ⟨r, ?_, ?_⟩
        · exact_mod_cast (show (r : ℤ) < m + 1 by omega)
        · by_cases hj : j = (m : ℤ) + 1 - 2 * (r : ℤ)
          · left
            apply Prod.ext
            · simp [hrCast]
            · exact hj
          · right
            apply Prod.ext
            · simp [hrCast]
            · simp [hrCast]
              omega

theorem directedEdgeCoefficient_d4CellBoundaries_sideFive
    (m : ℕ) (cell : Cell) :
    directedEdgeCoefficient
        (orientedCellBoundaryList (d4CellValueList m))
        (cellBoundaryEdgeAt cell .side₅) =
      (if cell ∈ d4SideFiveCells m then (1 : ℤ) else 0) -
        (if cell ∈ d4SideFiveNegativeCells m then (1 : ℤ) else 0) := by
  rw [directedEdgeCoefficient_orientedCellBoundaryList]
  have hcellCount := lawful_count_eq_indicator_of_nodup
    (d4CellValueList m) (d4CellValueList_nodup m) cell
  have hneighborCount := lawful_count_eq_indicator_of_nodup
    (d4CellValueList m) (d4CellValueList_nodup m)
      (neighboringCell cell .side₅)
  rw [hcellCount, hneighborCount]
  by_cases hcell : inBenzel (m + 4) (2 * m + 4) cell <;>
    by_cases hneighbor : inBenzel (m + 4) (2 * m + 4)
      (neighboringCell cell .side₅) <;>
    simp [mem_d4CellValueList_iff, mem_d4SideFiveCells_iff,
      mem_d4SideFiveNegativeCells_iff, hcell, hneighbor]

end FiniteDefects

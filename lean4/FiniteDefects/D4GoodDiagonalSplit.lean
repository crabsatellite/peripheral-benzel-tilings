import FiniteDefects.D4GoodDiagonal

/-! # Finite split equivalence for diagonal multiplication -/

namespace FiniteDefects

open Finset BigOperators Finsupp

abbrev GoodSplitFiber (degree : ℕ) :=
  Σ n : GoodFiber degree, ↥(Finset.antidiagonal n.1)

abbrev GoodPairedFibers (degree : ℕ) :=
  Σ ij : ↥(Finset.antidiagonal degree),
    GoodFiber ij.1.1 × GoodFiber ij.1.2

noncomputable def goodSplitFiberFintype (degree : ℕ)
    [Fintype (GoodFiber degree)] : Fintype (GoodSplitFiber degree) where
  elems := (Finset.univ : Finset (GoodFiber degree)).sigma
    (fun x => (Finset.univ : Finset ↥(Finset.antidiagonal x.1)))
  complete := by intro x; simp

noncomputable def goodPairedFibersFintype (degree : ℕ)
    [(d : ℕ) → Fintype (GoodFiber d)] : Fintype (GoodPairedFibers degree) where
  elems := (Finset.univ : Finset ↥(Finset.antidiagonal degree)).sigma
    (fun ij => (Finset.univ : Finset (GoodFiber ij.1.1)).product
      (Finset.univ : Finset (GoodFiber ij.1.2)))
  complete := by intro x; simp

noncomputable def goodSplitEquivPaired (degree : ℕ) :
    GoodSplitFiber degree ≃ GoodPairedFibers degree where
  toFun := fun split => by
    let left := split.2.1.1
    let right := split.2.1.2
    have hsum := Finset.mem_antidiagonal.mp split.2.2
    let ij : ↥(Finset.antidiagonal degree) :=
      ⟨(goodTotal left, goodTotal right), by
        rw [Finset.mem_antidiagonal, ← goodTotal_add, hsum, split.1.2]⟩
    exact ⟨ij, ⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩⟩
  invFun := fun paired => by
    let left := paired.2.1.1
    let right := paired.2.2.1
    have hij := Finset.mem_antidiagonal.mp paired.1.2
    let total : GoodFiber degree := ⟨left + right, by
      rw [goodTotal_add, paired.2.1.2, paired.2.2.2, hij]⟩
    exact ⟨total, ⟨(left, right), Finset.mem_antidiagonal.mpr rfl⟩⟩
  left_inv := by
    intro split
    rcases split with ⟨⟨total, htotal⟩, ⟨⟨left, right⟩, hsum⟩⟩
    have hsumEq := Finset.mem_antidiagonal.mp hsum
    dsimp at hsumEq ⊢
    subst total
    rfl
  right_inv := by
    intro paired
    rcases paired with
      ⟨⟨⟨leftDegree, rightDegree⟩, hdegrees⟩,
        ⟨left, hleft⟩, ⟨right, hright⟩⟩
    dsimp at hleft hright ⊢
    subst leftDegree
    subst rightDegree
    rfl

end FiniteDefects

import FiniteDefects.D4Area

/-! # Exact d=4 stone-count target, without a reference gate -/

namespace FiniteDefects

def d4KernelRightStoneCount {m : ℕ} (tiling : D4LiteralTiling m) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = .stone).card

def d4KernelStoneTarget (m : ℕ) : ℕ :=
  (m * m + m + 2) / 2

def D4KernelStoneStatement : Prop :=
  ∀ (m : ℕ) (tiling : D4LiteralTiling m),
    d4KernelRightStoneCount tiling = d4KernelStoneTarget m

theorem two_dvd_d4KernelStoneTargetNumerator (m : ℕ) :
    2 ∣ m * m + m + 2 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · refine ⟨2 * k * k + k + 1, ?_⟩
    ring
  · refine ⟨2 * k * k + 3 * k + 2, ?_⟩
    ring

theorem twice_d4KernelStoneTarget (m : ℕ) :
    2 * d4KernelStoneTarget m = m * m + m + 2 := by
  exact Nat.mul_div_cancel' (two_dvd_d4KernelStoneTargetNumerator m)

end FiniteDefects

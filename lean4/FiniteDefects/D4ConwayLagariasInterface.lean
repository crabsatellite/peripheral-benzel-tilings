import FiniteDefects.D4Area

/-! # Typed statement of the d=4 Conway--Lagarias specialization -/

namespace FiniteDefects

def d4RightStoneCount {m : ℕ} (tiling : D4LiteralTiling m) : ℕ :=
  (tiling.1.filter fun placement => placement.tile = .stone).card

def d4ConwayLagariasStoneTarget (m : ℕ) : ℕ :=
  (m * m + m + 2) / 2

def D4ConwayLagariasStatement : Prop :=
  ∀ (m : ℕ) (tiling : D4LiteralTiling m),
    d4RightStoneCount tiling = d4ConwayLagariasStoneTarget m

end FiniteDefects

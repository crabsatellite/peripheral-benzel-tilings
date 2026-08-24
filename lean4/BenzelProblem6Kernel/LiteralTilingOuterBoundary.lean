import BenzelProblem6Kernel.LiteralBoundaryFactorizationConsumer

/-!
# The literal tiling boundary is the explicit peripheral cycle

This is the complete commutative geometric boundary statement.  It combines
the exact-cover cell permutation, local trihex edge cancellation, and the
six-side arithmetic classification.
-/

namespace BenzelProblem6Kernel

theorem literalTilingBoundaryKeys_eq_reducedPeripheral {m : ℕ}
    (tiling : LiteralTiling m) :
    literalTilingBoundaryKeys tiling =
      labeledBoundaryKeys (literalReducedPeripheralBoundary m) := by
  rw [literalTilingBoundaryKeys_eq_benzelCells,
    literalReducedPeripheralBoundary_keys_eq_benzelXor]

end BenzelProblem6Kernel

import D4KernelOnly.D4BoundaryFactorizationKernel

/-!
# Premise-free compatibility export

The historical downstream files consume the name
`d4ConwayLagariasReference`.  In the public package that name is a theorem,
not an axiom: it is supplied by the kernel-only boundary factorization.
-/

namespace FiniteDefects

theorem d4ConwayLagariasReference : D4ConwayLagariasStatement :=
  d4ConwayLagariasStatement_proved

end FiniteDefects

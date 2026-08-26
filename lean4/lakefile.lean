import Lake
open Lake DSL

package "PeripheralBenzelTilings" where
  version := v!"2.0.1"
  weakLeanArgs := #["--trust=0", "-M16384"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

lean_lib BenzelProblem6Kernel

lean_lib FiniteDefects

lean_lib D4KernelOnly

@[default_target]
lean_lib PeripheralBenzelPublication

import Lake
open Lake DSL

package "BenzelProblem6" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib BenzelProblem6Kernel

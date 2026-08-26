# Combined kernel-only Lean 4 formalization

This directory is one Mathlib-only package containing three source libraries:

- `BenzelProblem6Kernel`: Propp Problem 6;
- `FiniteDefects`: literal `d=4` path and generating-function development;
- `D4KernelOnly`: premise-free Conway--Lagarias producer, general
  finite-defect theorem, carrier bridges, and final audits.

The combined root is `PeripheralBenzelPublication.lean`.  The source contains
no project-specific axiom, `opaque` theorem, `sorry`, `admit`, or native
evaluation bridge.  All publication endpoints report only `propext`,
`Classical.choice`, and `Quot.sound`.

Build with:

```powershell
lake build PeripheralBenzelPublication
```

The package pins Lean and Mathlib 4.16.0, compiles with `--trust=0`, and uses a
16GB per-process ceiling.  Run `python ..\verify_all.py` for the complete
paper-label and axiom audit.

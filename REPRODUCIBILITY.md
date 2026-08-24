# Reproducibility

## Kernel-only formal verification

The Lean project uses `leanprover/lean4:v4.16.0` and the pinned Mathlib
revision in `lean4/lake-manifest.json`. From the repository root, run:

```powershell
python verify_formula_map.py
```

This command fails closed unless all of the following hold:

- the manuscript's 19 theorem/formula labels exactly equal the map labels;
- all 43 unique mapped endpoints and all 124 publication endpoints have axiom
  receipts;
- the publication root, theorem map, formula map, and both axiom audits compile
  with `--trust=0`;
- no project axiom, opaque declaration, `sorry`, `admit`, native-evaluation
  bridge, or compiler-trust escape occurs in the source tree;
- every endpoint depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.

Expected receipt:

```text
formula_map_kernel_audit=passed labels=19 endpoints=43 publication_endpoints=124 sources=294 trust=0 axioms=Classical.choice,Quot.sound,propext
```

The verifier applies a 30GB Lean process limit. Keep the aggregate build below
32GB.

## Direct Lean commands

```powershell
Set-Location lean4
lake build BenzelProblem6Kernel.PublicationRoot
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel\KernelTheoremMap.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel\ManuscriptFormulaMap.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel\AxiomAudit.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel\ManuscriptAxiomAudit.lean
```

## Paper

```powershell
.\build_paper.ps1
```

The rendered manuscript is `output/pdf/benzel_problem6.pdf`.

## Release cache

The release cache is optional. It is bound to the exact release source and
contains only files under `lean4/.lake/build/lib/BenzelProblem6Kernel` with
extensions `.olean`, `.ilean`, `.trace`, and `.hash`. Verify the release asset
against its SHA-256 manifest before extraction at the repository root.

# Peripheral Benzel Tilings with Right Stones and Three Bone Orientations

This repository contains the manuscript and the complete kernel-only Lean 4
formalization of Propp's Problem 6 for type-103 peripheral benzel tilings.

## Main result

For every integer `n >= 5`, the number of tilings of the `(n, 2n-3)`-benzel by
right stones and all three bone orientations is

```text
T_103(n, 2n-3) = (3n+3)(3n-7)! / ((n-5)!(2n-1)!).
```

The proof sends each literal exact-cover tiling to a directed `Y` consisting
of three labelled ballot paths, enumerates both sink chiralities, and evaluates
the resulting three-variable generating function.

## Formal verification

The publication root is
`lean4/BenzelProblem6Kernel/PublicationRoot.lean`. The development contains no
project axiom, opaque theorem, `sorry`, `admit`, native-evaluation bridge, or
published-result premise.

The machine-readable manuscript map
`lean4/BenzelProblem6Kernel/ManuscriptFormulaMap.lean` covers all 19 numbered
manuscript labels through 43 exact Lean endpoints. `AxiomAudit.lean` covers all
124 publication endpoints. The complete audit reports only Lean/Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` principles.

Run the fail-closed audit from the repository root:

```powershell
python verify_formula_map.py
```

Expected receipt:

```text
formula_map_kernel_audit=passed labels=19 endpoints=43 publication_endpoints=124 sources=294 trust=0 axioms=Classical.choice,Quot.sound,propext
```

The project uses Lean 4.16.0 and Mathlib 4.16.0. The verifier enforces a
30GB per-process ceiling, below the project's 32GB aggregate limit.

## Contents

- `benzel_problem6.tex`, `references.bib`: canonical manuscript source.
- `output/pdf/benzel_problem6.pdf`: rendered manuscript.
- `lean4/`: complete Mathlib-only Lean project.
- `FORMULA_MAP.md`: human-readable manuscript-label map.
- `verify_formula_map.py`: exact-label, proof-escape, trust-zero, and axiom audit.
- `REPRODUCIBILITY.md`: exact build and verification commands.

## Prebuilt Lean cache

Release assets include a source-bound Lean project cache and SHA-256 manifest.
The cache contains only project `.olean`, `.ilean`, `.trace`, and `.hash`
artifacts; it does not include Mathlib or internal research files. On the exact
release tag, obtain Mathlib's cache and then extract the project cache at the
repository root so that it restores `lean4/.lake/build/lib/BenzelProblem6Kernel`.

## Archival identifiers

- Paper concept DOI: [10.5281/zenodo.22057378](https://doi.org/10.5281/zenodo.22057378)
- Canonical repository: [crabsatellite/peripheral-benzel-tilings](https://github.com/crabsatellite/peripheral-benzel-tilings)

The paper and software records are linked on Zenodo. Cite a version DOI when
exact artifact identity is required and a concept DOI for the evolving record.

## Licensing

See `LICENSE.md`. Lean source, verification code, and repository documentation
are Apache-2.0; manuscript source and rendered PDFs are CC BY 4.0.

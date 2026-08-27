# Finite-Defect Path Models for Peripheral Benzel Tilings

This repository contains the combined manuscript and the complete kernel-only
Lean 4 formalization of two linked results for type-103 peripheral benzel
tilings: Propp's Problem 6 on the rigid diagonal `d=3`, and the finite-defect
hierarchy culminating in the complete first-defect diagonal `d=4`.

## Main results

### Propp's Problem 6: the rigid diagonal `d=3`

For every integer `n >= 5`,

```text
T_103(n, 2n-3) = (3n+3)(3n-7)! / ((n-5)!(2n-1)!).
```

### Finite defects and the first-defect diagonal `d=4`

For the finite-defect hierarchy, put `d = 2a-b`, `t = a-2`, and assume
`k >= 1` and `2k <= t+1`.  Every literal type-103 tiling satisfies

```text
d = 3k     => wrong-phase stones + three-owner bones = binom(k,2)
d = 3k + 1 => wrong-phase stones + three-owner bones = binom(k+1,2).
```

Thus `d=4` is the first one-defect diagonal.  Deleting its unique defect gives
three independent labelled ballot paths, leading to the algebraic generating
function for every `T_103(a, 2a-4)` proved in the manuscript.  This is a full
enumeration of the first-defect diagonal, not merely a structural corollary of
the Problem 6 formula.

## Formal verification

The combined publication root is
`lean4/PeripheralBenzelPublication.lean`.  The public Lean source contains no
project-specific axiom, `opaque` theorem, `sorry`, `admit`, native-evaluation
bridge, or published-result premise.  The historical compatibility name
`FiniteDefects.d4ConwayLagariasReference` is a proved theorem supplied by the
kernel-only boundary factorization.

The exact publication endpoints include:

- `BenzelProblem6Kernel.manuscript_main_theorem_proved`;
- `FiniteDefects.generalFiniteDefectKernelOnly`;
- `FiniteDefects.offsetD4LiteralTilingEquiv`;
- `FiniteDefects.d4LiteralTilingEquivPathData_kernelOnly`;
- `FiniteDefects.d4LiteralTilingCount_ballot_formula_kernelOnly`;
- `FiniteDefects.d4GeneratingFunctionKernelOnly`.

All final audits report only Lean/Mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound` principles.  The project uses Lean 4.16.0,
Mathlib 4.16.0, `--trust=0`, and a 16GB per-process ceiling.
The release gate also requires a nonempty Lean endpoint map for every one of
the 32 labelled results in the first-defect part; the current map has 46 unique
audited endpoints.

Run the complete fail-closed audit from the repository root:

```powershell
python verify_all.py
```

## Contents

- `peripheral_benzel_tilings.tex`, `d4_extension.tex`, `references.bib`:
  canonical combined manuscript source.
- `output/pdf/peripheral_benzel_tilings.pdf`: rendered manuscript.
- `lean4/BenzelProblem6Kernel/`: Problem 6 formalization.
- `lean4/FiniteDefects/`: literal first-defect path and generating-function
  development.
- `lean4/D4KernelOnly/`: premise-free boundary factorization, general
  finite-defect theorem, exact carrier bridges, and final audits.
- `FORMULA_MAP.md`: human-readable paper-to-Lean map.
- `verify_formula_map.py`, `verify_all.py`: exact-label, source-policy,
  trust-zero, and axiom audits.
- `REPRODUCIBILITY.md`: build, verification, and cache instructions.

## Prebuilt Lean cache

Release assets include a source-bound Lean project cache and SHA-256 manifest.
The cache contains only project `.olean`, `.ilean`, `.trace`, and `.hash`
artifacts; it excludes Mathlib and research records.  On the exact release tag,
obtain Mathlib's cache and extract the project cache at the repository root so
that it restores the project artifacts under `lean4/.lake/build/lib/`.

## Archival identifiers

- Paper concept DOI: [10.5281/zenodo.22057378](https://doi.org/10.5281/zenodo.22057378)
- Software/formalization concept DOI: [10.5281/zenodo.22079396](https://doi.org/10.5281/zenodo.22079396)
- Repository: [crabsatellite/peripheral-benzel-tilings](https://github.com/crabsatellite/peripheral-benzel-tilings)

Cite a version DOI when exact artifact identity is required and a concept DOI
for the evolving record.

## Licensing

See `LICENSE.md`.  Lean source, verification code, and repository documentation
are Apache-2.0; manuscript source and rendered PDFs are CC BY 4.0.

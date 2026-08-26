# Reproducibility

## Pinned environment

- Lean: `v4.16.0`
- Mathlib: `v4.16.0` at the revision pinned by `lean4/lake-manifest.json`
- Trust setting: `--trust=0`
- Per-process limit: `-M16384`

## Verify the complete formalization

From the repository root:

```powershell
python verify_all.py
```

This checks the 20-label Problem 6 map, the 32-label first-defect map, source
policy, the two exact theorem maps, the combined publication root, and all
reported axioms.

To compile the combined root directly:

```powershell
cd lean4
lake build PeripheralBenzelPublication
```

## Build the paper

With MiKTeX or another installation providing `pdflatex` and `bibtex`:

```powershell
.\build_paper.ps1
```

The final artifact is `output/pdf/peripheral_benzel_tilings.pdf`.  The build
fails on unresolved references, LaTeX warnings, and overfull or underfull
boxes.

## Restore the release cache

Release assets contain a zip archive and JSON manifest bound to the exact
release source tree.  First obtain Mathlib's cache for the pinned revision,
then extract the project cache at the repository root.  It restores only
project artifacts under `lean4/.lake/build/lib/`; Mathlib and internal
research files are not included.

After extraction, rerun `python verify_all.py`.  Lean checks imported `.olean`
artifacts and recompiles any source whose cache is stale.

# Benzel Problem 6 kernel formalization

This Lean 4 project uses Mathlib only and contains no project axiom or theorem
premise.  The publication root exports the Conway--Lagarias stone-count
theorem, the literal tiling/path-model equivalence, and the manuscript's main
enumeration theorem unconditionally.

Current kernel-checked modules additionally include the literal twelve-branch
prototile energy table, the two-way literal benzel/owner carrier equivalence,
the exact benzel area, the complete finite owner-energy sum, all six
two-owner bone edge profiles, inverse owner coordinates, the strict-potential
no-cycle theorem, unique-sink count algebra, and the final adjacent-binomial
simplification. The positive-chirality adjacent-binomial factors and their
cyclic cancellation are also kernel-checked, as is a genuine recursive ballot
path carrier with its binomial-difference cardinality. See the root
`FORMULA_MAP.md` and `BenzelProblem6Kernel/ManuscriptFormulaMap.lean` for the
exact 19-label manuscript-to-Lean correspondence.  All 43 unique mapped
endpoints have individual axiom receipts in `ManuscriptAxiomAudit.lean`. The geometric
closure constructs the exact peripheral boundary, peels every literal tile,
proves that the terminal support is a finite tree, and cancels its closed word
in the involutive edge-label quotient.

Build the current root with:

```powershell
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel/PublicationRoot.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel/KernelTheoremMap.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel/ManuscriptFormulaMap.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel/AxiomAudit.lean
lake env lean --trust=0 -M 30000 -q BenzelProblem6Kernel/ManuscriptAxiomAudit.lean
```

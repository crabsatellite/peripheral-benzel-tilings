# Exact manuscript-to-Lean formula map

Canonical manuscript: `benzel_problem6.tex`
Kernel namespace: `BenzelProblem6Kernel`

Every numbered theorem, lemma, proposition, corollary, and equation in the
manuscript appears below under its literal TeX label.  The executable source of
truth is `lean4/BenzelProblem6Kernel/ManuscriptFormulaMap.lean`; the submission
audit rejects any missing or extra paper label, any unmapped label, any mapped
endpoint without an axiom receipt, and any nonstandard axiom.

| Paper label | Exact Lean endpoint(s) | Correspondence |
|---|---|---|
| `thm:main` | `manuscript_thm_main` | Literal `type103TilingCount n`, hypothesis `5 ≤ n`, and the displayed factorial quotient. |
| `eq:ballot-form` | `manuscript_eq_ballot_form` | The two-binomial expression and the displayed rational-binomial expression over `ℚ`. |
| `lem:tile-counts` | `manuscript_lem_tile_counts` | Both printed counts at the literal `n` parameter: right stones and bones. |
| `eq:owner-coordinates` | `manuscript_eq_owner_coordinates` | All three `/3` owner-coordinate identities over `ℚ`, with the manuscript signs and variable order. |
| `lem:owner-simplex` | `manuscript_owner_anchor_injective`; `manuscript_lem_owner_simplex_meets`; `manuscript_lem_owner_simplex_partition` | Injective simplex-to-owner anchors, every simplex owner meeting the benzel, unique owner/label representation of every benzel cell, and the three exact boundary-presence conditions. |
| `eq:cell-energy` | `manuscript_eq_cell_energy` | The three literal integer energy definitions `q+r`, `-q`, and `-r`. |
| `lem:energy-table` | `manuscript_lem_energy_table_values`; `manuscript_lem_energy_table_profiles`; `manuscript_lem_energy_table_directions` | All twelve table values and the six two-owner label-preserving directed profiles. |
| `prop:energy-rigidity` | `manuscript_prop_energy_rigidity` | Every chosen stone is in phase; every chosen bone produces a permitted labelled directed edge. |
| `prop:Y-bijection` | `manuscript_prop_Y_bijection`; `nonempty_literalYPathData`; both literal/path round-trip theorems | The literal exact-cover carrier is equivalent to the complete sink/chirality/arm carrier; concrete labelled paths exist and both reconstruction composites are identities. |
| `lem:independent-arms` | `manuscript_lem_independent_arms_positive_factors`; `manuscript_lem_independent_arms_negative_factors`; the two triple-count endpoints; six prefix-bound theorems; six pairwise meet-only-at-sink theorems | All six individual arm counts and all three path-pair separations for both chiralities. |
| `cor:fixed-sink` | `manuscript_eq_Pxyz`; `manuscript_eq_Qxyz`; `manuscript_eq_QoverP` | The two fixed-sink products and their displayed quotient. |
| `eq:Pxyz` | `manuscript_eq_Pxyz` | Exact cyclic positive-chirality binomial product. |
| `eq:Qxyz` | `manuscript_eq_Qxyz` | Exact cyclic ballot-difference product, including the `k=0` convention through `choosePred`. |
| `eq:QoverP` | `manuscript_eq_QoverP` | The displayed rational quotient, not merely a denominator-cleared surrogate. |
| `prop:generating-functions` | `manuscript_prop_generating_functions` | The conjunction of the three displayed formal-power-series identities. |
| `eq:Pgf` | `manuscript_eq_Pgf` | `P(t)` with the exact linear and quadratic denominator factors. |
| `eq:Qgf` | `manuscript_eq_Qgf` | `Q(t)=(2-T)^3P(t)` over `ℚ⟦X⟧`. |
| `eq:Ygf` | `manuscript_eq_Ygf` | The total series `T^9(3-T)/(3-2T)` in inverse-series form. |
| `eq:constant-term` | `manuscriptPositiveConstantTermSeries`; `manuscript_eq_constant_term`; coefficient-factorization endpoints | The displayed three-variable constant term after expanding the three geometric denominators: its coefficient is defined by the literal multivariate numerator and the three powers `φ_a^x φ_b^y φ_c^z`, then proved equal to `P(t)`. |

`KernelTheoremMap.lean` verifies that the exact endpoints are reachable from
`PublicationRoot.lean`.  `ManuscriptAxiomAudit.lean` covers all 43 unique
mapped declarations.  `AxiomAudit.lean` independently covers all 124
`publication_*` declarations.  Both audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

import BenzelProblem6Kernel.PublicationRoot

/-!
# Exact manuscript label map

Every numbered theorem, lemma, proposition, corollary, and equation in
`benzel_problem6.tex` is listed exactly once below.  Labels with several
mathematical clauses intentionally map to several kernel endpoints.
-/

-- thm:main
#check BenzelProblem6Kernel.manuscript_thm_main

-- eq:ballot-form
#check BenzelProblem6Kernel.manuscript_eq_ballot_form

-- lem:tile-counts
#check BenzelProblem6Kernel.manuscript_lem_tile_counts

-- eq:owner-coordinates
#check BenzelProblem6Kernel.manuscript_eq_owner_coordinates

-- lem:owner-simplex
#check BenzelProblem6Kernel.manuscript_owner_anchor_injective
#check BenzelProblem6Kernel.manuscript_lem_owner_simplex_meets
#check BenzelProblem6Kernel.manuscript_lem_owner_simplex_partition

-- eq:cell-energy
#check BenzelProblem6Kernel.manuscript_eq_cell_energy

-- lem:energy-table
#check BenzelProblem6Kernel.manuscript_lem_energy_table_values
#check BenzelProblem6Kernel.manuscript_lem_energy_table_profiles
#check BenzelProblem6Kernel.manuscript_lem_energy_table_directions

-- prop:energy-rigidity
#check BenzelProblem6Kernel.manuscript_prop_energy_rigidity

-- prop:Y-bijection
#check BenzelProblem6Kernel.manuscript_prop_Y_bijection
#check BenzelProblem6Kernel.nonempty_literalYPathData
#check BenzelProblem6Kernel.pathModelToLiteralTiling_literalTilingToPathModel
#check BenzelProblem6Kernel.literalTilingToPathModel_pathModelToLiteralTiling

-- lem:independent-arms
#check BenzelProblem6Kernel.manuscript_lem_independent_arms_positive_factors
#check BenzelProblem6Kernel.manuscript_lem_independent_arms_negative_factors
#check BenzelProblem6Kernel.manuscript_lem_independent_arms_positive_count
#check BenzelProblem6Kernel.manuscript_lem_independent_arms_negative_count
#check BenzelProblem6Kernel.positive_labelZero_prefix_bounds
#check BenzelProblem6Kernel.positive_labelOne_prefix_bounds
#check BenzelProblem6Kernel.positive_labelTwo_prefix_bounds
#check BenzelProblem6Kernel.negative_labelZero_prefix_bounds
#check BenzelProblem6Kernel.negative_labelOne_prefix_bounds
#check BenzelProblem6Kernel.negative_labelTwo_prefix_bounds
#check BenzelProblem6Kernel.positive_arms_zero_one_meet_only_at_sink
#check BenzelProblem6Kernel.positive_arms_one_two_meet_only_at_sink
#check BenzelProblem6Kernel.positive_arms_two_zero_meet_only_at_sink
#check BenzelProblem6Kernel.negative_arms_zero_one_meet_only_at_sink
#check BenzelProblem6Kernel.negative_arms_one_two_meet_only_at_sink
#check BenzelProblem6Kernel.negative_arms_two_zero_meet_only_at_sink

-- cor:fixed-sink
#check BenzelProblem6Kernel.manuscript_eq_Pxyz
#check BenzelProblem6Kernel.manuscript_eq_Qxyz
#check BenzelProblem6Kernel.manuscript_eq_QoverP

-- eq:Pxyz
#check BenzelProblem6Kernel.manuscript_eq_Pxyz

-- eq:Qxyz
#check BenzelProblem6Kernel.manuscript_eq_Qxyz

-- eq:QoverP
#check BenzelProblem6Kernel.manuscript_eq_QoverP

-- prop:generating-functions
#check BenzelProblem6Kernel.manuscript_prop_generating_functions

-- eq:Pgf
#check BenzelProblem6Kernel.manuscript_eq_Pgf

-- eq:Qgf
#check BenzelProblem6Kernel.manuscript_eq_Qgf

-- eq:Ygf
#check BenzelProblem6Kernel.manuscript_eq_Ygf

-- eq:constant-term
#check BenzelProblem6Kernel.manuscriptPositiveConstantTermSeries
#check BenzelProblem6Kernel.manuscript_eq_constant_term
#check BenzelProblem6Kernel.positiveGoodConstantTermCoefficient_eq
#check BenzelProblem6Kernel.positiveGoodConstantTermLevel_eq

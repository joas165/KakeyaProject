import Kakeya

/-!
# Axiom audit

Print the axioms used by the library's main analytic, combinatorial,
geometric, and conditional endpoint results. This file is an audit aid:
`lake build` checks that every audited declaration exists and is well-typed.
-/
-- Conditional analytic setup and finite tube multiplicity.
#print axioms Kakeya.Conditional.chi
#print axioms Kakeya.Conditional.chi_integrable
#print axioms Kakeya.Conditional.chi_nonneg
#print axioms Kakeya.Conditional.dimension_exponents
#print axioms Kakeya.Conditional.moment_from_level_budgets
#print axioms Kakeya.Conditional.norm_of_moment_bound
#print axioms Kakeya.Eighty4.tubeMultiplicity
#print axioms Kakeya.Eighty4.tubeMultiplicity_eq_count
#print axioms Kakeya.Eighty4.tubeMultiplicity_le_card
#print axioms Kakeya.Eighty4.tubeMultiplicity_measurable
#print axioms Kakeya.Eighty4.tubeMultiplicity_nonneg
#print axioms Kakeya.Eighty4.tubeMoment_integrable
-- Dyadic decomposition and logarithmic summation.
#print axioms Kakeya.Eighty4.DyadicIndex
#print axioms Kakeya.Eighty4.dyadicDepth
#print axioms Kakeya.Eighty4.dyadicIndex_card
#print axioms Kakeya.Eighty4.dyadicScale
#print axioms Kakeya.Eighty4.dyadicScale_pos
#print axioms Kakeya.Eighty4.exists_dyadic_index
#print axioms Kakeya.Eighty4.concreteDyadicBand
#print axioms Kakeya.Eighty4.concreteDyadicBand_cover
#print axioms Kakeya.Eighty4.concreteDyadicBand_upper
#print axioms Kakeya.Eighty4.concreteDyadicBand_measurable
#print axioms Kakeya.Eighty4.concreteDyadicBand_condition
#print axioms Kakeya.Eighty9.logarithmic_moment_from_level_budgets
#print axioms Kakeya.Eighty9.logarithmic_norm_from_level_budgets
-- Incidence counting and the canonical lower-incidence predicate.
#print axioms Kakeya.Seventy7.weight
#print axioms Kakeya.Seventy7.degree
#print axioms Kakeya.Seventy7.weighted_double_count
#print axioms Kakeya.Seventy7.degree_ge_one_of_covered
#print axioms Kakeya.Seventy7.incidence_double_count
#print axioms Kakeya.Eighty9.LowerIncidence
#print axioms Kakeya.Eighty9.onePieceIncidence
#print axioms Kakeya.Eighty9.onePieceIncidence_iff_eq
#print axioms Kakeya.Eighty9.pieceMap_injective_of_disjoint_nonempty
#print axioms Kakeya.Eighty9.reindexed_lower_incidence_of_pair_equiv
#print axioms Kakeya.Eighty9.reindexed_lower_incidence_of_pair_equiv_injective
#print axioms Kakeya.Eighty9.reindexed_lower_incidence_of_composed_range
#print axioms Kakeya.Eighty9.reindexed_card_eq_of_lower_incidence
#print axioms Kakeya.Eighty9.reindexed_card_le_of_lower_incidence
#print axioms Kakeya.Eighty9.reindexed_budget_of_lower_incidence
#print axioms Kakeya.Eighty9.reindexed_level_of_lower_incidence
-- Ninety21 Hall matching and the enlarged tube-label counting bridge.
#print axioms Kakeya.Ninety21.nonintersecting_bijection_of_greedy
#print axioms Kakeya.Ninety21.localized_nonintersecting_bijection
#print axioms Kakeya.Ninety21.tube_row_card_le_one
#print axioms Kakeya.Ninety21.tube_indices_subset_of_columns
#print axioms Kakeya.Ninety21.scaled_count_from_bijection
#print axioms Kakeya.Ninety21.scaled_count_from_selected_incidence
#print axioms Kakeya.Ninety21.exists_scaled_bijection_of_greedy
#print axioms Kakeya.Ninety21.transported_mass_sum
#print axioms Kakeya.Ninety21.localized_level_bound_of_bijection
#print axioms Kakeya.Ninety21.localized_level_bound_of_double_counted_bijection
-- Finite Vitali selection, greedy gains, and geometric reductions.
#print axioms Kakeya.exists_separated_centers_cover
#print axioms Kakeya.exists_disjoint_equal_balls_cover
#print axioms Kakeya.exists_disjoint_equal_balls_cover_target
#print axioms Kakeya.Eighty9.exists_tubeWise_equal_radius_vitali
#print axioms Kakeya.Eighty9.tubeWise_vitali_nonempty_fibers
#print axioms Kakeya.Eighty4.concreteGreedyGain
#print axioms Kakeya.Eighty4.concreteGreedyGain_measurable
#print axioms Kakeya.Eighty4.concreteGreedyGain_disjoint
#print axioms Kakeya.Eighty9.greedy_selected_card_budget
#print axioms Kakeya.Eighty9.mass_capture_of_original_localized_greedy_cover
#print axioms Kakeya.Eighty9.localized_cover_transfers_to_vitali
#print axioms Kakeya.Eighty9.exists_vitali_with_nonempty_localized_pieces
#print axioms Kakeya.Eighty9.localized_unitTube_ball_volume_le_of_frame
-- Conditional endpoint theorems. Geometric and incidence inputs remain explicit.
#print axioms Kakeya.Eighty9.LocalizedDyadicInputs
#print axioms Kakeya.Eighty9.LowerIncidenceAtLevels
#print axioms Kakeya.Eighty9.ComposedRangeCoverageAtLevels
#print axioms Kakeya.Eighty9.pair_map_composed_range_coverage_at_levels
#print axioms Kakeya.Eighty9.pair_map_lower_incidence_at_levels
#print axioms Kakeya.Eighty9.lowerIncidenceAtLevels_of_composed_range
#print axioms Kakeya.Eighty9.exact_reindexed_cardinality_at_every_level
#print axioms Kakeya.Eighty9.dyadic_level_budget_of_lower_incidence
#print axioms Kakeya.Eighty9.uniform_level_budget_of_lower_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_of_lower_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_moment_of_lower_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_of_composed_range
#print axioms Kakeya.Eighty9.full_conditional_kakeya_moment_of_composed_range
#print axioms Kakeya.Eighty9.SameBallRowBoundAtLevels
#print axioms Kakeya.Eighty9.SameBallIsRepresentativeAtLevels
#print axioms Kakeya.Eighty9.sameBallRowBoundAtLevels_of_representative
#print axioms Kakeya.Eighty9.same_ball_column_coverage_at_levels
#print axioms Kakeya.Eighty9.dyadic_level_budget_of_same_ball_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_of_same_ball_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_moment_of_same_ball_incidence
#print axioms Kakeya.Eighty9.full_conditional_kakeya_of_same_ball_representative
-- Tube-ball volume bounds in straight and arbitrary orientations.
#print axioms Kakeya.TubeBall.straightTube_inter_ball_volume_le
#print axioms Kakeya.TubeBall.straightTube_inter_ball_volume_le_explicit
#print axioms Kakeya.TubeBall.tubeBall_volume_le_of_measurePreserving_coordinates
#print axioms Kakeya.TubeBall.unitTube_ball_volume_le_of_frame
#print axioms Kakeya.TubeBall.directionCoordinates_measurePreserving
#print axioms Kakeya.TubeBall.unitTube_ball_volume_le_orthogonal_product
#print axioms Kakeya.TubeBall.localized_unitTube_ball_volume_le_orthogonal_product
#print axioms Kakeya.TubeBall.directionLine_closedBall_volume
#print axioms Kakeya.TubeBall.transverse_closedBall_volume
#print axioms Kakeya.TubeBall.unitTube_ball_volume_le_explicit_arbitrary_direction
#print axioms Kakeya.TubeBall.localized_unitTube_ball_volume_le_explicit_arbitrary_direction

module
import Kakeya
import Kakeya.Ninety21ConcreteTubeBallBridge
import Kakeya.Ninety21ConcreteGeometryReductions

/-!
# Axiom audit

Run `lake build` followed by `lake env lean Audit.lean` to check
the audited declarations and print their axiom dependencies.
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

-- Intersection-compatible Hall matching.
#print axioms Kakeya.Ninety21.intersecting_matching_of_degree_bounds
#print axioms Kakeya.Ninety21.extend_matching_to_bijection

-- Actual trimmed-piece bijections and exceptional-piece counts.
#print axioms Kakeya.Ninety64.theorem42_matching
#print axioms Kakeya.Ninety64.theorem42_actual_piece_bijection
#print axioms Kakeya.Ninety64.theorem42_restricted_matching
#print axioms Kakeya.Ninety64.theorem42_bijection_fixing_selected
#print axioms Kakeya.Ninety64.exceptional_piece_count_of_pair_injective
#print axioms Kakeya.Ninety64.exceptional_piece_count_of_packing
#print axioms Kakeya.Ninety64.exceptional_piece_scaled_budget

-- Extended original-tube map and its counting bounds.
#print axioms Kakeya.Ninety94.extensionHit_iff_original
#print axioms Kakeya.Ninety94.extendedMap_eq_some_iff
#print axioms Kakeya.Ninety94.extendedMap_eq_some_of_hit
#print axioms Kakeya.Ninety94.original_degree_ge
#print axioms Kakeya.Ninety94.extendedMap_fiber_ge
#print axioms Kakeya.Ninety94.q_mul_card_le_original
#print axioms Kakeya.Ninety94.q_mul_reindexed_card_le_original
#print axioms Kakeya.Ninety94.greedy_gain_common_point_unique

-- Ninety21 distinct-tube-count route to the logarithmic endpoint.
#print axioms Kakeya.Ninety21.SelectedIncidenceDyadicInputs
#print axioms Kakeya.Ninety21.dyadic_level_budget_of_selected_incidence
#print axioms Kakeya.Ninety21.uniform_level_budget_of_selected_incidence
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_selected_incidence
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_selected_incidence

-- Single retained-piece mass sum, with greedy capture discharged.
#print axioms Kakeya.Ninety21.SelectedIncidenceDyadicData
#print axioms Kakeya.Ninety21.GreedyCaptureAtLevels
#print axioms Kakeya.Ninety21.piece_mass_capture_of_greedy_cover
#print axioms Kakeya.Ninety21.inputs_of_greedy_cover
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_greedy_cover
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_greedy_cover

-- Hall matches the same pieces. The 4N count remains a separate proof obligation.
#print axioms Kakeya.Ninety21.exists_hall_reindexing
#print axioms Kakeya.Ninety21.hall_reindexed_card
#print axioms Kakeya.Ninety21.data_of_trimmed_hall
#print axioms Kakeya.Ninety21.hallPiece_at_equiv
#print axioms Kakeya.Ninety21.hallEquiv42_intersects
#print axioms Kakeya.Ninety21.hallPiece_mass_sum
#print axioms Kakeya.Ninety21.greedy_of_trimmed_hall
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_trimmed_hall
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_trimmed_hall

-- Original-tube degree splits the ACTUAL retained pieces by the paper's N/2 threshold.
-- Exceptional pieces are excluded from the lower-fiber assumption.
#print axioms Kakeya.Ninety21.paperOriginalTubeDegree
#print axioms Kakeya.Ninety21.paperRegularPieces
#print axioms Kakeya.Ninety21.paperExceptionalPieces
#print axioms Kakeya.Ninety21.mem_paperRegularPieces
#print axioms Kakeya.Ninety21.mem_paperExceptionalPieces
#print axioms Kakeya.Ninety21.paper_regular_exceptional_partition
#print axioms Kakeya.Ninety21.paper_regular_exceptional_card
#print axioms Kakeya.Ninety21.paperExceptional_parent_selected
#print axioms Kakeya.Ninety21.paperExceptional_trimmed
#print axioms Kakeya.Ninety21.paperRegularIndex
#print axioms Kakeya.Ninety21.paperRegularIndex_injective
#print axioms Kakeya.Ninety21.paperRegularIndices
#print axioms Kakeya.Ninety21.paperRegularIndices_subset_hall
#print axioms Kakeya.Ninety21.paperRegularIndexEquiv
#print axioms Kakeya.Ninety21.paperRegularIndices_card
#print axioms Kakeya.Ninety21.paperOriginalTubeMapReg
#print axioms Kakeya.Ninety21.paper_double_count_fibers
#print axioms Kakeya.Ninety21.paper_regular_count_of_fibers
#print axioms Kakeya.Ninety21.paper_hall_count_with_exceptional_remainder

-- Theorem 4.6 nonintersecting matching and extended equivalence.
#print axioms Kakeya.Ninety21.exists_paper46_hall_equiv
#print axioms Kakeya.Ninety21.hallEquiv
#print axioms Kakeya.Ninety21.hallEquiv_selected_fixed
#print axioms Kakeya.Ninety21.hallEquiv_regular_nonintersecting
#print axioms Kakeya.Ninety21.hallEquiv_exceptional_auxiliary

#print axioms Kakeya.Ninety21.paper46RegularIndex_injective
#print axioms Kakeya.Ninety21.paper46_regular_count_of_fibers

-- Theorem 4.6 relabeling and analytic estimates.
#print axioms Kakeya.Ninety21.paper46SelectedRetainedEquiv
#print axioms Kakeya.Ninety21.paper46RemainingRetainedEquiv
#print axioms Kakeya.Ninety21.paper46AnalyticEquiv
#print axioms Kakeya.Ninety21.paper46AnalyticPiece_at_equiv
#print axioms Kakeya.Ninety21.paper46_analytic_mass_sum
#print axioms Kakeya.Ninety21.paper46_analytic_card
#print axioms Kakeya.Ninety21.paper46_analytic_piece_volume
#print axioms Kakeya.Ninety21.paper46_analytic_capture
#print axioms Kakeya.Ninety21.paper46_analytic_count_with_exceptional
#print axioms Kakeya.Ninety21.Paper46LargeLevelInputs
#print axioms Kakeya.Ninety21.paper46ExceptionalOverhead
#print axioms Kakeya.Ninety21.paper46_large_level_retained_count
#print axioms Kakeya.Ninety21.paper46_retained_capture
#print axioms Kakeya.Ninety21.paper46_analytic_level_budget
#print axioms Kakeya.Ninety21.paper46_analytic_uniform_level_budget
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_paper46
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_paper46

#print axioms Kakeya.Ninety21.paper46_small_level_budget
#print axioms Kakeya.Ninety21.paper46EndpointBudget

#print axioms Kakeya.Ninety21.paper_regular_budget_of_tube_ball_count
#print axioms Kakeya.Ninety21.paper_exceptional_scaled_budget

#print axioms Kakeya.Ninety21.paper46Construction_of_tube_ball_count
#print axioms Kakeya.Ninety21.paper46Construction_of_dyadic_tube_ball_count
#print axioms Kakeya.Ninety21.paper46LargeLevelInputs_of_tube_ball_count

#print axioms Kakeya.Ninety21.tube_ball_scale_of_sq_le
#print axioms Kakeya.Ninety21.paper_regular_budget_of_sq_le

#print axioms Kakeya.Ninety21.TubeBallPairIndexing.pair_injective
#print axioms Kakeya.Ninety21.paper_regular_budget_of_pair_indexing
#print axioms Kakeya.Ninety21.paper46Construction_of_pair_indexing
#print axioms Kakeya.Ninety21.paper46LargeLevelInputs_of_pair_indexing

#print axioms Kakeya.Ninety21.paper46Cutoff
#print axioms Kakeya.Ninety21.paper46Construction_of_pair_indexing_at_cutoff



-- Concrete tube-ball geometry and greedy transport.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_subset_tube
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_subset_gain
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_subset_level
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_subset_ball
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.gain_disjoint
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_measurable
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.toBallLocalized
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.pairIndexing
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.paper46Construction
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedyQ_measurable
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedyQ_subset_level
#print axioms Kakeya.Ninety21.ConcreteTubeBallGreedy.toRetainedGreedy

-- Geometry, Vitali selection and greedy numerical reductions.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedy_card_budget
#print axioms Kakeya.Ninety21.canonical_retained_radius_scale
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_volume_le_orthogonal_product
#print axioms Kakeya.Ninety21.exists_concrete_vitali_localized_cover
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedy_recurrence_of_average

#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_volume_le_explicit
#print axioms Kakeya.Ninety21.concrete_greedyUnion_succ
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedyQ_subset_residual
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedy_residual_conservation
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.cover_of_vitali_labels
#print axioms Kakeya.Ninety21.ConcreteTubeBallGreedy.ofAverage

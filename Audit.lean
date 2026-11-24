module
import Kakeya
import Kakeya.Ninety21ConcreteTubeBallBridge
import Kakeya.Ninety21ConcreteGeometryReductions
import Kakeya.Ninety21RetainedCoverage
import Kakeya.Ninety21VitaliIndexBudget
import Kakeya.Ninety21TwoRadiusEndpoint
import Kakeya.Ninety21OccupiedVitaliPieces
import Kakeya.Ninety21GreedyVitaliBounds
import Kakeya.Ninety110OrderedTails
import Kakeya.Ninety109Endpoint

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
-- Two-radius Vitali coverage and volume estimates.
#print axioms Kakeya.Ninety21.finite_double_union_measure_le
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.measure_le_tripleBall_sum
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.exists_twoRadius_vitali_mass_bound
#print axioms Kakeya.Ninety21.unitTube_tripleBall_volume_le
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.volume_le_tripleBall_cost
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.exists_twoRadius_vitali_volume_bound
-- Retained tube-ball labels and cover-index budgets.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.coverIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.selectedBall_mem_coverIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.pairBall_mem_coverIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.coverIndices_card_budget_nat
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.coverIndices_card_budget
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitaliPairs
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitaliPairs_parent
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitaliPairs_ball
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitaliPairs_contains
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withVitaliPairs
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitali_mem_coverIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitali_cover_withPairs
-- Two-radius analytic endpoint.
#print axioms Kakeya.Ninety21.twoRadius_mass_le_double_sum
#print axioms Kakeya.Ninety21.twoRadius_mass_capture_from_step
#print axioms Kakeya.Ninety21.twoRadiusRadius
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.mass_capture
#print axioms Kakeya.Ninety21.paper46_twoRadius_analytic_level_budget
#print axioms Kakeya.Ninety21.paper46_twoRadius_large_uniform_level_budget
#print axioms Kakeya.Ninety21.paper46_twoRadius_analytic_uniform_level_budget
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_paper46_twoRadius
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_paper46_twoRadius
-- Occupied Vitali pieces, disjointness, and cover transfer.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitaliIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitali_nonempty
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedCandidates_cover
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.vitali_subset_occupied
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitaliLabels
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitaliLabel_nonempty
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitaliLabel_disjoint
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.activeVitaliTubes
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.activeVitaliTubes_card_le
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.firstOccupiedVitaliBall
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.firstOccupiedVitaliBall_mem
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitaliBase
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitaliPieces
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitaliPieces_greedyQ
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitali_gain_eq
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.gain_subset_parentTube
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.gain_subset_dyadicLevel
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_nonempty_of_gain_ball
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.piece_eq_gain_ball_of_univ_trim
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitaliPieces_piece_eq
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitaliPieces_nonempty
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitali_pairBall_ne_selected
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitali_label_injective
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitali_label_mem
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.withOccupiedVitaliPieces_disjoint
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitali_mem_coverIndices
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitali_cover_transfer
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.occupiedVitali_index_budget
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofOccupiedVitali
-- Greedy Vitali selection and occupied-indexed radius-R balls.
#print axioms Kakeya.Ninety21.exists_finite_occupied_radius_cover
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.exists_greedy_vitali_from_compact_gains
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.exists_greedy_occupied_vitali
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exists_selected
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_occupied
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_disjoint
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_triple_cover
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_triple_cover
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_piece_nonempty
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_ball_eq
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_incidence_eq
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_incidence_card_le_all
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_index_budget
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofGreedyVitaliCandidates
-- Finite greedy-gain nets, indexed Vitali centers, and selected stages.
#print axioms Kakeya.Ninety21.VitaliFiniteCenterPair
#print axioms Kakeya.Ninety21.vitaliFiniteCenterEquiv
#print axioms Kakeya.Ninety21.vitaliFiniteParent
#print axioms Kakeya.Ninety21.vitaliFiniteCenter
#print axioms Kakeya.Ninety21.vitaliFiniteCandidates
#print axioms Kakeya.Ninety21.vitaliFinite_index_exists
#print axioms Kakeya.Ninety21.vitaliFinite_indexed_cover
#print axioms Kakeya.Ninety21.vitaliFinite_center_mem
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.gain_compact_closure_of_bounded_level
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.stages_of_selected_range
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.exists_greedy_vitali_of_bounded_level
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.finiteGainNet
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.finiteGainNet_mem
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.finiteGainNet_cover
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.finiteGainNet_indexed_cover
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.euclidean_gain_compact_closure
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofIndexedGainNets
-- Existing-geometry finite-net compatibility.
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofExistingGainNetIndexMap
-- Original finite-net ball indexing and occupied Vitali input.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamily
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamily_ball
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamily_ball_occupied
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofGreedyNetFamily
#print axioms Kakeya.Ninety21.greedyFiniteNet
#print axioms Kakeya.Ninety21.greedyFiniteNet_mem
#print axioms Kakeya.Ninety21.greedyFiniteNet_cover
#print axioms Kakeya.Ninety21.greedyFiniteNet_nonempty
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
-- Greedy-average recurrence and triple-radius cost for the occupied family.
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_greedy_recurrence_of_average
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_triple_volume_le
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofGreedyVitaliAverage
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_greedyVitaliAverage
-- Canonical greedy selection and Euclidean triple-radius endpoint.
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_canonical_greedy_recurrence
#print axioms Kakeya.Ninety21.tripleRadiusTransverseCoefficient
#print axioms Kakeya.Ninety21.conditional_mass_eq_measure_toReal
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.euclidean_triple_cost
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofCanonicalVitaliEuclidean
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_canonicalVitaliEuclidean
-- Maximal residual selection without replacement.
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.MaximalUnused
#print axioms Kakeya.Ninety21.exists_maximal_unused_tube
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.greedy_average_of_maximal_unused
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_greedy_recurrence_of_maximal_unused
#print axioms Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofMaximalUnusedVitaliEuclidean
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_maximalUnusedVitaliEuclidean
-- Original greedy selection without replacement and its Vitali data.
#print axioms Kakeya.Ninety21.maximalUnusedChoice
#print axioms Kakeya.Ninety21.maximalUnusedChoice_spec
#print axioms Kakeya.Ninety21.maximalUnusedUsed
#print axioms Kakeya.Ninety21.maximalUnusedChosen
#print axioms Kakeya.Ninety21.maximalUnusedUsed_eq_image
#print axioms Kakeya.Ninety21.maximalUnused_available
#print axioms Kakeya.Ninety21.maximalUnusedChosen_not_mem
#print axioms Kakeya.Ninety21.maximalUnusedChosen_injective_initial
#print axioms Kakeya.Ninety21.maximalUnusedUsed_union_eq_prefix
#print axioms Kakeya.Ninety21.maximalUnusedChosen_maximal
#print axioms Kakeya.Ninety21.maximalUnused_dyadic_step_le_card
#print axioms Kakeya.Ninety21.maximalUnusedDyadicChosen
#print axioms Kakeya.Ninety21.maximalUnusedDyadicSelected
#print axioms Kakeya.Ninety21.maximalUnusedDyadicStage
#print axioms Kakeya.Ninety21.maximalUnusedDyadicStage_chosen
#print axioms Kakeya.Ninety21.maximalUnusedDyadic_hChosen
#print axioms Kakeya.Ninety21.maximalUnusedDyadic_hStages
#print axioms Kakeya.Ninety21.maximalUnusedDyadicSelected_card
#print axioms Kakeya.Ninety21.maximalUnusedDyadic_hMax
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamily_maximalUnused
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamily_hStages
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains_selection
-- Empty-gain localization.
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_empty_of_gain_empty
#print axioms Kakeya.Ninety21.greedyFiniteNet_empty_of_gain_empty
#print axioms Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.ofGreedyNetFamilyAllowEmpty
-- Greedy–Vitali concrete bounds.
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_ball_occupied_of_centers
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_selected_card_le
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_selected_card_maximal_unused
#print axioms Kakeya.Ninety21.ofGreedyNetFamily_center_on_level
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_piece_euclidean_cost
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds_radius
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_label_ball_occupied
#print axioms Kakeya.Ninety21.canonicalGreedyVitaliRadius
#print axioms Kakeya.Ninety21.canonicalGreedyVitaliRadius_pos
#print axioms Kakeya.Ninety21.canonicalGreedyVitaliRadius_scale
-- Exceptional parent-ball indexing and pair-label counting.
#print axioms Kakeya.Ninety21.paperExceptionalParentBallIndices
#print axioms Kakeya.Ninety21.paper_exceptional_card_le_parent_ball_count
#print axioms Kakeya.Ninety21.paper_exceptional_scaled_budget_of_parent_ball_count
#print axioms Kakeya.Ninety21.paper_exceptional_scaled_budget_of_pair_indexing
-- Two-tube transversality and disjoint-ball packing.
#print axioms Kakeya.Ninety21.originalTube_ball_center_near_axis
#print axioms Kakeya.Ninety21.TransverseDirections
#print axioms Kakeya.Ninety21.two_transverse_tubes_ball_center_diameter
#print axioms Kakeya.Ninety21.disjoint_balls_card_le_half_radius_net
#print axioms Kakeya.Ninety21.two_transverse_tubes_ball_count_of_cover
-- Exceptional original-tube incidence and parent-wise bounds.
#print axioms Kakeya.Ninety21.transverse_finite_incidence_count
#print axioms Kakeya.Ninety21.exceptional_parent_ball_large_original_incidence
#print axioms Kakeya.Ninety21.exceptional_parent_ball_packing_of_transverse_count
#print axioms Kakeya.Ninety21.exceptional_scaled_budget_of_transverse_count
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_parent_balls_selected
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_parent_balls_disjoint
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_transverse_pair_card_le
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_transverse_geometry
-- Uniform Euclidean covering and exceptional-budget specialization.
#print axioms Kakeya.Ninety21.euclidean_uniform_half_radius_net
#print axioms Kakeya.Ninety21.euclidean_transverse_uniform_half_radius_net
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_uniform_cover
-- Separated-direction nets and angular-cap incidence counting.
#print axioms Kakeya.Ninety21.separated_finset_card_le_net_card
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices
#print axioms Kakeya.Ninety21.transverse_of_not_mem_nonTransverseDirectionIndices
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices_card_budget_of_net
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_angular_cap_net
#print axioms Kakeya.Ninety21.separated_two_chart_card_le
#print axioms Kakeya.Ninety21.uniform_projected_cap_net
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices_card_of_projected_charts
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices_budget_of_projected_charts
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_projected_chart
-- Angular-cap population normalization.
#print axioms Kakeya.Ninety21.angular_population_real_bound
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices_budget_of_quantitative_packing
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_cap_packing
-- Unit-cap coordinate geometry and reverse Lipschitz control.
#print axioms Kakeya.Ninety21.unit_cap_axial_difference_le
#print axioms Kakeya.Ninety21.unit_two_cap_reverse_lipschitz
#print axioms Kakeya.Ninety21.nonTransverseDirectionIndices_card_of_unit_chart_geometry
-- Unit-direction Gram identities and nontransverse projected norms.
#print axioms Kakeya.Ninety21.unit_directions_gram_identity
#print axioms Kakeya.Ninety21.transverse_of_unit_sine_sq_lower
#print axioms Kakeya.Ninety21.unit_sine_sq_lt_of_not_transverse
#print axioms Kakeya.Ninety21.projected_norm_lt_of_not_transverse
#print axioms Kakeya.Ninety21.original_nontransverse_projected_norm_le
-- Quantitative Euclidean cap packing.
#print axioms Kakeya.Ninety21.finite_euclidean_packing_of_ball_volume
#print axioms Kakeya.Ninety21.finite_euclidean_projected_packing
#print axioms Kakeya.Ninety21.separated_two_chart_real_card_le
#print axioms Kakeya.Ninety21.quantitative_cap_card_of_projected_chart
-- Orthogonal coordinate charts for unit directions.
#print axioms Kakeya.Ninety21.directionOrthogonalBasis
#print axioms Kakeya.Ninety21.unitDirectionPerpendicular
#print axioms Kakeya.Ninety21.unitDirectionOrthogonalChart
#print axioms Kakeya.Ninety21.unitDirectionOrthogonalChart_norm
#print axioms Kakeya.Ninety21.unitDirectionOrthogonalChart_pythagoras
-- Concrete angular packing and exceptional-piece budget.
#print axioms Kakeya.Ninety21.unitDirectionHemisphere
#print axioms Kakeya.Ninety21.unitDirectionHemisphere_same_sign
#print axioms Kakeya.Ninety21.unitDirectionOrthogonalChart_coordinate_distance
#print axioms Kakeya.Ninety21.original_unit_directions_quantitative_cap_card
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_unit_directions
-- Per-level Theorem 4.6 counting and endpoint.
#print axioms Kakeya.Ninety21.paper46_remaining_count_of_exceptional_budget
#print axioms Kakeya.Ninety21.paper46_retained_count_of_exceptional_budget
#print axioms Kakeya.Ninety21.paper46_large_level_retained_count_per_level
#print axioms Kakeya.Ninety21.paper46_analytic_level_budget_per_level
#print axioms Kakeya.Ninety21.paper46_analytic_uniform_level_budget_per_level
#print axioms Kakeya.Ninety21.full_conditional_kakeya_moment_of_paper46_per_level
#print axioms Kakeya.Ninety21.full_conditional_kakeya_of_paper46_per_level
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_parents_subset
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions
#print axioms Kakeya.Ninety21.angular_packing_parameters_of_card_bound
#print axioms Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions_card_bound
-- Lemmas 4.8 and 4.9.
#print axioms Kakeya.Ninety109.multiple_hits_angle
#print axioms Kakeya.Ninety109.multiple_hits_card
#print axioms Kakeya.Ninety109.multiple_hits_card_dyadic
#print axioms Kakeya.Ninety109.fixed_tube_vitali_ball_tail
#print axioms Kakeya.Ninety109.triple_vitali_ball_overlap_bound
#print axioms Kakeya.Ninety109.fixed_tube_vitali_ball_tail_with_bounded_overlap
#print axioms Kakeya.Ninety109.triple_hit_of_coverPiece_incidence
#print axioms Kakeya.Ninety109.fixed_tube_vitali_piece_tail
#print axioms Kakeya.Ninety109.TubeFamily.regular_tail_card_along_parent
#check Kakeya.Ninety109.TubeFamily.regular_parent_forward_hit
#print axioms Kakeya.Ninety109.TubeFamily.regular_parent_forward_hit
#check Kakeya.Ninety109.TubeFamily.regular_hforward_along_parent
#print axioms Kakeya.Ninety109.TubeFamily.regular_hforward_along_parent
#check Kakeya.Ninety109.TubeFamily.regular_parent_incidence_tail
#print axioms Kakeya.Ninety109.TubeFamily.regular_parent_incidence_tail
#print axioms Kakeya.Ninety109.orderedTail_subset_geometricHits
#print axioms Kakeya.Ninety109.orderedTail_card_le_geometricHits
#print axioms Kakeya.Ninety109.orderedTail_eq_inter_selection2
#print axioms Kakeya.Ninety109.orderedTail_subset_laterIncidences
#print axioms Kakeya.Ninety109.orderedTail_card_le_selection2
#print axioms Kakeya.Ninety109.OrderedTailChainApplication
#print axioms Kakeya.Ninety109.orderedTailApplication_of_tail_chain
#print axioms Kakeya.Ninety109.orderedTailApplication_of_selection2
#print axioms Kakeya.Ninety109.orderedTailApplication_of_geometric_bound
#print axioms Kakeya.Ninety109.ordered_tail_card_of_fixed_tube_vitali_ball_tail
#check Kakeya.Ninety109.ordered_tail_card_of_forward_ball_hits
#print axioms Kakeya.Ninety109.ordered_tail_card_of_forward_ball_hits
#check Kakeya.Ninety109.TubeFamily.regular_label_pair_injective
#print axioms Kakeya.Ninety109.TubeFamily.regular_label_pair_injective
#print axioms Kakeya.Ninety109.ordered_overlap_eq_sum_tails
#print axioms Kakeya.Ninety109.ordered_overlap_of_tails
#print axioms Kakeya.Ninety109.fixed_parent_overlap
#print axioms Kakeya.Ninety109.fixed_parent_overlap_dyadic
#print axioms Kakeya.Ninety109.OrderedOverlapBound
#print axioms Kakeya.Ninety109.incidence_sum_of_ordered_overlap
#print axioms Kakeya.Ninety109.regular_label_count_of_ordered_overlap
#print axioms Kakeya.Ninety109.exceptional_cover_count
-- Lemma 4.8 fixed-parent tail and inclusion using globally indexed balls.
#check Kakeya.Ninety109.TubeFamily.fixedParentTubeTail
#print axioms Kakeya.Ninety109.TubeFamily.fixedParentTubeTail
#check Kakeya.Ninety109.TubeFamily.fixed_parent_tube_tail_card
#print axioms Kakeya.Ninety109.TubeFamily.fixed_parent_tube_tail_card
#check Kakeya.Ninety109.TubeFamily.regular_tail_card_of_parent_subset_inclusion
#print axioms Kakeya.Ninety109.TubeFamily.regular_tail_card_of_parent_subset_inclusion
#print axioms Kakeya.Ninety109.TubeFamily.retainedPiece_subset_global_vitali_ball
#check Kakeya.Ninety109.TubeFamily.R_c_orderedTail_subset_of_global_vitali_balls
#print axioms Kakeya.Ninety109.TubeFamily.R_c_orderedTail_subset_of_global_vitali_balls
#check Kakeya.Ninety109.TubeFamily.ParentSubsetApplication
#print axioms Kakeya.Ninety109.TubeFamily.ParentSubsetApplication
#check Kakeya.Ninety109.TubeFamily.parentTailApplication_of_parent_subset
#print axioms Kakeya.Ninety109.TubeFamily.parentTailApplication_of_parent_subset
#check Kakeya.Ninety109.TubeFamily.parentTailApplication_of_ball_map
#print axioms Kakeya.Ninety109.TubeFamily.parentTailApplication_of_ball_map
-- Retained pieces and the conditional logarithmic endpoint.
#print axioms Kakeya.Ninety109.greedyUnion_subset_coverPieces
#print axioms Kakeya.Ninety109.TubeFamily.piece_volume
#print axioms Kakeya.Ninety109.regularTailChain
#print axioms Kakeya.Ninety109.regularApplication_of_tail_chain
#print axioms Kakeya.Ninety109.regularSelection2
#print axioms Kakeya.Ninety109.regularApplication_of_selection2
#print axioms Kakeya.Ninety109.TubeFamily.TailChainApplication
#print axioms Kakeya.Ninety109.TubeFamily.overlapApplication_of_tail_chain
#print axioms Kakeya.Ninety109.TubeFamily.Selection2Application
#print axioms Kakeya.Ninety109.TubeFamily.overlapApplication_of_selection2
#print axioms Kakeya.Ninety109.TubeFamily.OverlapApplication
#print axioms Kakeya.Ninety109.TubeFamily.level_bound
#print axioms Kakeya.Ninety109.TubeFamily.moment_bound
#print axioms Kakeya.Ninety109.TubeFamily.norm_bound
#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound
#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_selection2
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_selection2

-- Selected Vitali ball indices and the two-hypothesis endpoint.
#check Kakeya.Ninety109.selectedVitaliBallIndices
#print axioms Kakeya.Ninety109.retained_ball_image_eq_selected
#print axioms Kakeya.Ninety109.TubeFamily.globalVitaliBalls_eq_selected
#check Kakeya.Ninety109.TubeFamily.SelectedVitaliDisjoint
#print axioms Kakeya.Ninety109.TubeFamily.globalVitaliDisjoint_of_selected
#print axioms Kakeya.Ninety109.TubeFamily.fixed_parent_tube_tail_card_of_selected_disjoint
#print axioms Kakeya.Ninety109.TubeFamily.selected_ball_tail_le_incidence_card
#check Kakeya.Ninety109.TubeFamily.angularTail
#check Kakeya.Ninety109.TubeFamily.RegularTailSubsetSelectedBalls
#print axioms Kakeya.Ninety109.TubeFamily.overlapApplication_of_selected_ball_subset
#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_selected_ball_subset
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_selected_ball_subset

import Jung.Main

/-!
Independent statement and transitive foundational-dependency audit.
This driver prints information about the compiled project and adds no theorem.
-/

set_option pp.universes true

#print Jung5.Point
#print Jung5.l1Dist
#print Jung5.UnitFiniteEnclosing
#print Jung5.Cut
#print Jung5.minShore
#print Jung5.separates
#print Jung5.balancedSupport
#print Jung5.sharpPoint

#check Jung5.jung_l1_five
#check Jung5.jung_l1_five_explicit
#print Jung5.jung_l1_five_explicit
#check Jung5.jung_l1_five_sharp
#check Jung5.unit_finite_enclosing
#check Jung5.finite_contact_reduction
#check Jung5.contact_six_active_family
#check Jung5.contact_active_convex_balance
#check Jung5.exists_contact_minimizer
#check Jung5.six_contact_obstruction
#check Jung5.six_point_median_bound
#check Jung5.Gap.weight_distance
#check Jung5.Gap.weight_objective
#check Jung5.Gap.balancedSupport_card
#check Jung5.cut_weight_bound
#check Jung5.CutCertificate.finite_certificate
#check Jung5.CutCertificate.balancedCut_coverage
#check Jung5.finite_enclosing_scaled
#check Jung5.enclosing_all_sets_of_unit_finite
#check Jung5.sharpness_witness
#check Jung5.sharpPoint_radius_lower

#print axioms Jung5.l1Dist_nonneg
#print axioms Jung5.l1Dist_self
#print axioms Jung5.l1Dist_symm
#print axioms Jung5.l1Dist_triangle
#print axioms Jung5.abs_coordinate_sub_le
#print axioms Jung5.l1Dist_scale

#print axioms Jung5.signDot_sub
#print axioms Jung5.signDot_add
#print axioms Jung5.signDot_le_l1Dist
#print axioms Jung5.weighted_signDot_zero
#print axioms Jung5.contact_weight_bound
#print axioms Jung5.sum_contacts_lower_bound
#print axioms Jung5.six_uniform_balance
#print axioms Jung5.six_contact_obstruction

#print axioms Jung5.contactSignVector_isSign
#print axioms Jung5.contact_norming_identity
#print axioms Jung5.contact_distance_le_radius
#print axioms Jung5.contact_radius_nonneg
#print axioms Jung5.continuous_contact_distance
#print axioms Jung5.continuous_contact_radius
#print axioms Jung5.exists_contact_minimizer
#print axioms Jung5.signDot_smul
#print axioms Jung5.contact_form_motion
#print axioms Jung5.contact_common_step
#print axioms Jung5.contact_strict_descent
#print axioms Jung5.contactActiveVector_spec
#print axioms Jung5.contactActiveVector_mem
#print axioms Jung5.contact_dual_vector
#print axioms Jung5.contact_active_convex_balance
#print axioms Jung5.contact_sum_embedding
#print axioms Jung5.contact_six_active_family
#print axioms Jung5.finite_contact_reduction

#print axioms Jung5.Gap.stepGap_nonneg
#print axioms Jung5.Gap.ordered_pair
#print axioms Jung5.Gap.ordered_median
#print axioms Jung5.Gap.mem_rawPrefix
#print axioms Jung5.Gap.card_rawPrefix
#print axioms Jung5.Gap.canonical_separates
#print axioms Jung5.Gap.canonicalPrefix_separates
#print axioms Jung5.Gap.canonicalPrefix_minShore
#print axioms Jung5.Gap.canonicalPrefix_balanced
#print axioms Jung5.Gap.orderedCoord_monotone
#print axioms Jung5.Gap.coordGap_nonneg
#print axioms Jung5.Gap.coord_pair
#print axioms Jung5.Gap.coord_median
#print axioms Jung5.Gap.weight_nonneg
#print axioms Jung5.Gap.weight_eval
#print axioms Jung5.Gap.weight_distance
#print axioms Jung5.Gap.weight_objective
#print axioms Jung5.Gap.balancedSupport_subset
#print axioms Jung5.Gap.balancedSupport_card
#print axioms Jung5.six_point_median_bound

#print axioms Jung5.CutCertificate.balancedCut_card
#print axioms Jung5.CutCertificate.balancedCut_injective
#print axioms Jung5.CutCertificate.balancedCut_coverage
#print axioms Jung5.CutCertificate.finite_certificate
#print axioms Jung5.cut_weight_bound

#print axioms Jung5.finite_enclosing_scaled
#print axioms Jung5.continuous_l1Dist_center
#print axioms Jung5.isClosed_l1_center_constraint
#print axioms Jung5.isCompact_l1_center_constraint
#print axioms Jung5.enclosing_all_sets_of_unit_finite

#print axioms Jung5.sharpPoint_pair
#print axioms Jung5.sharpPoint_diameter_bound
#print axioms Jung5.sharpPoint_zero_radius
#print axioms Jung5.opposite_quarters
#print axioms Jung5.sharpPoint_sum_lower
#print axioms Jung5.sharpPoint_radius_lower
#print axioms Jung5.sharpness_witness

#print axioms Jung5.unit_finite_enclosing
#print axioms Jung5.jung_l1_five
#print axioms Jung5.jung_l1_five_explicit
#print axioms Jung5.jung_l1_five_sharp

#print Jung.Point
#print Jung.l1Dist
#print Jung.coefficient
#check Jung.jung_l1_four_k_plus_one
#check Jung.jung_l1_four_k_plus_one_all
#check Jung.jung_l1_four_k_plus_one_explicit
#check Jung.Cut.weight_bound
#check Jung.median_bound
#print axioms Jung.abs_coordinate_sub_le
#print axioms Jung.coefficient_nonneg
#print axioms Jung.contact_active_convex_balance
#print axioms Jung.contact_active_family
#print axioms Jung.contact_common_step
#print axioms Jung.contact_distance_le_radius
#print axioms Jung.contact_dual_vector
#print axioms Jung.contact_form_motion
#print axioms Jung.contact_norming_identity
#print axioms Jung.contact_radius_nonneg
#print axioms Jung.contact_strict_descent
#print axioms Jung.contact_sum_embedding
#print axioms Jung.contact_weight_bound
#print axioms Jung.contactActiveVector_mem
#print axioms Jung.contactActiveVector_spec
#print axioms Jung.contacts_uniform
#print axioms Jung.contactSignVector_isSign
#print axioms Jung.continuous_contact_distance
#print axioms Jung.continuous_contact_radius
#print axioms Jung.continuous_l1Dist_center
#print axioms Jung.cut_bound_of_moments
#print axioms Jung.cut_bound_strict
#print axioms Jung.Cut.balanced_sum
#print axioms Jung.Cut.basic_moments
#print axioms Jung.Cut.delta_ite
#print axioms Jung.Cut.double_delta
#print axioms Jung.Cut.double_product
#print axioms Jung.Cut.double_quadratic
#print axioms Jung.Cut.indicator_sum
#print axioms Jung.Cut.intersection_dot
#print axioms Jung.Cut.odd_square
#print axioms Jung.Cut.quadratic_formula
#print axioms Jung.Cut.quadratic_lower
#print axioms Jung.Cut.quadratic_upper
#print axioms Jung.Cut.size_facts
#print axioms Jung.Cut.sum_switch
#print axioms Jung.Cut.total_formula
#print axioms Jung.Cut.vector_sign
#print axioms Jung.Cut.vector_sum
#print axioms Jung.Cut.weight_bound
#print axioms Jung.enclosing_all_sets_of_unit_finite
#print axioms Jung.exists_contact_minimizer
#print axioms Jung.finite_enclosing_scaled
#print axioms Jung.Gap.balanced_card
#print axioms Jung.Gap.card_shore
#print axioms Jung.Gap.cut_card
#print axioms Jung.Gap.cut_delta
#print axioms Jung.Gap.cut_mem
#print axioms Jung.Gap.cut_size
#print axioms Jung.Gap.gap_prefix
#print axioms Jung.Gap.ordered_median
#print axioms Jung.Gap.ordered_monotone
#print axioms Jung.Gap.ordered_pair
#print axioms Jung.Gap.separation_count
#print axioms Jung.Gap.step_nonneg
#print axioms Jung.Gap.weight_distance
#print axioms Jung.Gap.weight_nonneg
#print axioms Jung.Gap.weight_objective
#print axioms Jung.half_weight_card
#print axioms Jung.isClosed_l1_center_constraint
#print axioms Jung.isCompact_l1_center_constraint
#print axioms Jung.jung_l1_four_k_plus_one
#print axioms Jung.jung_l1_four_k_plus_one_all
#print axioms Jung.jung_l1_four_k_plus_one_explicit
#print axioms Jung.l1Dist_nonneg
#print axioms Jung.l1Dist_scale
#print axioms Jung.l1Dist_self
#print axioms Jung.l1Dist_symm
#print axioms Jung.l1Dist_triangle
#print axioms Jung.median_bound
#print axioms Jung.signDot_add
#print axioms Jung.signDot_le_l1Dist
#print axioms Jung.signDot_smul
#print axioms Jung.signDot_sub
#print axioms Jung.sum_contacts_lower_bound
#print axioms Jung.uniform_sign_balance
#print axioms Jung.unit_finite_enclosing
#print axioms Jung.weighted_signDot_zero

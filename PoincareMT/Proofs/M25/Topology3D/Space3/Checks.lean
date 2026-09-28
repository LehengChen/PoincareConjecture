import PoincareMT.Proofs.M25.Topology3D.Space3.ChartUnion
import PoincareMT.Proofs.M25.Topology3D.Space3.CompactChart
import PoincareMT.Proofs.M25.Topology3D.Space3.FlowInvariants
import PoincareMT.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareMT.Proofs.M25.Topology3D.Space3.SardRegularValues
import PoincareMT.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import PoincareMT.Proofs.M25.Topology3D.Space3.UniformTube
import PoincareMT.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularLevelFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.HeightField
import PoincareMT.Proofs.M25.Topology3D.Space3.ManifoldOpenChart
import PoincareMT.Proofs.M25.Topology3D.Space3.CollarParameter
import PoincareMT.Proofs.M25.Topology3D.Space3.ClockTracks
import PoincareMT.Proofs.M25.Topology3D.Space3.CollarChart
import PoincareMT.Proofs.M25.Topology3D.Space3.FlowTube
import PoincareMT.Proofs.M25.Topology3D.Space3.FlatCap
import PoincareMT.Proofs.M25.Topology3D.Space3.FlatCapProfile
import PoincareMT.Proofs.M25.Topology3D.Space3.FlatCapModel
import PoincareMT.Proofs.M25.Topology3D.Space3.HeightCoordinates
import PoincareMT.Proofs.M25.Topology3D.Space3.LocalFieldIsotopy
import PoincareMT.Proofs.M25.Topology3D.Space3.BallExterior
import PoincareMT.Proofs.M25.Topology3D.Space3.StandardTube
import PoincareMT.Proofs.M25.Topology3D.Space3.FlatCapBall
import PoincareMT.Proofs.M25.Topology3D.Space3.CollarCoordinates
import PoincareMT.Proofs.M25.Topology3D.Space3.BallShrinking
import PoincareMT.Proofs.M25.Topology3D.Space3.ChartedCapShrinking
import PoincareMT.Proofs.M25.Topology3D.Space3.ChartedBallInvariance
import PoincareMT.Proofs.M25.Topology3D.Space3.SmallCap
import PoincareMT.Proofs.M25.Topology3D.Space3.SharedBoundaryTangency
import PoincareMT.Proofs.M25.Topology3D.Space3.SharedBoundaryFlow
import PoincareMT.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareMT.Proofs.M25.Topology3D.Space3.GermIsotopy
import PoincareMT.Proofs.M25.Topology3D.Space3.BoundaryChartLinearization
import PoincareMT.Proofs.M25.Topology3D.Space3.PlanarBoundaryCap
import PoincareMT.Proofs.M25.Topology3D.Space3.PlanarRelativeCompression
import PoincareMT.Proofs.M25.Topology3D.Space3.RelativeBallCompression
import PoincareMT.Proofs.M25.Topology3D.Space3.CollarOrientation
import PoincareMT.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension
import PoincareMT.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import PoincareMT.Proofs.M25.Topology3D.Space3.SchoenfliesFromBall
import PoincareMT.Proofs.M25.Topology3D.Space3.GenericHeight
import PoincareMT.Proofs.M25.Topology3D.Space3.SurfaceMorse
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularLevelPeriod
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularInnermostDisc
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularBandTransport
import PoincareMT.Proofs.M25.Topology3D.Space3.SourceCirclePullback
import PoincareMT.Proofs.M25.Topology3D.Space3.SourceCircleDisc
import PoincareMT.Proofs.M25.Topology3D.Space3.SphereDiscCoordinates
import PoincareMT.Proofs.M25.Topology3D.Space3.SphereDiffeomorphRestriction
import PoincareMT.Proofs.M25.Topology3D.Space3.HorizontalBandField
import PoincareMT.Proofs.M25.Topology3D.Space3.SourceDiscBoundary
import PoincareMT.Proofs.M25.Topology3D.Space3.RegularInnermostTube

/-!
# Declaration audit for the Alexander construction

This module checks every current independently compiled construction.
It does not assert that the Alexander theorem has been proved.
-/

set_option autoImplicit false

-- This audit module intentionally prints the dependencies of every checked declaration.
set_option linter.hashCommand false

#print axioms PoincareMT.M25.Topology3D.sphereRadialExtension
#print axioms PoincareMT.M25.Topology3D.sphereRadialExtension_smul
#print axioms PoincareMT.M25.Topology3D.sphereRadialExtension_contDiffOn
#print axioms PoincareMT.M25.Topology3D.sphere_mfderiv_injective_of_radialExtension
#print axioms PoincareMT.M25.Topology3D.exists_opposite_sphere_regularValues
#print axioms PoincareMT.M25.Topology3D.exists_sphere_collar_unit_normal
#print axioms PoincareMT.M25.Topology3D.exists_sphere_collar_regular_normal
#print axioms PoincareMT.M25.Topology3D.range_eq_normal_perp
#print axioms PoincareMT.M25.Topology3D.height_annihilates_iff_normal_sign
#print axioms PoincareMT.M25.Topology3D.exists_smooth_manifold_local_inverse
#print axioms PoincareMT.M25.Topology3D.mfderiv_injective_of_local_right_inverse
#print axioms PoincareMT.M25.Topology3D.exists_injective_neighborhood_of_mfderiv
#print axioms PoincareMT.M25.Topology3D.finite_regular_fiber
#print axioms PoincareMT.M25.Topology3D.exists_finite_smooth_inverse_branches
#print axioms PoincareMT.M25.Topology3D.sphere_ne_antipode
#print axioms PoincareMT.M25.Topology3D.exists_opposite_normal_branches
#print axioms PoincareMT.M25.Topology3D.collar_central_contMDiff
#print axioms PoincareMT.M25.Topology3D.collar_central_mfderiv_injective
#print axioms PoincareMT.M25.Topology3D.collar_height_critical_iff
#print axioms PoincareMT.M25.Topology3D.exists_finite_collar_height_critical_points
#print axioms PoincareMT.M25.Topology3D.fderiv_apply_fixedVector
#print axioms PoincareMT.M25.Topology3D.unit_normal_fderiv_orthogonal
#print axioms PoincareMT.M25.Topology3D.normal_second_fderiv
#print axioms PoincareMT.M25.Topology3D.height_second_fderiv
#print axioms PoincareMT.M25.Topology3D.height_hessian_kernel_iff
#print axioms PoincareMT.M25.Topology3D.height_hessian_injective
#print axioms PoincareMT.M25.Topology3D.collar_height_hessian_injective
#print axioms PoincareMT.M25.Topology3D.sphere_mvfderiv_inner_apply
#print axioms PoincareMT.M25.Topology3D.sphere_height_critical_pairing
#print axioms PoincareMT.M25.Topology3D.criticalBranch_height_mvfderiv
#print axioms PoincareMT.M25.Topology3D.criticalBranch_height_difference_nonzero
#print axioms PoincareMT.M25.Topology3D.exists_ne_of_regular_difference
#print axioms PoincareMT.M25.Topology3D.exists_injective_values_of_regular_differences
#print axioms PoincareMT.M25.Topology3D.exists_generic_collar_height

#print axioms Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff
#print axioms Poincare.Analysis.hasFDerivAt_parameter_intervalIntegral_of_contDiff
#print axioms PoincareMT.M25.Topology3D.radialDerivativeAverage
#print axioms PoincareMT.M25.Topology3D.radialDerivativeAverage_zero
#print axioms PoincareMT.M25.Topology3D.radialDerivativeAverage_contDiff
#print axioms PoincareMT.M25.Topology3D.radialDerivativeAverage_apply
#print axioms PoincareMT.M25.Topology3D.fderiv_radialDerivativeAverage_zero
#print axioms PoincareMT.M25.Topology3D.exists_smooth_quadratic_factor
#print axioms PoincareMT.M25.Topology3D.exists_binary_quadratic_coefficients
#print axioms PoincareMT.M25.Topology3D.exists_morse_quadratic_coefficients
#print axioms PoincareMT.M25.Topology3D.morseSquareMap
#print axioms PoincareMT.M25.Topology3D.morseSquareMap_zero
#print axioms PoincareMT.M25.Topology3D.morseSquareMap_identity
#print axioms PoincareMT.M25.Topology3D.exists_morse_square_chart
#print axioms PoincareMT.M25.Topology3D.exists_morse_chart_zero
#print axioms PoincareMT.M25.Topology3D.exists_morse_chart
#print axioms PoincareMT.M25.Topology3D.exists_surface_morse_chart
#print axioms PoincareMT.M25.Topology3D.exists_generic_collar_morse_height
#print axioms PoincareMT.M25.Topology3D.exists_complementary_scalar_form
#print axioms PoincareMT.M25.Topology3D.exists_regular_function_chart
#print axioms PoincareMT.M25.Topology3D.exists_surface_regular_chart
#print axioms PoincareMT.M25.Topology3D.levelSliceChart
#print axioms PoincareMT.M25.Topology3D.levelSliceChart_source
#print axioms PoincareMT.M25.Topology3D.levelSliceChart_apply
#print axioms PoincareMT.M25.Topology3D.exists_regular_level_line_chart
#print axioms PoincareMT.M25.Topology3D.locallyConnected_regular_surface_level
#print axioms PoincareMT.M25.Topology3D.finite_regular_surface_level_components
#print axioms PoincareMT.M25.Topology3D.flow_orbit_surjective
#print axioms PoincareMT.M25.Topology3D.flowReturnTimes
#print axioms PoincareMT.M25.Topology3D.flow_eq_iff_sub_mem_returnTimes
#print axioms PoincareMT.M25.Topology3D.exists_positive_flow_period
#print axioms PoincareMT.M25.Topology3D.exists_flow_circle_homeomorph
#print axioms PoincareMT.M25.Topology3D.heightCrossMap
#print axioms PoincareMT.M25.Topology3D.heightCrossMap_apply
#print axioms PoincareMT.M25.Topology3D.heightCrossMap_normal
#print axioms PoincareMT.M25.Topology3D.heightCrossMap_height
#print axioms PoincareMT.M25.Topology3D.heightCrossMap_ne_zero
#print axioms PoincareMT.M25.Topology3D.heightCrossMap_ne_zero_of_regular_derivative
#print axioms PoincareMT.M25.Topology3D.gradientHeightCross_contDiffOn
#print axioms PoincareMT.M25.Topology3D.exists_compact_level_tangent_field
#print axioms PoincareMT.M25.Topology3D.collarHeightLevel
#print axioms PoincareMT.M25.Topology3D.collarHeightLevel_compact
#print axioms PoincareMT.M25.Topology3D.collar_regular_height_cross_ne_zero
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_level_field
#print axioms PoincareMT.M25.Topology3D.boundedFieldFlow
#print axioms PoincareMT.M25.Topology3D.realFlow_component_invariant
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_level_flow
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_component_flow
#print axioms PoincareMT.M25.Topology3D.exists_curve_time_chart
#print axioms PoincareMT.M25.Topology3D.curve_isOpenMap_of_time_charts
#print axioms PoincareMT.M25.Topology3D.curve_injOn_interval_of_time_chart
#print axioms PoincareMT.M25.Topology3D.collarLevelHomeomorph
#print axioms PoincareMT.M25.Topology3D.collarLevelHomeomorph_apply
#print axioms PoincareMT.M25.Topology3D.collarLevelHomeomorph_symm_eq
#print axioms PoincareMT.M25.Topology3D.collarHeightLevel_locallyConnected
#print axioms PoincareMT.M25.Topology3D.finite_collarHeightLevel_components
#print axioms PoincareMT.M25.Topology3D.exists_collar_level_curve_time_chart
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_component_period

#print axioms PoincareMT.M25.Topology3D.glueOpenCharts
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_source
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_target
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_eqOn_left
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_eqOn_right
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_symm_eqOn_left
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_symm_eqOn_right
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_contDiffOn
#print axioms PoincareMT.M25.Topology3D.glueOpenCharts_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.compactChart_closure_image
#print axioms PoincareMT.M25.Topology3D.compactChart_frontier_image
#print axioms PoincareMT.M25.Topology3D.compactChart_closure_ball
#print axioms PoincareMT.M25.Topology3D.compactChart_frontier_ball
#print axioms PoincareMT.M25.Topology3D.boundedField_intervalSolution
#print axioms PoincareMT.M25.Topology3D.boundedField_globalSolution
#print axioms PoincareMT.M25.Topology3D.boundedField_solution_unique
#print axioms PoincareMT.M25.Topology3D.boundedFlow
#print axioms PoincareMT.M25.Topology3D.boundedFlow_zero
#print axioms PoincareMT.M25.Topology3D.boundedFlow_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.boundedFlow_add
#print axioms PoincareMT.M25.Topology3D.boundedFlow_neg
#print axioms PoincareMT.M25.Topology3D.boundedFlowEquiv
#print axioms PoincareMT.M25.Topology3D.boundedFlow_injective
#print axioms PoincareMT.M25.Topology3D.boundedFlow_surjective
#print axioms PoincareMT.M25.Topology3D.boundedFlow_eq_self
#print axioms PoincareMT.M25.Topology3D.boundedFlow_support_subset
#print axioms PoincareMT.M25.Topology3D.boundedFlow_hasCompactSupport
#print axioms PoincareMT.M25.Topology3D.compactField_bounds
#print axioms PoincareMT.M25.Topology3D.compactField_globalSolution
#print axioms PoincareMT.M25.Topology3D.boundedFlow_preserves_linear
#print axioms PoincareMT.M25.Topology3D.boundedFlow_preserves_height
#print axioms PoincareMT.M25.Topology3D.boundedFlow_local_smooth
#print axioms PoincareMT.M25.Topology3D.boundedFlow_smooth_strip
#print axioms PoincareMT.M25.Topology3D.boundedFlow_smooth_multiple
#print axioms PoincareMT.M25.Topology3D.boundedFlow_contDiff_of_smooth_strip
#print axioms PoincareMT.M25.Topology3D.boundedFlow_contDiff
#print axioms PoincareMT.M25.Topology3D.boundedFlowDiffeomorph
#print axioms PoincareMT.M25.Topology3D.boundedFlow_eq_affine_on
#print axioms PoincareMT.M25.Topology3D.boundedFlow_eq_affine_of_large_norm
#print axioms PoincareMT.M25.Topology3D.boundedFlow_smooth_strip_of_compact_perturbation
#print axioms PoincareMT.M25.Topology3D.boundedFlow_contDiff_of_compact_perturbation
#print axioms PoincareMT.M25.Topology3D.clockField
#print axioms PoincareMT.M25.Topology3D.boundedClockFlow_fst
#print axioms PoincareMT.M25.Topology3D.clockEvolution
#print axioms PoincareMT.M25.Topology3D.boundedClockFlow_eq
#print axioms PoincareMT.M25.Topology3D.clockEvolution_self
#print axioms PoincareMT.M25.Topology3D.clockEvolution_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.clockEvolution_trans
#print axioms PoincareMT.M25.Topology3D.clockEvolution_reverse
#print axioms PoincareMT.M25.Topology3D.clockEvolutionEquiv
#print axioms PoincareMT.M25.Topology3D.clockField_contDiff
#print axioms PoincareMT.M25.Topology3D.clockField_compact_perturbation
#print axioms PoincareMT.M25.Topology3D.clockField_bounds
#print axioms PoincareMT.M25.Topology3D.boundedClockFlow_contDiff
#print axioms PoincareMT.M25.Topology3D.clockEvolution_contDiff
#print axioms PoincareMT.M25.Topology3D.clockEvolutionDiffeomorph
#print axioms PoincareMT.M25.Topology3D.clockEvolution_preserves_height
#print axioms PoincareMT.M25.Topology3D.exists_compact_smooth_cutoff
#print axioms PoincareMT.M25.Topology3D.contDiff_cutoff_smul
#print axioms PoincareMT.M25.Topology3D.exists_compactField_extension
#print axioms PoincareMT.M25.Topology3D.cutoff_smul_preserves_linear
#print axioms PoincareMT.M25.Topology3D.exists_compactField_extension_preserving
#print axioms PoincareMT.M25.Topology3D.criticalValues_null
#print axioms PoincareMT.M25.Topology3D.dense_opposite_regularValues
#print axioms PoincareMT.M25.Topology3D.isOpen_image_of_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.isOpenMap_restrict_of_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart_apply
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart_source
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart_target
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.smoothOpenChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.exists_injective_product_neighborhood
#print axioms PoincareMT.M25.Topology3D.exists_injective_uniform_tube
#print axioms PoincareMT.M25.Topology3D.boundedFlow_mapsTo_set
#print axioms PoincareMT.M25.Topology3D.boundedFlow_preserves_firstIntegral
#print axioms PoincareMT.M25.Topology3D.boundedFlow_intertwines_on
#print axioms PoincareMT.M25.Topology3D.scalarFlow_eq_add_on
#print axioms PoincareMT.M25.Topology3D.regularFlow_height
#print axioms PoincareMT.M25.Topology3D.regularFlow_back_height
#print axioms PoincareMT.M25.Topology3D.regularLevelEquiv
#print axioms PoincareMT.M25.Topology3D.regularLevelEquiv_apply
#print axioms PoincareMT.M25.Topology3D.regularLevelEquiv_symm_apply
#print axioms PoincareMT.M25.Topology3D.regularLevelHomeomorph
#print axioms PoincareMT.M25.Topology3D.regularFlow_back_contDiffOn
#print axioms PoincareMT.M25.Topology3D.tangentHeightVector
#print axioms PoincareMT.M25.Topology3D.tangentHeightVector_normal
#print axioms PoincareMT.M25.Topology3D.tangentHeightVector_height
#print axioms PoincareMT.M25.Topology3D.tangentHeightField
#print axioms PoincareMT.M25.Topology3D.tangentHeightField_normal
#print axioms PoincareMT.M25.Topology3D.tangentHeightField_height
#print axioms PoincareMT.M25.Topology3D.tangentHeightVector_contDiffOn
#print axioms PoincareMT.M25.Topology3D.tangentHeightField_contDiffOn
#print axioms PoincareMT.M25.Topology3D.tangentHeightField_defining_derivative
#print axioms PoincareMT.M25.Topology3D.contDiffOn_gradient_of_isOpen
#print axioms PoincareMT.M25.Topology3D.tangentHeightField_cutoff
#print axioms PoincareMT.M25.Topology3D.exists_manifold_source_local_inverse
#print axioms PoincareMT.M25.Topology3D.manifold_isOpen_image
#print axioms PoincareMT.M25.Topology3D.manifold_isOpenMap_restrict
#print axioms PoincareMT.M25.Topology3D.manifoldOpenChart
#print axioms PoincareMT.M25.Topology3D.manifoldOpenChart_apply
#print axioms PoincareMT.M25.Topology3D.manifoldOpenChart_source
#print axioms PoincareMT.M25.Topology3D.manifoldOpenChart_target
#print axioms PoincareMT.M25.Topology3D.manifoldOpenChart_symm_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.collarParameter
#print axioms PoincareMT.M25.Topology3D.collarParameter_apply
#print axioms PoincareMT.M25.Topology3D.collarParameter_level
#print axioms PoincareMT.M25.Topology3D.collarParameter_contDiffOn
#print axioms PoincareMT.M25.Topology3D.collarParameter_fderiv_ne_zero
#print axioms PoincareMT.M25.Topology3D.clockField_slice_lipschitz
#print axioms PoincareMT.M25.Topology3D.clockEvolution_tracks
#print axioms PoincareMT.M25.Topology3D.clockEvolution_eq_self
#print axioms PoincareMT.M25.Topology3D.clockEvolution_support_subset
#print axioms PoincareMT.M25.Topology3D.clockEvolution_hasCompactSupport
#print axioms PoincareMT.M25.Topology3D.exists_smooth_product_chart
#print axioms PoincareMT.M25.Topology3D.exists_collar_defining_function
#print axioms PoincareMT.M25.Topology3D.clockGraphDiffeomorph
#print axioms PoincareMT.M25.Topology3D.clockGraphDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.clockGraphDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.flowTubeChart
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_apply
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_source
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_symm_apply
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.flowTubeChart_boundary
#print axioms PoincareMT.M25.Topology3D.exists_smooth_positive_profile
#print axioms PoincareMT.M25.Topology3D.exists_smooth_profile_between
#print axioms PoincareMT.M25.Topology3D.fiberScalingDiffeomorph
#print axioms PoincareMT.M25.Topology3D.fiberScalingDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.fiberScalingDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.exists_bounded_flatCap_profile
#print axioms PoincareMT.M25.Topology3D.exists_flatCap_profile
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph_cap
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph_cylinder
#print axioms PoincareMT.M25.Topology3D.flatCapDiffeomorph_fst_norm_le
#print axioms PoincareMT.M25.Topology3D.heightCoordinates
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_fst_apply
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_snd_apply
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_symm_apply
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_norm_sq
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_symm_norm_sq
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_image_ball
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_image_closedBall
#print axioms PoincareMT.M25.Topology3D.heightCoordinates_image_sphere
#print axioms PoincareMT.M25.Topology3D.clockEvolution_preserves_linear
#print axioms PoincareMT.M25.Topology3D.exists_ambient_isotopy_of_localField
#print axioms PoincareMT.M25.Topology3D.isPreconnected_compl_of_neighborhood
#print axioms PoincareMT.M25.Topology3D.isConnected_unitAnnulus
#print axioms PoincareMT.M25.Topology3D.compactChart_exterior_connected
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_apply
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_source
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_target
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.closedBall_subset_discChart_source
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_image_sphere
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.discChart_image_closedBall
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.closure_inside_eq_discChart_image
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.frontier_inside_eq_range
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_apply
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_source
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_target
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_boundary
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.cylinderChart_image_inside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closedRegion
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.boundary
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_open
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_connected
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_disjoint_boundary
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.exists_larger_ball
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closedRegion_compact
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_bounded
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closure_inside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.frontier_inside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_union_boundary
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.outside_connected
#print axioms PoincareMT.M25.Topology3D.exists_flatCapBallChart
#print axioms PoincareMT.M25.Topology3D.exists_collar_chart
#print axioms PoincareMT.M25.Topology3D.collar_image_open
#print axioms PoincareMT.M25.Topology3D.exists_sphere_collar_defining_function
#print axioms PoincareMT.M25.Topology3D.collar_closedBand_compact
#print axioms PoincareMT.M25.Topology3D.chartRadialField
#print axioms PoincareMT.M25.Topology3D.chartRadialField_contDiffOn
#print axioms PoincareMT.M25.Topology3D.chartRadialField_track_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.exists_ball_shrinking_isotopy
#print axioms PoincareMT.M25.Topology3D.inwardField_radial_bound
#print axioms PoincareMT.M25.Topology3D.boundedFlow_mapsTo_closedBall
#print axioms PoincareMT.M25.Topology3D.exists_capContraction_cutoff
#print axioms PoincareMT.M25.Topology3D.capContractionCoefficient
#print axioms PoincareMT.M25.Topology3D.capContractionCoefficient_bounds
#print axioms PoincareMT.M25.Topology3D.capContractionField
#print axioms PoincareMT.M25.Topology3D.capContractionField_contDiff
#print axioms PoincareMT.M25.Topology3D.capContractionField_radial
#print axioms PoincareMT.M25.Topology3D.capContractionField_inward
#print axioms PoincareMT.M25.Topology3D.capContractionField_tangent
#print axioms PoincareMT.M25.Topology3D.capContractionField_attraction
#print axioms PoincareMT.M25.Topology3D.capFlow_mapsTo_closedBall
#print axioms PoincareMT.M25.Topology3D.capFlow_distance_sq_le
#print axioms PoincareMT.M25.Topology3D.capFlow_height_mono
#print axioms PoincareMT.M25.Topology3D.capFlow_mapsTo_cap
#print axioms PoincareMT.M25.Topology3D.capFlow_eventually_mapsTo_ball
#print axioms PoincareMT.M25.Topology3D.exists_cap_shrinking_isotopy
#print axioms PoincareMT.M25.Topology3D.equiv_mapsTo_of_fixed_compl
#print axioms PoincareMT.M25.Topology3D.equiv_symm_fixed_of_fixed
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_of_mem
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_apply_chart
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_eq_self
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_leftInverse
#print axioms PoincareMT.M25.Topology3D.chartConjugateEquiv
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_contDiff_family
#print axioms PoincareMT.M25.Topology3D.chartConjugateMap_contDiff
#print axioms PoincareMT.M25.Topology3D.chartConjugateDiffeomorph
#print axioms PoincareMT.M25.Topology3D.chartConjugateDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.exists_chart_transport_isotopy
#print axioms PoincareMT.M25.Topology3D.exists_charted_cap_shrinking_isotopy
#print axioms PoincareMT.M25.Topology3D.chartPushforward
#print axioms PoincareMT.M25.Topology3D.chartPushforward_contDiffOn
#print axioms PoincareMT.M25.Topology3D.exists_chart_field_extension
#print axioms PoincareMT.M25.Topology3D.boundedFlow_negField
#print axioms PoincareMT.M25.Topology3D.tangentFlow_mapsTo_closedBall
#print axioms PoincareMT.M25.Topology3D.tangentFlow_image_closedBall
#print axioms PoincareMT.M25.Topology3D.boundedFlow_mapsTo_charted_ball
#print axioms PoincareMT.M25.Topology3D.boundedFlow_image_charted_ball
#print axioms PoincareMT.M25.Topology3D.exists_sphericalCap_subset
#print axioms PoincareMT.M25.Topology3D.exists_sphere_curve_with_velocity
#print axioms PoincareMT.M25.Topology3D.inner_fderiv_eq_zero_of_local_sphere
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.norm_symm_of_mem_boundary
#print axioms PoincareMT.M25.Topology3D.chartTransition_tangent
#print axioms PoincareMT.M25.Topology3D.boundedFlow_chart_pushforward
#print axioms PoincareMT.M25.Topology3D.exists_sharedBoundary_preserving_isotopy
#print axioms PoincareMT.M25.Topology3D.radialStereoMap
#print axioms PoincareMT.M25.Topology3D.radialStereoInverse
#print axioms PoincareMT.M25.Topology3D.radialStereoTarget
#print axioms PoincareMT.M25.Topology3D.radialStereoTarget_open
#print axioms PoincareMT.M25.Topology3D.radialStereoMap_norm
#print axioms PoincareMT.M25.Topology3D.radialStereoMap_contDiff
#print axioms PoincareMT.M25.Topology3D.radialStereoTarget_ne_zero
#print axioms PoincareMT.M25.Topology3D.radialStereoTarget_inner_normalize_lt
#print axioms PoincareMT.M25.Topology3D.radialStereoMap_mem_target
#print axioms PoincareMT.M25.Topology3D.radialStereoInverse_contDiffOn
#print axioms PoincareMT.M25.Topology3D.radialStereoInverse_map
#print axioms PoincareMT.M25.Topology3D.radialStereoMap_inverse
#print axioms PoincareMT.M25.Topology3D.radialStereoChart
#print axioms PoincareMT.M25.Topology3D.radialStereoChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.radialStereoChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_contDiff
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_tsupport
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_hasCompactSupport
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_flow_snd
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_flow_slice
#print axioms PoincareMT.M25.Topology3D.exists_boundaryDisc_ambient_flow
#print axioms PoincareMT.M25.Topology3D.exists_ball_radial_field
#print axioms PoincareMT.M25.Topology3D.boundedFlow_eq_chart_radial
#print axioms PoincareMT.M25.Topology3D.exists_boundaryDisc_shrinking_isotopy
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.isometryConjugate
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.isometryConjugate_apply
#print axioms PoincareMT.M25.Topology3D.space3_stereographic_dimension
#print axioms PoincareMT.M25.Topology3D.PlanarSchoenfliesData.ballNeighborhoodChart
#print axioms PoincareMT.M25.Topology3D.boundaryDisc_shrinking_of_planar
#print axioms PoincareMT.M25.Topology3D.smallPerturbation_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.smallPerturbationDiffeomorph
#print axioms PoincareMT.M25.Topology3D.smallPerturbationDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.lipschitz_smul_of_abs_le_one
#print axioms PoincareMT.M25.Topology3D.exists_smallPerturbation_isotopy
#print axioms PoincareMT.M25.Topology3D.hasFDerivAt_rescaled
#print axioms PoincareMT.M25.Topology3D.cutoff_smul_fderiv_bound
#print axioms PoincareMT.M25.Topology3D.cutoff_smul_lipschitz
#print axioms PoincareMT.M25.Topology3D.lipschitz_rescaled
#print axioms PoincareMT.M25.Topology3D.exists_small_germ_extension
#print axioms PoincareMT.M25.Topology3D.exists_identity_germ_isotopy
#print axioms PoincareMT.M25.Topology3D.norm_le_of_lipschitz_supported_ball
#print axioms PoincareMT.M25.Topology3D.horizontalFieldLift_lipschitz
#print axioms PoincareMT.M25.Topology3D.exists_radialStereo_transport_isotopy
#print axioms PoincareMT.M25.Topology3D.exists_boundary_germ_isotopy_at
#print axioms PoincareMT.M25.Topology3D.exists_boundary_germ_isotopy
#print axioms PoincareMT.M25.Topology3D.smoothChart_symm_fderiv_comp
#print axioms PoincareMT.M25.Topology3D.exists_smoothChart_derivative
#print axioms PoincareMT.M25.Topology3D.exists_normalized_chart_correction
#print axioms PoincareMT.M25.Topology3D.exists_boundary_chart_linearization
#print axioms PoincareMT.M25.Topology3D.exists_boundary_disc_affine_image
#print axioms PoincareMT.M25.Topology3D.exists_compact_field_tracking
#print axioms PoincareMT.M25.Topology3D.exists_boundary_translation
#print axioms PoincareMT.M25.Topology3D.ellipsoidRadialRatio
#print axioms PoincareMT.M25.Topology3D.ellipsoidRadialRatio_pos
#print axioms PoincareMT.M25.Topology3D.ellipsoidRadialRatio_smul
#print axioms PoincareMT.M25.Topology3D.ellipsoidRadialRatio_contDiffOn
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingField
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingField_contDiffOn
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_zero
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_ne_zero
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_one_norm
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_contDiffOn
#print axioms PoincareMT.M25.Topology3D.exists_compact_ellipsoid_rounding_field
#print axioms PoincareMT.M25.Topology3D.exists_boundary_ellipsoid_rounding
#print axioms PoincareMT.M25.Topology3D.open_eq_of_frontier_eq_of_common_exterior
#print axioms PoincareMT.M25.Topology3D.bounded_open_eq_of_frontier_eq
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.inside_eq_of_boundary_eq
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closedRegion_eq_of_boundary_eq
#print axioms PoincareMT.M25.Topology3D.compactChart_region_eq_of_boundary_eq
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_one
#print axioms PoincareMT.M25.Topology3D.ellipsoidRoundingTrack_image_sphere
#print axioms PoincareMT.M25.Topology3D.normPreservingSphereHomeomorph
#print axioms PoincareMT.M25.Topology3D.normPreservingSphereHomeomorph_apply
#print axioms PoincareMT.M25.Topology3D.radialStereo_supported_fixes_pole
#print axioms PoincareMT.M25.Topology3D.sphereDiscChart
#print axioms PoincareMT.M25.Topology3D.sphereDiscChart_closedBall_subset_source
#print axioms PoincareMT.M25.Topology3D.sphereDiscChart_apply
#print axioms PoincareMT.M25.Topology3D.exists_boundary_disc_round_boundary
#print axioms PoincareMT.M25.Topology3D.scaledBallNeighborhoodChart
#print axioms PoincareMT.M25.Topology3D.scaledBallNeighborhoodChart_apply
#print axioms PoincareMT.M25.Topology3D.scaledBallNeighborhoodChart_boundary
#print axioms PoincareMT.M25.Topology3D.scaledBallNeighborhoodChart_closedRegion
#print axioms PoincareMT.M25.Topology3D.exists_boundary_disc_round_image
#print axioms PoincareMT.M25.Topology3D.stereographicCapHeight
#print axioms PoincareMT.M25.Topology3D.stereographicCapHeight_mem_Ioo
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_opposite_height
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_cap_iff
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_image_closedBall
#print axioms PoincareMT.M25.Topology3D.exists_boundary_disc_cap
#print axioms PoincareMT.M25.Topology3D.boundaryDisc_cap_of_planar
#print axioms PoincareMT.M25.Topology3D.integralCurves_eqOn_of_local_agreement
#print axioms PoincareMT.M25.Topology3D.boundedFlow_mapsTo_of_backward_agreement
#print axioms PoincareMT.M25.Topology3D.exists_relative_ball_compression
#print axioms PoincareMT.M25.Topology3D.exists_relative_cap_compression
#print axioms PoincareMT.M25.Topology3D.exists_charted_relative_cap_compression
#print axioms PoincareMT.M25.Topology3D.exists_nested_ball_compression
#print axioms PoincareMT.M25.Topology3D.exists_disjoint_ball_compression
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize_apply
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize_image
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize_inside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize_closedRegion
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.normReparametrize_boundary
#print axioms PoincareMT.M25.Topology3D.ballPair_cap_of_planar
#print axioms PoincareMT.M25.Topology3D.relative_ball_compression_of_planar
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.interior_closedRegion
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.closure_outside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.boundary_subset_closure_sides
#print axioms PoincareMT.M25.Topology3D.ball_collar_halves
#print axioms PoincareMT.M25.Topology3D.exists_ball_collar_orientation
#print axioms PoincareMT.M25.Topology3D.chartTimeField
#print axioms PoincareMT.M25.Topology3D.chartTimeField_contDiffOn
#print axioms PoincareMT.M25.Topology3D.chartTimeField_track
#print axioms PoincareMT.M25.Topology3D.chartTimeField_preserves_linear
#print axioms PoincareMT.M25.Topology3D.exists_ambient_isotopy_of_chart
#print axioms PoincareMT.M25.Topology3D.exists_smoothChart_near_compact
#print axioms PoincareMT.M25.Topology3D.fderiv_eq_of_local_fixed_sphere
#print axioms PoincareMT.M25.Topology3D.fixedHyperplane_interpolation_injective
#print axioms PoincareMT.M25.Topology3D.fixedHyperplane_interpolation_isUnit
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_fixed
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_zero
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_one
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_contDiffOn
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_hasFDerivAt
#print axioms PoincareMT.M25.Topology3D.sphereInterpolation_invertible_derivative
#print axioms PoincareMT.M25.Topology3D.exists_sphereInterpolation_chart
#print axioms PoincareMT.M25.Topology3D.exists_sphere_collar_correction
#print axioms PoincareMT.M25.Topology3D.fixedHyperplane_normal_ne_zero
#print axioms PoincareMT.M25.Topology3D.fderiv_normal_pos_of_local_exterior
#print axioms PoincareMT.M25.Topology3D.fixedSphere_isotopy_norm_sides
#print axioms PoincareMT.M25.Topology3D.fixedSphere_isotopy_image_balls
#print axioms PoincareMT.M25.Topology3D.exists_oriented_collar_extension
#print axioms PoincareMT.M25.Topology3D.contMDiffOn_sphere_of_coe
#print axioms PoincareMT.M25.Topology3D.sphereDirection
#print axioms PoincareMT.M25.Topology3D.sphereDirection_coe
#print axioms PoincareMT.M25.Topology3D.sphereDirection_smul
#print axioms PoincareMT.M25.Topology3D.sphereDirection_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.radialSphereMap
#print axioms PoincareMT.M25.Topology3D.radialSphereMap_contMDiff
#print axioms PoincareMT.M25.Topology3D.radialSphereInverse_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.radialSphereChart
#print axioms PoincareMT.M25.Topology3D.exists_ball_boundary_parametrization
#print axioms PoincareMT.M25.Topology3D.collar_radius_bounds
#print axioms PoincareMT.M25.Topology3D.exists_collar_radial_coordinates
#print axioms PoincareMT.M25.Topology3D.exists_radial_collar_chart
#print axioms PoincareMT.M25.Topology3D.exists_ball_chart_collar_match
#print axioms PoincareMT.M25.Topology3D.exists_uniform_sphere_band
#print axioms PoincareMT.M25.Topology3D.exists_ball_collar_band
#print axioms PoincareMT.M25.Topology3D.exists_ball_outer_collar_union
#print axioms PoincareMT.M25.Topology3D.schoenfliesData_of_ball
#print axioms PoincareMT.Proofs.M09.exists_local_smooth_flow
#print axioms PoincareMT.Proofs.M09.exists_smooth_local_inverse
#print axioms PoincareMT.M25.Topology3D.complexUnitCircleHomeomorph
#print axioms PoincareMT.M25.Topology3D.complexUnitCircleHomeomorph_contMDiff
#print axioms PoincareMT.M25.Topology3D.complexUnitCircleHomeomorph_symm_contMDiff
#print axioms PoincareMT.M25.Topology3D.periodUnitCircleHomeomorph
#print axioms PoincareMT.M25.Topology3D.periodCircleParam
#print axioms PoincareMT.M25.Topology3D.periodUnitCircleHomeomorph_coe
#print axioms PoincareMT.M25.Topology3D.periodCircleParam_contMDiff
#print axioms PoincareMT.M25.Topology3D.exists_periodCircle_local_time
#print axioms PoincareMT.M25.Topology3D.contMDiff_of_smooth_period_lift
#print axioms PoincareMT.M25.Topology3D.mfderiv_injective_of_nonzero_period_lift
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_component_circle
#print axioms PoincareMT.M25.Topology3D.heightPlaneCoordinates
#print axioms PoincareMT.M25.Topology3D.heightPlaneCoordinates_snd
#print axioms PoincareMT.M25.Topology3D.heightPlaneCoordinates_reconstruct
#print axioms PoincareMT.M25.Topology3D.isPlanarEmbedding_height_projection
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_component_disc
#print axioms PoincareMT.M25.Topology3D.exists_compact_height_band_field
#print axioms PoincareMT.M25.Topology3D.tangentHeightVector_ne_zero_of_heightCross
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_band_field
#print axioms PoincareMT.M25.Topology3D.exists_symmetric_interval_of_nhdsSet
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_band_transport
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.boundary_connected
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.preconnected_subset_inside_or_outside
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.not_mutual_boundary_inside
#print axioms
  PoincareMT.M25.Topology3D.BallNeighborhoodChart.closedRegion_subset_inside_of_boundary_subset
#print axioms PoincareMT.M25.Topology3D.BallNeighborhoodChart.exists_innermost
#print axioms PoincareMT.M25.Topology3D.collarHeightLevel_eq_central_height
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_innermost_disc
#print axioms PoincareMT.M25.Topology3D.stereographicCapHeight_mem_unit_interval
#print axioms PoincareMT.M25.Topology3D.stereographicCapHeight_complement
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_image_closedBall_pos
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_cap_eq_iff
#print axioms PoincareMT.M25.Topology3D.stereoInvFun_image_sphere_pos
#print axioms PoincareMT.M25.Topology3D.sphereStereo_image_closedBall
#print axioms PoincareMT.M25.Topology3D.sphereStereo_image_sphere
#print axioms PoincareMT.M25.Topology3D.sphereStereo_complementary_discs
#print axioms PoincareMT.M25.Topology3D.normPreservingSphereDiffeomorph
#print axioms PoincareMT.M25.Topology3D.normPreservingSphereDiffeomorph_apply
#print axioms PoincareMT.M25.Topology3D.normPreservingSphereDiffeomorph_symm_apply
#print axioms PoincareMT.M25.Topology3D.exists_collar_circle_source_pullback
#print axioms PoincareMT.M25.Topology3D.exists_pole_off_regular_height
#print axioms PoincareMT.M25.Topology3D.sourceCircle_stereographic_dimension
#print axioms PoincareMT.M25.Topology3D.stereographic'_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.stereographic'_symm_contMDiff
#print axioms PoincareMT.M25.Topology3D.isPlanarEmbedding_stereographic_projection
#print axioms PoincareMT.M25.Topology3D.exists_source_circle_disc_chart
#print axioms PoincareMT.M25.Topology3D.horizontalBandProjection
#print axioms PoincareMT.M25.Topology3D.horizontalBandProjection_apply
#print axioms PoincareMT.M25.Topology3D.horizontalBandLift
#print axioms PoincareMT.M25.Topology3D.horizontalBandLift_apply
#print axioms PoincareMT.M25.Topology3D.horizontalBandProjection_lift
#print axioms PoincareMT.M25.Topology3D.horizontalBandLift_height
#print axioms PoincareMT.M25.Topology3D.horizontalBandLift_reconstruct
#print axioms PoincareMT.M25.Topology3D.horizontalBandField
#print axioms PoincareMT.M25.Topology3D.horizontalBandField_contDiff
#print axioms PoincareMT.M25.Topology3D.horizontalBandField_tsupport
#print axioms PoincareMT.M25.Topology3D.horizontalBandField_hasCompactSupport
#print axioms PoincareMT.M25.Topology3D.horizontalBandField_clock_bounds
#print axioms PoincareMT.M25.Topology3D.horizontalBandField_evolution_hasCompactSupport
#print axioms PoincareMT.M25.Topology3D.compactChart_interior_closedBall
#print axioms PoincareMT.M25.Topology3D.compactChart_frontier_closedBall
#print axioms PoincareMT.M25.Topology3D.sourceDisc_round_of_planarData
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart_source
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart_contMDiff
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart_symm_contMDiffOn
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart_image_closedBall
#print axioms PoincareMT.M25.Topology3D.roundSphereDiscChart_image_sphere
#print axioms PoincareMT.M25.Topology3D.exists_source_disc_complement
#print axioms PoincareMT.M25.Topology3D.source_sphere_two_discs_of_planar
#print axioms PoincareMT.M25.Topology3D.source_sphere_two_parametrized_discs_of_planar
#print axioms PoincareMT.M25.Topology3D.horizontalBandFlow_hasDerivAt
#print axioms PoincareMT.M25.Topology3D.horizontalBand_clockEvolution_tracks
#print axioms PoincareMT.M25.Topology3D.horizontalBand_clockEvolution_lift_tracks
#print axioms PoincareMT.M25.Topology3D.horizontalBandFlow_regular_height
#print axioms PoincareMT.M25.Topology3D.horizontalBand_regular_tracks
#print axioms PoincareMT.M25.Topology3D.horizontalBand_level_image
#print axioms PoincareMT.M25.Topology3D.horizontalBand_lift_mem_iff
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_horizontal_transport
#print axioms PoincareMT.M25.Topology3D.planarFamilyGraphDiffeomorph
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_apply
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_source
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_closedBall_subset_source
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_contDiffOn
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_symm_contDiffOn
#print axioms PoincareMT.M25.Topology3D.horizontalTubeChart_height
#print axioms PoincareMT.M25.Topology3D.exists_regular_collar_innermost_tube

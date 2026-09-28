import PoincareMT.Proofs.M35.RawFlow.IntrinsicPolynomialDecay
import PoincareMT.Proofs.M35.RawFlow.IntrinsicMetricCoefficients
import PoincareMT.Proofs.M35.RawFlow.IntrinsicCurvatureJetsBounds

/-! Batched axiom audit for the actual raw radial geometry producers. -/

set_option autoImplicit false
set_option linter.hashCommand false

#print axioms PoincareMT.M35.Uniqueness.raw_nonnegative_sectional
#print axioms PoincareMT.M35.Uniqueness.raw_curvature_derivatives_bounded_on_slab
#print axioms PoincareMT.M35.Uniqueness.intrinsicLogWarping_contDiff_norm
#print axioms PoincareMT.M35.Uniqueness.raw_intrinsic_radial_velocity_bounded
#print axioms PoincareMT.M35.Uniqueness.raw_radialArclength_hasDerivAt_velocity
#print axioms PoincareMT.M35.Uniqueness.rawInverseRadius_contDiffAt
#print axioms PoincareMT.M35.Uniqueness.rawWarpingRadius_hasDerivAt_time
#print axioms PoincareMT.M35.Uniqueness.rawWarpingSlope_hasDerivAt_time
#print axioms PoincareMT.M35.Uniqueness.rawWarpingSlope_continuousOn_slab
#print axioms PoincareMT.M35.Uniqueness.rawTangentialCurvature_bounds
#print axioms PoincareMT.M35.Uniqueness.initialEnd_scalar_norm
#print axioms PoincareMT.M35.Uniqueness.initial_axis_tail_ricci_null
#print axioms PoincareMT.M35.Uniqueness.initial_intrinsic_slope_support
#print axioms PoincareMT.M35.Uniqueness.raw_intrinsic_slope_polynomial_decay
#print axioms PoincareMT.M35.Uniqueness.raw_intrinsic_warping_jets_bounded_on_slab
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialDiffeomorph
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialInverse_fderiv
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialMetric_inner
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialMetric_inner_zero
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialMetric_rotation
#print axioms PoincareMT.M35.Uniqueness.intrinsicSpatialMetric_axisRadialCoefficient

import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceFinalChartDiagonal
import PoincareMT.Proofs.M28.Mathlib.RelativeBilinearLimits
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.Geometry.UniformMetricDistance
import PoincareMT.Proofs.M28.Mathlib.ConnectedFrontierBarrier
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.Geometry.OpenMetricScaling
import PoincareMT.Proofs.M28.Generalized.StrongNeckInverseCenterChart
import PoincareMT.Proofs.M28.Generalized.StrongNeckInverseCenterMetric
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceRawStageMetricPairing
import PoincareMT.Proofs.M28.Generalized.StrongNeckInverseCenterScalar
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceFinalChartCapture

/-!
# Direct audits of the final source-chart and distance adapters

The original source diagonal, guarded inverse normal charts, exact metric
factors, fixed ambient-frontier barrier, and distance comparisons follow
MT Sections 10.5-10.6, pp. 263-265, and M28 derivations 136, 141, 143, 144, 149.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_source_final_chart_diagonal
#print axioms ContinuousLinearMap.eventually_mutual_quadratic_bounds_of_uniform_squeeze
#print axioms PoincareMT.M28.tendstoUniformlyOn_edist_toReal_of_mutual_inner_bounds
#print axioms IsConnected.subset_of_frontier_barrier
#print axioms eventually_image_subset_of_compact_frontier_barrier
#print axioms PoincareMT.M28.intrinsicOpenMetric_scaleSmoothMetric_edist
#print axioms PoincareMT.M28.intrinsicOpenMetric_scaleSmoothMetric_edist_toReal
#print axioms PoincareMT.M28.strongNeck_center_chart_height
#print axioms PoincareMT.M28.inverseStrongNeckCenterChart
#print axioms PoincareMT.M28.inverseStrongNeckCenterChart_apply
#print axioms PoincareMT.M28.inverseStrongNeckCenterChart_domain
#print axioms PoincareMT.M28.inverseStrongNeckCenterChart_zero
#print axioms PoincareMT.M28.strongNeck_half_pullbackCoefficients
#print axioms PoincareMT.M28.inverseStrongNeckCenterChart_relative_metric
#print axioms PoincareMT.M28.CounterexampleNeckFamily.regularRawStageDiffeomorph_metric_pairing
#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.regularRawStageDiffeomorph_relative_inner_bounds
#print axioms PoincareMT.M28.exists_inverseStrongNeckCenterChart_scalar_lower_accuracy
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_source_final_chart_capture_accuracy

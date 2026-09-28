import PoincareMT.Proofs.M28.Mathlib.LastClosedVisit
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactBallRestriction
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.RegularSets.PathCapture
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CapturedPathDistance
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSuffix

/-! # Direct audits for the source-suffix topology and capture interfaces -/

set_option autoImplicit false

#print axioms Poincare.exists_last_visit_of_isClosed
#print axioms Poincare.exists_last_visit_component
#print axioms PoincareMT.M28.mem_regularPoints_intrinsicOpenMetric_of_compact_ball
open PoincareMT.M28.RegularPointedMetricConvergence in
#print axioms exists_eventually_regular_path_capture
open PoincareMT.M28.RegularPointedMetricConvergence in
#print axioms eventually_edist_le_twice_captured_path_length
#print axioms PoincareMT.M28.SourceTubeData.exists_final_initial_graph_subarc

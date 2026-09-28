import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialNodeCapture
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialScalar

/-!
# Direct axiom audit of initial-neck geometric inputs

The guarded inverse, captured literal zero node and exact initial scale
supply inputs to Morgan--Tian Proposition 10.7, p. 253; derivation 88.
-/

set_option autoImplicit false

open PoincareMT.M28

#print axioms RegularPointedMetricConvergence.stageDiffeomorph
#print axioms RegularPointedMetricConvergence.stageDiffeomorph_source
#print axioms RegularPointedMetricConvergence.stageDiffeomorph_target
#print axioms RegularPointedMetricConvergence.stageDiffeomorph_apply
#print axioms SourceTubeData.initial_node_geometry
#print axioms CounterexampleNeckFamily.tubeCritical_contains_initial_node
#print axioms CounterexampleNeckFamily.exists_retained_initial_node_capture_accuracy
#print axioms CounterexampleNeckFamily.tubeCritical_base_scalar_eq
#print axioms CounterexampleNeckFamily.regular_limit_base_scalar_eq
#print axioms CounterexampleNeckFamily.regular_limit_base_scale_eq

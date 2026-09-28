import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceCriticalBallWholeNeighborhoodProducer
import PoincareMT.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardData

/-! # Direct axiom audit of fixed whole-neck neighborhood capture -/

set_option autoImplicit false

#print axioms PoincareMT.M28.RegularPointedMetricConvergence.eventually_compact_open_edist_le
#print axioms PoincareMT.EpsilonNeck.restrict_compactClosure
#print axioms PoincareMT.EpsilonNeck.buffered_intrinsicEDist_lt
#print axioms PoincareMT.M28.CounterexampleNeckFamily.eventually_retained_whole_neighborhood_in_core
#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.exists_retained_whole_neighborhood_capture_accuracy
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_whole_neck_backward_data

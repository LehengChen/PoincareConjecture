import PoincareMT.Proofs.M13

/-!
# Actual parabolic rescaling axiom guards

The construction output types, raw operations, full M13 theorem and actual
earlier suppliers are admission-free and use only the three guarded axioms.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.parabolicInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.parabolicInterval

/-- info: 'PoincareMT.MetricHomothetyCalculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.MetricHomothetyCalculus

/-- info: 'PoincareMT.ParabolicSpacetimeRescaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ParabolicSpacetimeRescaling

/-- info: 'PoincareMT.parabolicHorizontalSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.parabolicHorizontalSection

/-- info: 'PoincareMT.backwardHorizontalVelocityWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.backwardHorizontalVelocityWithin

/-- info: 'PoincareMT.ParabolicHorizontalCalculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ParabolicHorizontalCalculus

/-- info: 'PoincareMT.ParabolicBackwardEndpointCalculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ParabolicBackwardEndpointCalculus

/-- info: 'PoincareMT.ParabolicDomainTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ParabolicDomainTransport

/-- info: 'PoincareMT.ParabolicBallNeighborhoodTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.ParabolicBallNeighborhoodTransport

/-- info: 'PoincareMT.OrdinaryParabolicRescaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.OrdinaryParabolicRescaling

/-- info: 'PoincareMT.GeneralizedParabolicRescaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedParabolicRescaling

/-- info: 'PoincareMT.GeneralizedParabolicRescalingTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedParabolicRescalingTheory

/-- info: 'PoincareMT.generalizedParabolicRescaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.generalizedParabolicRescaling

/-- info: 'PoincareMT.generalizedParabolicRescaling_from_M12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.generalizedParabolicRescaling_from_M12

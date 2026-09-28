import PoincareMT.Proofs.M83

/-!
# M83 proof closure audit

Pin the published orientation-exclusion theorem and both adapters after the
production `sorry` was removed. Independent of the repository-wide audit target.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.m83OrientationExclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m83OrientationExclusion

/-- info: 'PoincareMT.m83NoProjectivePlaneFromTopology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m83NoProjectivePlaneFromTopology

/-- info: 'PoincareMT.m83NoProjectivePlaneFromMilestones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m83NoProjectivePlaneFromMilestones

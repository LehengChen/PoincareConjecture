import PoincareMT.Proofs.M62

/-! M62 primitive geometry, exact predecessor and single-admission guards. -/

set_option autoImplicit false

/-- info: 'PoincareMT.M62ShrinkingCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M62ShrinkingCurve

/-- info: 'PoincareMT.M62.SpacetimeData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M62.SpacetimeData

/-- info: 'PoincareMT.M62.CircleProductData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M62.CircleProductData

/-- info: 'PoincareMT.M62CurveEvolutionTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M62CurveEvolutionTheory

/-- info: 'PoincareMT.m62CurvatureService_from_M04' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m62CurvatureService_from_M04

/-- info: 'PoincareMT.m62CorrectedCurveEvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m62CorrectedCurveEvolution

/-- info: 'PoincareMT.m62CorrectedCurveEvolution_from_predecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m62CorrectedCurveEvolution_from_predecessors

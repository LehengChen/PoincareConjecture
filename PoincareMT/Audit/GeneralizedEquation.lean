import PoincareMT.Proofs.M12

/-!
# Intrinsic Ricci equation axiom guards

The M12 theorem, its concrete predecessor suppliers, and the underlying
operators remain admission-free.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.horizontalMetricLieDerivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.horizontalMetricLieDerivative

/-- info: 'PoincareMT.horizontalRicci' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.horizontalRicci

/-- info: 'PoincareMT.rawHorizontalCovariantDerivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.rawHorizontalCovariantDerivative

/-- info: 'PoincareMT.movingGaugeDrift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.movingGaugeDrift

/-- info: 'PoincareMT.movingGaugeSectionTimeDerivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.movingGaugeSectionTimeDerivative

/-- info: 'PoincareMT.GeneralizedFlowCarrierConclusion.gaugeCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedFlowCarrierConclusion.gaugeCover

/-- info: 'PoincareMT.SpacetimeHorizontalConnection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SpacetimeHorizontalConnection

/-- info: 'PoincareMT.GeneralizedRicciGaugeTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedRicciGaugeTheory

/-- info: 'PoincareMT.m12MetricPredecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m12MetricPredecessors

/-- info: 'PoincareMT.generalizedRicciGaugeGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.generalizedRicciGaugeGeometry

/-- info: 'PoincareMT.generalizedRicciGaugeGeometry_from_M03_M04_M11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.generalizedRicciGaugeGeometry_from_M03_M04_M11

/-- info: 'PoincareMT.GeneralizedRicciGaugeTheory.ordinary_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedRicciGaugeTheory.ordinary_flow

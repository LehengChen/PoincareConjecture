import PoincareMT.Proofs.M11

/-!
# Actual spacetime axiom guards

The geometric records, statement types and complete M11 proof contain no
admissions. The proof tree is imported through its numbered entry.
-/

set_option autoImplicit false

/-- info: 'PoincareMT.spacetimeHorizontal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.spacetimeHorizontal

/-- info: 'PoincareMT.GeneralizedFlowSpacetime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedFlowSpacetime

/-- info: 'PoincareMT.SpacetimeSliceGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SpacetimeSliceGeometry

/-- info: 'PoincareMT.SpacetimeCylinderMetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.SpacetimeCylinderMetric

/-- info: 'PoincareMT.CompatibleSpacetimeTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.CompatibleSpacetimeTheory

/-- info: 'PoincareMT.GeneralizedSpacetimeGeometryTheory' does not depend on any axioms -/
#guard_msgs in
#print axioms PoincareMT.GeneralizedSpacetimeGeometryTheory

/-- info: 'PoincareMT.generalizedSpacetimeGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.generalizedSpacetimeGeometry

import PoincareMT.Proofs.M61

/-! M61 primitive-width, checked-adapter and single-admission axiom guards. -/

set_option autoImplicit false

/-- info: 'PoincareMT.M61WidthTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M61WidthTheory

/-- info: 'PoincareMT.m61FamilyWidth_eq_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61FamilyWidth_eq_legacy

/-- info: 'PoincareMT.m61Represents_iff_homotopic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61Represents_iff_homotopic

/-- info: 'PoincareMT.m61UniqueClassLabels_from_M59' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61UniqueClassLabels_from_M59

/-- info: 'PoincareMT.m61BasedClassWidth_from_M59' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61BasedClassWidth_from_M59

/-- info: 'PoincareMT.m61SphereWidth_from_M60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61SphereWidth_from_M60

/-- info: 'PoincareMT.m61ShortFamilyWidth_from_M60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61ShortFamilyWidth_from_M60

/-- info: 'PoincareMT.m61Widths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61Widths

/-- info: 'PoincareMT.m61Widths_from_predecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m61Widths_from_predecessors

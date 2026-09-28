import PoincareMT.Proofs.M64

/-! M64 primitive statements, exact adapters and single-admission guards. -/

set_option autoImplicit false

/-- info: 'PoincareMT.M64Annulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M64Annulus

/-- info: 'PoincareMT.M64RawFamilyApproximation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M64RawFamilyApproximation

/-- info: 'PoincareMT.M64ComparisonTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M64ComparisonTheory

/-- info: 'PoincareMT.m64RawFillingArea_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m64RawFillingArea_c1

/--
info: 'PoincareMT.m64AppliedFamilyEstimates_from_M63' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.m64AppliedFamilyEstimates_from_M63

/-- info: 'PoincareMT.m64FamilyEnergyBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m64FamilyEnergyBound

/-- info: 'PoincareMT.m64AnnulusComparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m64AnnulusComparison

/--
info: 'PoincareMT.m64AnnulusComparison_from_predecessors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PoincareMT.m64AnnulusComparison_from_predecessors

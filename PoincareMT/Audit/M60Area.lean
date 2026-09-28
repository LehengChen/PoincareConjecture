import PoincareMT.Proofs.M60

/-! M60 definition, helper and single-admission axiom guards. -/

set_option autoImplicit false

/-- info: 'PoincareMT.M60SphereAreaProperties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M60SphereAreaProperties

/-- info: 'PoincareMT.M60FillingAreaProperties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M60FillingAreaProperties

/-- info: 'PoincareMT.M60AreaCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.M60AreaCore

/-- info: 'PoincareMT.m60FillingArea_le_disk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m60FillingArea_le_disk

/-- info: 'PoincareMT.m60FillingArea_nonneg_of_disk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m60FillingArea_nonneg_of_disk

/-- info: 'PoincareMT.m60ShortLoopAreaClaim_from_M58' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m60ShortLoopAreaClaim_from_M58

/-- info: 'PoincareMT.m60AreaAndFilling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m60AreaAndFilling

/-- info: 'PoincareMT.m60AreaAndFilling_from_predecessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.m60AreaAndFilling_from_predecessors

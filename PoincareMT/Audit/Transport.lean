import PoincareMT.Definitions.M57Transport
import PoincareMT.Statements.M57Transport
import PoincareMT.Proofs.M57

/-! Admission boundary for the local ancestry-transport milestone. -/

/-
The definitions and statement are admission-free; only the theorem-owned
proof has the expected `sorryAx` dependency.
-/

/-- info: 'PoincareMT.RepairedAncestryTransportInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedAncestryTransportInput

/-- info: 'PoincareMT.RepairedAncestryTransportData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedAncestryTransportData

/-- info: 'PoincareMT.RepairedComparisonProviderRealization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedComparisonProviderRealization

/-- info: 'PoincareMT.RepairedTransportTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedTransportTheory

/-- info: 'PoincareMT.repairedAncestryTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedAncestryTransport

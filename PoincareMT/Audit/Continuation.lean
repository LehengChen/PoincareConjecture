import PoincareMT.Proofs.M41
import PoincareMT.Proofs.M42
import PoincareMT.Proofs.M43
import PoincareMT.Definitions.M44CapPersistence
import PoincareMT.Statements.M44CapPersistence
import PoincareMT.Proofs.M44
import PoincareMT.Proofs.M44.Providers

/-! Admission boundaries for the branch-specific continuation milestones. -/

/-- info: 'PoincareMT.RepairedNonemptyContinuationData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedNonemptyContinuationData

/-- info: 'PoincareMT.RepairedNonemptyContinuationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedNonemptyContinuationTheory

/-- info: 'PoincareMT.repairedNonemptyContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedNonemptyContinuation

/-! M42 keeps the vanishing certificate at the exact M33 branch. -/

/-- info: 'PoincareMT.RepairedVanishingContinuationData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedVanishingContinuationData

/-- info: 'PoincareMT.RepairedVanishingContinuationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedVanishingContinuationTheory

/-- info: 'PoincareMT.repairedVanishingContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedVanishingContinuation

/-! M43 assembles the two constructor-disjoint branch certificates. -/

/-- info: 'PoincareMT.RepairedUnifiedContinuationData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedUnifiedContinuationData

/-- info: 'PoincareMT.RepairedUnifiedContinuationTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedUnifiedContinuationTheory

/-- info: 'PoincareMT.repairedUnifiedContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedUnifiedContinuation

/-! M44 packages cap persistence from the three explicit predecessor theories. -/

/-- info: 'PoincareMT.RepairedCapPersistenceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedCapPersistenceData

/-- info: 'PoincareMT.RepairedCapPersistenceTheory' does not depend on any axioms -/
#guard_msgs in
#print axioms PoincareMT.RepairedCapPersistenceTheory

/-- info: 'PoincareMT.repairedCapPersistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedCapPersistence

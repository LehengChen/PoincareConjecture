import PoincareMT.Definitions.M54GroupEffects
import PoincareMT.Statements.M54GroupEffects
import PoincareMT.Proofs.M54

/-! Admission boundaries for the finite-group persistence milestone. -/

/-- info: 'PoincareMT.FiniteOrCyclicFactors' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.FiniteOrCyclicFactors

/-- info: 'PoincareMT.RepairedGroupFactorData' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGroupFactorData

/-- info: 'PoincareMT.RepairedSurgeryGroupEffectsData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedSurgeryGroupEffectsData

/-- info: 'PoincareMT.RepairedGroupPersistenceInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGroupPersistenceInput

/-- info: 'PoincareMT.RepairedGroupEffectsTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGroupEffectsTheory

/-- info: 'PoincareMT.repairedGroupEffects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedGroupEffects

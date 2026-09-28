import PoincareMT.Definitions.M47CanonicalInduction
import PoincareMT.Statements.M47CanonicalInduction
import PoincareMT.Proofs.M47

/-! Admission boundaries for the canonical-neighborhood induction milestone. -/

/-- info: 'PoincareMT.RepairedCanonicalInductionData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedCanonicalInductionData

/-- info: 'PoincareMT.RepairedCanonicalInductionTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedCanonicalInductionTheory

/-- info: 'PoincareMT.repairedCanonicalInduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedCanonicalInduction

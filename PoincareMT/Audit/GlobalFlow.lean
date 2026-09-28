import PoincareMT.Definitions.M52GlobalFlow
import PoincareMT.Statements.M52GlobalFlow
import PoincareMT.Proofs.M52

/-! Admission boundaries for the global controlled-flow milestone. -/

/-- info: 'PoincareMT.RepairedGlobalFlowData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGlobalFlowData

/-- info: 'PoincareMT.RepairedGlobalFlowTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGlobalFlowTheory

/-- info: 'PoincareMT.repairedGlobalFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedGlobalFlow

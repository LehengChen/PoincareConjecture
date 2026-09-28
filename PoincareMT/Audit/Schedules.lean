import PoincareMT.Definitions.M45ControlledSchedules
import PoincareMT.Statements.M45ControlledSchedules
import PoincareMT.Proofs.M45.Providers

/-! Admission boundaries for the controlled-schedule milestone. -/

/-- info: 'PoincareMT.RepairedControlledSchedulesData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedControlledSchedulesData

/-- info: 'PoincareMT.RepairedControlledSchedulesTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedControlledSchedulesTheory

/-- info: 'PoincareMT.repairedControlledSchedules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedControlledSchedules

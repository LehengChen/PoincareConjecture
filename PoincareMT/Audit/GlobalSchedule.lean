import PoincareMT.Definitions.M51GlobalSchedule
import PoincareMT.Statements.M51GlobalSchedule
import PoincareMT.Proofs.M51

/-! Admission boundaries for the global schedule milestone. -/

/-- info: 'PoincareMT.RepairedGlobalScheduleData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGlobalScheduleData

/-- info: 'PoincareMT.RepairedGlobalScheduleTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedGlobalScheduleTheory

/-- info: 'PoincareMT.repairedGlobalSchedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedGlobalSchedule

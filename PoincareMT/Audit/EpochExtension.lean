import PoincareMT.Definitions.M48EpochExtension
import PoincareMT.Statements.M48EpochExtension
import PoincareMT.Proofs.M48

/-! Admission boundaries for the one-step epoch-extension milestone. -/

/-- info: 'PoincareMT.RepairedEpochExtensionData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedEpochExtensionData

/-- info: 'PoincareMT.RepairedEpochExtensionTheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedEpochExtensionTheory

/-- info: 'PoincareMT.repairedEpochExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedEpochExtension

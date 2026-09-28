import PoincareMT.Definitions.M49VolumeLoss
import PoincareMT.Statements.M49VolumeLoss
import PoincareMT.Proofs.M49
import PoincareMT.Proofs.M49.LeftLimitVolume
import PoincareMT.Proofs.M49.Lemma17_12_VolumeGrowth

/-! Admission boundaries for the corrected surgery volume-loss milestone. -/

/-- info: 'PoincareMT.RepairedSurgeryEventLossData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedSurgeryEventLossData

/-- info: 'PoincareMT.RepairedVolumeLossData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.RepairedVolumeLossData

/-- info: 'PoincareMT.RepairedVolumeLossTheory' does not depend on any axioms -/
#guard_msgs in
#print axioms PoincareMT.RepairedVolumeLossTheory

/-- info: 'PoincareMT.repairedVolumeLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.repairedVolumeLoss

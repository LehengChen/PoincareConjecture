import PoincareMT.Proofs.M05

/-!
# M05 proof closure audit

This focused audit keeps the Hamilton--Ivey integration check independent of
the repository-wide audit target.
-/

/-- info: 'PoincareMT.hamiltonIveyPinching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.hamiltonIveyPinching

/-- info: 'PoincareMT.hamiltonIveyPinching_from_M04' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoincareMT.hamiltonIveyPinching_from_M04

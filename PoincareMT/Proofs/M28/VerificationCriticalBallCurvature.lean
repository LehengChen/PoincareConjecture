import PoincareMT.Proofs.M28.Sec10_3_Tube.CriticalBallCurvature

/-! Kernel audit for the critical-ball curvature interface. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28
open PoincareMT.M28.CounterexampleNeckFamily

#print axioms CounterexampleNeckFamily.eventually_scalar_le_on_critical_regularComponent
#print axioms PoincareMT.M28.CounterexampleNeckFamily.hcurv_on_criticalBall

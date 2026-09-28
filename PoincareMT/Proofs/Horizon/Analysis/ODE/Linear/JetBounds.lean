import PoincareMT.Proofs.M07.Analysis.ODE.Linear.JetBounds
import PoincareMT.Proofs.Horizon.Analysis.ODE.ParameterLinear
import PoincareMT.Proofs.Horizon.Analysis.ODE.ParameterDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall

/-! Deduplicated bridge for the Horizon snapshot module
`Analysis.ODE.Linear.JetBounds`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Analysis.ODE.Linear.JetBounds`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

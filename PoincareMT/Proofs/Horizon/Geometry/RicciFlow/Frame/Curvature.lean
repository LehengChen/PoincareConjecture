import PoincareMT.Proofs.M05.Geometry.RicciFlow.Frame.Curvature
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Frame.Curvature`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.RicciFlow.Frame.Curvature`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

import PoincareMT.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Regularity
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Frame.Transport
import PoincareMT.Proofs.Horizon.Analysis.ODE.LocalFlow.ParametricLinearODE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import PoincareMT.Proofs.Horizon.Analysis.Calculus.WithinProduct

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Frame.Transport.Regularity`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Regularity`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

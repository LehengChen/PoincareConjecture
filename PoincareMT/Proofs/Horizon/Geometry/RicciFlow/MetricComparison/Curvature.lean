import PoincareMT.Proofs.M04.MetricComparison
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.MetricComparison.Curvature`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.MetricComparison`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

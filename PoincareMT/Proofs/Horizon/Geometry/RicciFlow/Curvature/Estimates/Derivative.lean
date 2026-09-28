import PoincareMT.Proofs.M04.DerivativeEstimates
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.MetricComparison.LocalCurvature
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Cutoff.Geometric
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Carrier.Recentered

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Estimates.Derivative`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.DerivativeEstimates`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

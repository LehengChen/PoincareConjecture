import PoincareMT.Proofs.M04
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.Within
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Derivative
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.MetricComparison.Curvature
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Positivity.Preservation
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Bounds.Scalar

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Construction`.
Its constants already exist on main in
`PoincareMT.Proofs.M04`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

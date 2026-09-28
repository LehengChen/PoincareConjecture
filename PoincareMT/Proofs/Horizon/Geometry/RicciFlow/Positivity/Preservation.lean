import PoincareMT.Proofs.M04.CurvaturePositivity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Positivity.Scalar.StrongMaximum
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Positivity.PointwiseFlatness
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Positivity.Ricci.Compact
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.Compact

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Positivity.Preservation`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.CurvaturePositivity`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

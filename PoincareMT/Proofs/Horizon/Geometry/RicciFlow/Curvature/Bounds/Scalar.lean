import PoincareMT.Proofs.Ch04.ScalarBounds
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace
import PoincareMT.Proofs.Horizon.Analysis.Parabolic.Maximum.ScalarComparison
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Bounds.Scalar`.
Its constants already exist on main in
`PoincareMT.Proofs.Ch04.ScalarBounds`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

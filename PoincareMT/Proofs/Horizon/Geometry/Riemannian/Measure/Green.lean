import PoincareMT.Proofs.M07.Geometry.Riemannian.Measure.Green
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.CoordinateGreen
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Local
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Measure.Green`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Measure.Green`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

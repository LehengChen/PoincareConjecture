import PoincareMT.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.Euclidean
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import PoincareMT.Proofs.Horizon.Analysis.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.ScalarOperators.Divergence`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

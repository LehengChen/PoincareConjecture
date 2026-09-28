import PoincareMT.Proofs.M01.ConnectionExistence
import PoincareMT.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.KoszulFunctional
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.Riesz
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.Smoothness
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Normalization.Connection.Existence`.
Its constants already exist on main in
`PoincareMT.Proofs.M01.ConnectionExistence`
`PoincareMT.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Existence`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

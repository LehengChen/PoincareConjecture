import PoincareMT.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.RicciContraction
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.RicciContraction.SecondDerivative
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.LaplacianTrace

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Harnack.Matrix.Bounds`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

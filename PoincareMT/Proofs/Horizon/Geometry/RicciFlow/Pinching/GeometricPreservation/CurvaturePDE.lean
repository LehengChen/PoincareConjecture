import PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.CurvaturePDE
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Pinching.GeometricPreservation.TensorConnection
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureReaction
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.Laplacian.Product
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.LaplacianTrace.Four
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.LaplacianRegularity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Pinching.GeometricPreservation.CurvaturePDE`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.CurvaturePDE`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

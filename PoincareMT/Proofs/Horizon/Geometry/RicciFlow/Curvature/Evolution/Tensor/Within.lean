import PoincareMT.Proofs.M04.TensorEvolution
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionCoefficients
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionEndpoints
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionInterior
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.RiemannEvolutionEndpoints

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Evolution.Tensor.Within`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.TensorEvolution`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

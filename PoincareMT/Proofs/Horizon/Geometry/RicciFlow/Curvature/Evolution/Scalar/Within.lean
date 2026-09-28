import PoincareMT.Proofs.M04.ScalarEvolution
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Coefficients
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Evolution.Scalar.Within`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.ScalarEvolution`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

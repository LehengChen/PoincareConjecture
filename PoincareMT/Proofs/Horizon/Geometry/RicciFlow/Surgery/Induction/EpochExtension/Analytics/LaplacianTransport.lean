import PoincareMT.Proofs.M48.LaplacianTransport
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.HessianTensorial
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.Trace
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.RicciNormTransport
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.LaplacianTransport`.
Its constants already exist on main in
`PoincareMT.Proofs.M48.LaplacianTransport`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

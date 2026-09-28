import PoincareMT.Proofs.M48.ScalarGradientTransport
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.RegularHistory
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Control.Basic
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorMetricTrace

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ScalarGradientTransport`.
Its constants already exist on main in
`PoincareMT.Proofs.M48.ScalarGradientTransport`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

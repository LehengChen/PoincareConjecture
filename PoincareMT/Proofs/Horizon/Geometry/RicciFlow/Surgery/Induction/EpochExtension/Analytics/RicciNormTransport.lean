import PoincareMT.Proofs.M48.RicciNormTransport
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Generalized
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.RicciNormTransport`.
Its constants already exist on main in
`PoincareMT.Proofs.M48.RicciNormTransport`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

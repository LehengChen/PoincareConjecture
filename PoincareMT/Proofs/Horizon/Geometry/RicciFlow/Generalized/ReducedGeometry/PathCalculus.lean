import PoincareMT.Definitions.M14PathCalculus
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Generalized.ReducedGeometry.PathCalculus`.
Its constants already exist on main in
`PoincareMT.Definitions.M14PathCalculus`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

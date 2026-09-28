import PoincareMT.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Harnack.Regularity`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

import PoincareMT.Proofs.M01.CurvatureCalculusTensorial
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Fields
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Normalization.Curvature.Tensorial`.
Its constants already exist on main in
`PoincareMT.Proofs.M01.CurvatureCalculusTensorial`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

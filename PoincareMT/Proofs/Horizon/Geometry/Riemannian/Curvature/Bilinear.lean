import PoincareMT.Proofs.M05.Geometry.Riemannian.Curvature.Bilinear
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Connection.Regularity
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Tactic.Module

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Curvature.Bilinear`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.Riemannian.Curvature.Bilinear`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

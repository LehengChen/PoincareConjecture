import PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/


/-!
# Radial curvature in isometric frames

Conjugating the retained radial curvature by an isometric frame preserves
symmetry and its Ricci trace. The transported radial vector remains in its
kernel. These are the geometric inputs to the matrix Riccati comparison.

Reference: Morgan--Tian, Theorem 1.34, p. 19.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Nonnegative sectional curvature makes the actual radial curvature
nonnegative after transport to an isometric frame. -/
theorem radialCurvatureInFrame_nonneg_of_orthonormal
    (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hP : ∀ u w, g.inner x (P u) (P w) = inner ℝ u w)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 ≤ D.sectionalCurvature x u v)
    (v : TangentSpace (𝓡 n) x) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ inner ℝ (D.radialCurvatureInFrame x P v u) u := by
  rw [← hP, radialCurvatureInFrame_apply, P.apply_symm_apply]
  exact D.curvatureTensor_diagonal_nonneg_of_orthonormal x hsec (P u) v

end PoincareMT.LeviCivitaData

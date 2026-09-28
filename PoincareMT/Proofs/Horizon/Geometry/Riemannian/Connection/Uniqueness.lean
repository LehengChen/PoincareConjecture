import PoincareMT.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Connection.Uniqueness`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/-!
# Uniqueness of the Levi-Civita connection on differentiable germs

The metric and torsion conditions determine a retained connection on locally
differentiable sections. No equality on arbitrary total sections is asserted.
This is a prerequisite for identifying curvature after coordinate changes.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The frozen fixed-extension curvature is independent of the retained
compatible torsion-free connection. -/
theorem horizon_curvature_eq (D D' : LeviCivitaData g) (x : M)
    (v w z : TangentSpace (𝓡 n) x) :
    D.curvature x v w z = D'.curvature x v w z := by
  exact D.curvatureOnFields_eq_of_contMDiffAt D'
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) z)

/-- The four-covariant curvature tensor is independent of the retained connection. -/
theorem horizon_curvatureTensor_eq (D D' : LeviCivitaData g) (x : M)
    (v w z u : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w z u = D'.curvatureTensor x v w z u := by
  simp only [curvatureTensor, D.horizon_curvature_eq D']

/-- The frozen Hilbert-Schmidt curvature norm is independent of the retained connection. -/
theorem horizon_curvatureTensorNorm_eq (D D' : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm x := by
  simp only [curvatureTensorNorm, D.horizon_curvatureTensor_eq D']

end PoincareMT.LeviCivitaData

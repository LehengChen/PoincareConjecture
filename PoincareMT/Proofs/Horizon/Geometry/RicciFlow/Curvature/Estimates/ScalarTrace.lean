import PoincareMT.Proofs.M04.ScalarEstimates
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.RicciFlow.Curvature.Estimates.ScalarTrace`.
Its constants already exist on main in
`PoincareMT.Proofs.M04.ScalarEstimates`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/


/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/ScalarEstimates.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Scalar minimum and trace estimates

Morgan-Tian, printed pp. 4-5 and Claim 4.2 on p. 64. The Hessian sign follows
by restricting to local integral curves and vanishing of the differential.
Its trace gives the Laplacian sign; the Ricci trace inequality is a
finite-dimensional calculation. Source and review records are task-local.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Filter Function Topology

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The intrinsic Hessian is nonnegative at a smooth local minimum. -/
theorem hessian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.hessian f x v v := by
  exact D.hessian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin v

/-- Tracing the local Hessian minimum inequality gives the Laplacian sign. -/
theorem laplacian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x) :
    0 ≤ D.laplacian f x := by
  exact D.laplacian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin

end PoincareMT.LeviCivitaData

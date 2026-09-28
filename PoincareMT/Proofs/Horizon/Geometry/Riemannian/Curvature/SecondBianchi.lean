import PoincareMT.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Curvature.SecondBianchi`.
Its constants already exist on main in
`PoincareMT.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/


/-!
# Differential second Bianchi identity

The commutator calculation is adapted from Chow-Liao-Qin, revision
`1b535dd102b94cc42b107cca27059687888f08b3`,
`DifferentialGeometry/Geometry/Curvature/CurvatureOperator/SecondBianchi.lean`,
`second_bianchi_levi_civita`. It uses the retained connection and curvature.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma horizon_mvfderiv_inner (D : LeviCivitaData g)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.covariantDerivativeOnFields X Y x) (Z x) +
      g.inner x (Y x) (D.covariantDerivativeOnFields X Z x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

end PoincareMT.LeviCivitaData

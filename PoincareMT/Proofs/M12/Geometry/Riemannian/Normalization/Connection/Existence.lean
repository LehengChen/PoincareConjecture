import PoincareMT.Proofs.M12.Geometry.Riemannian.Normalization.Connection.KoszulFunctional
import PoincareMT.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Riesz
import PoincareMT.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Smoothness
import PoincareMT.Proofs.M01.ConnectionExistence

/-!
M12's existence provider reuses the actual M01 connection construction.
Source: Morgan-Tian, Theorem 1.2 and formula (1.1), printed pp. 3-4.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Every smooth metric on a Hausdorff second-countable smooth manifold has
compatible torsion-free connection data, supplied by M01's existing proof. -/
theorem normalization_exists_leviCivitaData {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) :=
  m01_exists_leviCivitaData g

end PoincareMT

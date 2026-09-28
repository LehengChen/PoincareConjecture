import PoincareMT.Proofs.M04.TensorEvolutionRHS

/-!
# Interior tensor-evolution RHS adapter

This sibling restricts the reviewed frozen curvature-tensor evolution
derivative to the interior time domain.  It preserves the exact function and
RHS while changing only the derivative domain.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareMT.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Restrict the frozen tensor-evolution derivative to interior flow times. -/
theorem hasDerivWithinAt_curvatureTensor_frozen_rhs_interior
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) (interior J) t :=
  (hasDerivAt_curvatureTensor_frozen_rhs F ht x u v w z).hasDerivWithinAt

#print axioms PoincareMT.M04.hasDerivWithinAt_curvatureTensor_frozen_rhs_interior

end PoincareMT.M04

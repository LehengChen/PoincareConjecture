import PoincareMT.Proofs.M04.TensorEvolutionRHS

/-!
# Interior tensor-evolution RHS adapter

This small sibling is the consumer-facing bridge from the reviewed curvature
first-variation calculation to the frozen four-slot tensor-evolution RHS.  It
keeps the supplied tangent inputs fixed while time varies and introduces no
endpoint, compactness, positivity, or Shi hypotheses.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareMT.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Apply the reviewed first-variation identity and transport its value to the
frozen tensor heat RHS at an interior flow time. -/
theorem hasDerivAt_curvatureTensor_frozen_rhs_adapter
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) t := by
  refine (hasDerivAt_curvatureTensor_first_variation F ht x u v w z).congr_deriv ?_
  exact curvature_firstVariation_rhs_eq_frozen (F.connection t) x u v w z

end PoincareMT.M04

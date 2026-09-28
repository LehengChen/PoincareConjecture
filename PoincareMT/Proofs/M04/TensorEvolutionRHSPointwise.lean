import PoincareMT.Proofs.M04.TensorEvolutionRHS

/-!
# Pointwise tensor-evolution RHS wiring

This sibling exposes the two orientations used when the reviewed curvature
commutator and first-variation calculations are consumed by later tensor
contractions.  The statements are pointwise and introduce no endpoint,
compactness, positivity, or Shi hypotheses.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareMT.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Move the reviewed commutator insertion to the right-hand side.

The form with the unswapped derivative on the left is convenient when a
pointwise tensor Laplacian is expanded before contraction.
-/
theorem curvatureTensor_second_derivative_commutator_eq_sub_insertion
    (D : LeviCivitaData g) (x : M)
    (a b c d e f : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![a, b, c, d, e, f] =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![b, a, c, d, e, f] -
        (∑ i, D.riemannEvaluation x
          (Function.update ![c, d, e, f] i
            (D.curvature x a b (![c, d, e, f] i)))) := by
  have h := curvatureTensor_second_derivative_commutator D x a b c d e f
  linarith

/-- Orient the reviewed first-variation identity as the frozen heat RHS.

This is the exact reverse of `curvature_firstVariation_rhs_eq_frozen`, so a
consumer can rewrite a frozen tensor-evolution value back to the six-term
first-variation expression without redoing the commutator calculation.
-/
theorem curvature_frozen_rhs_eq_firstVariation
    (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d] +
        D.curvatureReaction x a b c d =
      -2 * D.ricci x (D.curvature x a b d) c -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, d, c] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, d, b, c] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, c, b, d] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, a, d, c] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, d, a, c] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, c, a, d] := by
  exact (curvature_firstVariation_rhs_eq_frozen D x a b c d).symm

end PoincareMT.M04

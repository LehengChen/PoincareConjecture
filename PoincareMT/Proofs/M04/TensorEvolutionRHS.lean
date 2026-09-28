import PoincareMT.Proofs.M04.CurvatureFirstVariation
import PoincareMT.Proofs.M04.RiemannEvolutionInterior
import PoincareMT.Proofs.M04.TensorCommutator

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareMT.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

/-- The generic covariant commutator specialized to the four-slot curvature tensor.

This is the commutator input used by the reviewed first-variation-to-heat
calculation; keeping the tuple transport here avoids repeating it at consumers.
-/
theorem curvatureTensor_second_derivative_commutator
    (D : LeviCivitaData g) (x : M)
    (a b c d e f : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![a, b, c, d, e, f] -
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![b, a, c, d, e, f] =
      -(∑ i, D.riemannEvaluation x
        (Function.update ![c, d, e, f] i
          (D.curvature x a b (![c, d, e, f] i)))) := by
  have h := covariantTensorDerivative_commutator D
    (isSmoothCovariantTensor_riemannEvaluation D) x a b ![c, d, e, f]
  have hab : Fin.cons a (Fin.cons b ![c, d, e, f]) = ![a, b, c, d, e, f] := by
    funext i
    fin_cases i <;> rfl
  have hba : Fin.cons b (Fin.cons a ![c, d, e, f]) = ![b, a, c, d, e, f] := by
    funext i
    fin_cases i <;> rfl
  rw [hab, hba] at h
  simpa only [LeviCivitaData.iteratedCovariantTensorDerivative] using h

/-- The reviewed first-variation expression is the frozen tensor heat RHS. -/
theorem curvature_firstVariation_rhs_eq_frozen
    (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    -2 * D.ricci x (D.curvature x a b d) c -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, d, c] -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, d, b, c] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, c, b, d] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, a, d, c] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, d, a, c] -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, c, a, d] =
      D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d] +
        D.curvatureReaction x a b c d := by
  exact curvature_firstVariation_eq_laplacian_add_reaction D x a b c d

/-- Interior tensor evolution, assembled from first variation and the commutator bridge. -/
theorem hasDerivAt_curvatureTensor_frozen_rhs
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) t := by
  exact (hasDerivAt_curvatureTensor_first_variation F ht x u v w z).congr_deriv
    (curvature_firstVariation_rhs_eq_frozen (F.connection t) x u v w z)

end PoincareMT.M04

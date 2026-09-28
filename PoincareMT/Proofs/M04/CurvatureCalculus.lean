import PoincareMT.Statements.Ch01.CurvatureCalculus
import PoincareMT.Proofs.M04.RicciRegularity
import PoincareMT.Proofs.M04.TensorDerivativeClosure
import PoincareMT.Proofs.M04.CurvatureSymmetries

/-!
# Curvature tensor calculus obligation

The local coordinate proof and transport to the fixed-extension evaluations
are collected in this supporting theorem owned by M04.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The explicit curvature evaluations satisfy the stated local tensor calculus. -/
theorem curvatureTensorCalculus {g : RiemannianMetric n M}
    (D : LeviCivitaData g) : D.CurvatureTensorCalculus := by
  refine ⟨M04.isSmoothCovariantTensor_riemannEvaluation D,
    M04.isSmoothCovariantTensor_ricciEvaluation D, ?_, ?_, ?_⟩
  · intro k T hT
    exact M04.isSmoothCovariantTensor_covariantTensorDerivative D hT
  · intro x u v w z
    exact ⟨M04.curvatureTensor_swap_last D x u v w z,
      M04.curvatureTensor_pair_exchange D x u v w z,
      M04.curvatureTensor_cyclic D x u v w z, M04.ricci_symm D x u v⟩
  · intro U hU X Y Z hX hY hZ x hx
    exact M04.curvatureOnFields_eq_curvature D hU hX hY hZ hx

end PoincareMT.LeviCivitaData

#print axioms PoincareMT.LeviCivitaData.curvatureTensorCalculus

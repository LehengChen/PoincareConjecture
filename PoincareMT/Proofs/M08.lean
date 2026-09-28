import PoincareMT.Statements.Ch06.LGeometry
import PoincareMT.Proofs.M04
import PoincareMT.Proofs.M08.PathBasics
import PoincareMT.Proofs.M08.VariationPaths
import PoincareMT.Proofs.M08.PathCongruence
import PoincareMT.Proofs.M08.Endpoints
import PoincareMT.Proofs.M08.ChartExtensions
import PoincareMT.Proofs.M08.RegularizedAction
import PoincareMT.Proofs.M08.MetricCompactness
import PoincareMT.Proofs.M08.AdmissiblePaths
import PoincareMT.Proofs.M08.MinimizerAbstract
import PoincareMT.Proofs.M08.CompleteMinimizer
import PoincareMT.Proofs.M08.EulerLagrange
import PoincareMT.Proofs.M08.RegularizedGeodesic
import PoincareMT.Proofs.M08.FirstVariation
import PoincareMT.Proofs.M08.IndexKernel
import PoincareMT.Proofs.M08.ExtensionToZero
import PoincareMT.Proofs.M08.SecondVariation
import PoincareMT.Proofs.M08.JacobiInitialValue

/-!
# L-geodesic proof assembly

The theorem assembles the ordinary fixed-carrier analytic and ODE argument
from Morgan--Tian Sections 6.1--6.4 and Chapter 7. The owned producers supply
all nine fields of `LGeodesicTheory`, relative to the M04 curvature package.
-/

/-! M08 is the numbered review and proof entry point. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- M08: given M04, an ordinary Ricci flow on a connected smooth manifold,
complete with one curvature bound on [T-taumax,T] for taumax > 0, admits
minimizing backward L-paths and realizes the reduced-length infimum. Minimizers
satisfy Euler's equation; every Euler path has a smooth square-root-time
representative and extends uniquely toward backward time zero. Smooth
square-root-time variations satisfy the first and second variation formulas
with both endpoint terms. At minimizers the fixed-endpoint index kernel is
exactly the Jacobi fields; initial-zero Jacobi fields exist uniquely for every
prescribed square-root initial derivative, without a terminal-zero condition.

Sources: Morgan-Tian Definitions 6.1-6.2, p. 106; Lemma 6.4, pp. 107-108;
Lemma 6.8, p. 108; Lemmas 6.10/6.12 and Proposition 6.13, pp. 109-112;
Proposition 6.33 and Claim 6.34, pp. 120-122; Lemmas 7.2-7.3, pp. 150-151.
The actual pullback Jacobi derivative includes the connection-time correction.
`reviews/contracts/M08-repair-contract.md` records this transport and the
FORMAL-M08-SPATIAL-VELOCITY, FORMAL-M08-VARIATION-ENDPOINTS and
FORMAL-M08-PREDECESSOR repairs. Endpoint smoothness concerns representatives
in square-root time and does not extend the flow equation outside its domain. -/
theorem lGeodesicExistenceAndVariation
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    Nonempty (LGeodesicTheory F T τmax) := by
  refine ⟨{
    minimizing_existence := ?_
    euler_lagrange := ?_
    regularized_geodesic := ?_
    first_variation := ?_
    second_variation_jacobi := ?_
    extension_to_zero := ?_
    reduced_length_attained := ?_
    second_variation := ?_
    jacobi_initial_value := ?_
  }⟩
  · intro τ₁ τ₂ hτ₁ hordered hτ₂ p₁ p₂
    exact M08.exists_minimizing_backward_path hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ p₁ p₂
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact M08.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p hp
    exact M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
  · intro τ₁ τ₂ _ _ hτ₂ p V
    exact M08.exists_firstVariation hM04 hwindow hτ₂ V
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    have hEuler := M08.isBackwardLGeodesic_of_minimizing hM04 hwindow hcurvature hτ₂ p hp
    obtain ⟨R⟩ := M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hEuler
    exact M08.exists_fixedEndpointSecondVariation hM04 hp R V
  · intro τ₁ τ₂ hτ₁ _ hτ₂ p hp
    exact M08.exists_backward_geodesic_extension hM04 hwindow hcurvature hτ₁ hτ₂ p hp
  · intro τ hτ hτmax p q
    exact M08.reducedLength_attained_of_exists_minimizing
      (M08.exists_minimizing_backward_path hM04 hT hwindow hcurvature le_rfl hτ hτmax p q)
  · intro τ₁ τ₂ _ _ hτ₂ p hp V
    obtain ⟨R⟩ := M08.nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hτ₂ p hp
    exact M08.exists_secondVariation hM04 V R
  · intro τ₁ τ₂ _ _ _ p R Z
    exact M08.exists_lJacobi_initialValue F hM04 p R Z

/-- M08 with the reviewed M04 curvature package supplied explicitly. -/
theorem lGeodesicExistenceAndVariation_from_M04
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (LGeodesicTheory F T τmax) := by
  exact lGeodesicExistenceAndVariation F T τmax hT hτmax hwindow hcurvature
    ricciFlowCurvatureTheory

end PoincareMT

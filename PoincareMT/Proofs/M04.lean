import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Proofs.M04.CurvatureCalculus
import PoincareMT.Proofs.M04.TensorNorm
import PoincareMT.Proofs.M04.ScalarEvolution
import PoincareMT.Proofs.M04.TensorEvolution
import PoincareMT.Proofs.M04.DerivativeEstimates
import PoincareMT.Proofs.M04.MetricComparison
import PoincareMT.Proofs.M04.CurvaturePositivity
import PoincareMT.Proofs.Ch04.ScalarBounds

/-!
# Typed assembly of milestone M04

Each field is supplied by its explicit component theorem. This adds no proof
placeholder and remains relative to the inventoried geometric obligations.
-/

/-! M04 is the numbered review and proof entry point. -/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M04: the selected smooth metric and compatible connection satisfy curvature
tensor calculus, and ordinary Ricci flows satisfy scalar, Ricci and Riemann
evolution. Under the stated spacetime curvature and compact-ball controls they
obey Shi derivative estimates and metric comparison. Compact three-dimensional
flows preserve nonnegative sectional/Ricci curvature; connected flows with
nonnegative sectional curvature satisfy scalar-zero rigidity. Given the stated
initial scalar lower bounds, compact flows obey the negative scalar barrier,
including -6 / (1 + 4*t) in dimension three for initial time a >= 0.

Sources: Morgan-Tian Chapter 1, pp. 3-8; Theorem 3.13 and Lemma 3.15,
pp. 41-42; Theorems 3.28-3.29, pp. 51-52; Proposition 4.1, pp. 64-65;
Corollaries 4.14-4.15, pp. 69-70; Theorem 4.18, pp. 71-72.
Use the corrected Ricci contraction and eigenvalue-concavity convention in
`reviews/errata/2026-09-11-tensor-evolution.md`, the scalar sign correction in
`reviews/errata/2026-09-10-analytic-outline-audit.md`, and the retained spacetime
cutoff hypotheses of `reviews/declarations/curvature-estimates-v1.md`.
This established component assembly adds no admission of its own. -/
theorem ricciFlowCurvatureTheory : RicciFlowCurvatureTheory.{u} := by
  exact {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
    curvature_norm_zero := @LeviCivitaData.curvatureDerivativeNorm_zero
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor
    ricci_evolution := @RicciFlow.hasDerivWithinAt_ricci
    local_derivative_estimates := @local_curvatureDerivative_bound
    initial_derivative_estimates := @local_curvatureDerivative_bound_of_initial
    metric_comparison := @RicciFlow.metric_comparison_of_curvature_bound
    sectional_preservation := @RicciFlow.nonnegativeSectionalCurvature_preserved
    ricci_preservation := @RicciFlow.nonnegativeRicciCurvature_preserved
    scalar_zero_rigidity := @RicciFlow.flat_of_scalarCurvature_eq_zero
    scalar_lower_bound := @RicciFlow.scalarCurvature_lowerBound
    normalized_scalar_lower_bound := @RicciFlow.scalarCurvature_lowerBound_three }

end PoincareMT

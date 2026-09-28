import PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.ManifoldJacobiPairing
import PoincareMT.Statements.M64Comparison

/-!
# Proposition 19.35: intrinsic Jacobi estimate

This is the dimension-two adapter for the closed M07 Jacobi pairing estimate.
It keeps the actual Levi-Civita connection and the actual curvature norm of an
`IntrinsicAnnulus`; callers supply the radial geodesic, Jacobi equation, and
curvature-speed bounds produced by the exponential chart.  The adapter is
statement-preserving and introduces no new geometric premise into the public
M64 contract.

Source: M07 intrinsic Jacobi comparison and Morgan--Tian Proposition 19.35,
pp. 467--481.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

open ConnectionAlongCurve ConnectionVariation

set_option maxHeartbeats 1000000 in
-- The M07 adapter unfolds the transported Jacobi fields and needs a larger budget.
/-- M07's half-pairing estimate specialized to the two-dimensional metric of an intrinsic
annulus. Source: MT Proposition 19.35, pp. 467-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_manifold_jacobi_half_inner_one_lower_bound
    (N : IntrinsicAnnulus) {q : ℝ → AnnulusCoordinates} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 2) (q t)} {K c : ℝ}
    (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hsub : Icc 0 1 ⊆ I)
    (hjac : ∀ t ∈ I,
      manifoldCovDerivAlong N.metric q
          (manifoldCovDerivAlong N.metric q J 1) 1 t =
        -N.connection.curvature (q t) (J t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1))
    (hK : ∀ t ∈ Icc 0 1,
      N.connection.curvatureTensorNorm (q t) ≤ K)
    (hc : ∀ t ∈ Icc 0 1,
      N.metric.tangentNorm (q t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1) = c)
    (hcr : c ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hJ0 : J 0 = 0) :
    N.metric.tangentNorm (q 0)
        (manifoldCovDerivAlong N.metric q J 1 0) ^ 2 / 2 ≤
      N.metric.inner (q 1)
        (manifoldCovDerivAlong N.metric q J 1 1) (J 1) := by
  exact ManifoldJacobi.manifold_jacobi_half_inner_one_lower_bound
    N.connection hI hq hJ hsub hjac hK hc hcr hJ0

end PoincareMT

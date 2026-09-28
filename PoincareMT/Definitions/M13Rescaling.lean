import PoincareMT.Statements.M13DomainTransport
import PoincareMT.Statements.M13BackwardEndpoints
import PoincareMT.Statements.M13ScaleBounds

/-!
# Complete constructed parabolic rescaling

Morgan-Tian Definition 3.40, p. 61, with actual compatible domains from
Definitions 3.38 and 3.41, pp. 61-62. All fields refer to one selected
constructed rescaling. Existence of this record is the full M13 theorem's
conclusion, and no definition obtains it from an admitted theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- One actual rescaling and all its metric, differential and domain identities. -/
structure GeneralizedParabolicRescaling {n : ℕ} {X : Type u} [TopologicalSpace X]
    {A : AdaptedMetricAtlas n X} (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  geometry : ParabolicSpacetimeRescaling R Q hQ a
  horizontal : ParabolicHorizontalCalculus geometry
  backwardEndpoints : ParabolicBackwardEndpointCalculus geometry
  bounds : ParabolicScaleBounds geometry
  domains : ParabolicDomainTransport.{u, u} geometry
  domain_calculus : ParabolicDomainCalculus domains
  coordinateDomains : ParabolicDomainTransport.{u, 0} geometry
  coordinate_domain_calculus : ParabolicDomainCalculus coordinateDomains
  ball_neighborhoods : ∀ (t : ℝ) (p : (R.slices t).Point) (r : ℝ), 0 < r →
    ∀ K : SpacetimeInterval, Nonempty (ParabolicBallNeighborhoodTransport geometry t p r K)

end PoincareMT

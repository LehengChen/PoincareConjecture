import PoincareMT.Statements.M15Noncollapsing

/-!
# The configuration-provider consequence of Theorem 8.1

Apply one uniform Theorem 8.1 constant to each configuration supplied on a
region. The radius, terminal ball, and calibrated measure are exactly those
tested by the noncollapse predicate. Source: Morgan-Tian Theorem 8.1, p. 169,
and the provider formulation in `reviews/contracts/M15-repair-contract.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.Proofs.M15

/-- A configuration provider transports the fixed uniform constant to the
actual ball-volume predicate. Source: Theorem 8.1, p. 169. -/
theorem provider_implies_noncollapse {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I) (Omega : Set G.Point)
    (taubar l₀ V r₀ : ℝ) (U : M15GeneralizedUniformData.{u} n taubar l₀ V) :
    M15ProviderImpliesNoncollapse G Omega taubar l₀ V r₀ U.kappa U := by
  intro provider
  refine ⟨rfl, ?_⟩
  intro p hp r hr hr₀ x hx K C _ _ _ _ _ B
  obtain ⟨E, ⟨D⟩⟩ := provider.provide p hp r hr hr₀ x hx K C B
  exact U.estimate X time I G (G.spacetime.timeFunction p) x E r K C B D

end PoincareMT.Proofs.M15

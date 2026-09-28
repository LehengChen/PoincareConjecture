import PoincareMT.Definitions.M15Noncollapsing
import PoincareMT.Statements.M14GeneralizedLGeometry
import PoincareMT.Statements.M12GeneralizedEquation
import PoincareMT.Statements.M13Rescaling
import PoincareMT.Statements.Ch04.CurvatureTheory

/-!
# M15 generalized and compact noncollapsing theorem

Morgan--Tian Theorems 8.1 and 8.10, pp. 169-177.  The generalized clause
uses the actual M11/M12 spacetime and M14 stable exponential configurations;
the compact clause has its own three-dimensional constants and valid-time
hypotheses.  The two branches do not share `omega` or `T₀`, and no legacy
fixed-carrier noncollapsing assertion is used as a predecessor.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

/-! Theorem 8.1's uniform generalized conclusion and its explicit provider
bridge. Predecessor services are arguments of the numbered theorem; its
output records only properties of the supplied geometric configurations. -/
structure GeneralizedNoncollapsingConclusion (n : ℕ) : Prop where
  uniform : M15GeneralizedUniformTheorem.{u} n
  provider_bridge :
    ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval)
      (G : GeneralizedLGeometryTransport n X time I)
      (Omega : Set G.Point)
      (taubar l₀ V r₀ : ℝ)
      (U : M15GeneralizedUniformData.{u} n taubar l₀ V),
      M15ProviderImpliesNoncollapse G Omega taubar l₀ V r₀ U.kappa U

/-! The separate compact branch of Theorem 8.10. -/
structure CompactNoncollapsingConclusion : Prop where
  compact : M15CompactTheorem810.{u}

/-! Combined M15 output with independent generalized and compact constants. -/
structure NoncollapsingConclusion (n : ℕ) : Prop where
  generalized : GeneralizedNoncollapsingConclusion.{u} n
  compact : CompactNoncollapsingConclusion.{u}

end PoincareMT

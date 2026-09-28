import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.M13Rescaling

/-!
# M44's analytic predecessor services

M44 applies the actual curvature-calculus service from M04 and the ordinary
parabolic-rescaling service from M13 on the physical Type-`u` carriers of an
observed surgery flow. The cap-persistence theorem owns the compactness,
stopping, and limit construction; this record names only the two reusable
analytic services it genuinely invokes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure M44CapPersistencePredecessors : Prop where
  curvature : RicciFlowCurvatureTheory.{u}
  ordinary_flow : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    Nonempty (OrdinaryParabolicRescaling F Q hQ a)

end PoincareMT

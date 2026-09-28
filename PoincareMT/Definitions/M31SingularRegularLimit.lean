import PoincareMT.Definitions.Ch11.SingularLimits

/-!
# M31 repaired singular-time regular-limit data

The source-aligned conclusion is the complete `SingularLimitConclusion` from
Chapter 11. Reusing that record retains the actual old-time gluing map,
terminal slice, proper scalar curvature, end controls, and canonical
neighborhood output; in particular, an empty regular-limit set remains
allowed. The terminal accuracy is `terminalAccuracyFactor * H.epsilon`, not
the printed `2 * H.epsilon` (see `terminalAccuracyFactor`).
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

/-- Terminal regular-limit output for one singular-time assumption. This is
the complete source record, including the gluing compatibility that connects
the terminal source map to the preterminal flow. -/
abbrev RepairedSingularRegularLimitData
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions F T M) := SingularLimitConclusion H

end PoincareMT

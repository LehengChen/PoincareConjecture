import PoincareMT.Definitions.M52GlobalFlow
import PoincareMT.Definitions.M74ConnectedSumReduction

/-!
# M75 smooth endpoint composition

The producer boundary contains the actual normalized initial metric, the
changing-carrier flow returned by M52, and the M74 reduction of that flow's
time-zero carrier.  No endpoint proposition or original-to-sphere map is an
input: the endpoint map is the composition constructed by M75.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

structure M75EndpointInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] (N : NormalizedInitialMetric (M := M)) where
  global : RepairedGlobalFlowData N
  reduction : Nonempty (M74ReductionConclusion (global.certificate.flow.slice 0))

end PoincareMT

import PoincareMT.Definitions.M75SmoothPoincare
import PoincareMT.Proofs.M71.TerminalEvent
import PoincareMT.Proofs.M72.Providers
import PoincareMT.Proofs.M74.Providers

/-!
# M75 endpoint input from extinction of the actual flow

The global flow, its raw M38 topology data and its M71 extinction conclusion
construct the M72 input. Apply M72, M73 and M74 to obtain the initial-slice
reduction required by the checked M75 composition. Extinction remains an
explicit predecessor; no sphere identification is assumed by this provider.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

theorem m75EndpointInputFromExtinction
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (E : FiniteExtinctionConclusion G.certificate.flow) :
    ∃ I : M75EndpointInput N, I.global = G := by
  let I := m72ReconstructionInputFromRaw G L E isConnected_univ
  exact ⟨{ global := G, reduction := m74Reduction_from_M72_M73 I }, rfl⟩

/-- Any actual empty observation suffices: M71's checked terminal helper
selects the first empty surgery, after which M72--M74 give the reduction of
this exact flow. Producing the empty observation remains the extinction task. -/
theorem m75EndpointInputFromEmpty
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (T : ℝ) (hT : T ∈ G.certificate.flow.time_domain)
    (hempty : IsEmpty (G.certificate.flow.slice T).carrier) :
    ∃ I : M75EndpointInput N, I.global = G := by
  obtain ⟨E, _hET, _hearlier⟩ := m71FirstEmptySurgery G.certificate T hT hempty
  exact m75EndpointInputFromExtinction G L E

end PoincareMT

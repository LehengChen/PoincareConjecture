import PoincareMT.Proofs.M01
import PoincareMT.Proofs.M15.Providers
import PoincareMT.Proofs.M25
import PoincareMT.Proofs.M28
import PoincareMT.Proofs.M31
import PoincareMT.Proofs.M32.Providers
import PoincareMT.Proofs.M33.Providers
import PoincareMT.Proofs.M34
import PoincareMT.Proofs.M35.Providers
import PoincareMT.Proofs.M36
import PoincareMT.Proofs.M38
import PoincareMT.Proofs.M39
import PoincareMT.Proofs.M40
import PoincareMT.Proofs.M43
import PoincareMT.Proofs.M44
import PoincareMT.Proofs.M44.Providers
import PoincareMT.Proofs.M45.Providers
import PoincareMT.Proofs.M46.Providers
import PoincareMT.Proofs.M47.Providers
import PoincareMT.Proofs.M48
import PoincareMT.Proofs.M49
import PoincareMT.Proofs.M50
import PoincareMT.Proofs.M51
import PoincareMT.Proofs.M52
import PoincareMT.Proofs.M53
import PoincareMT.Proofs.M54
import PoincareMT.Proofs.M55
import PoincareMT.Proofs.M56
import PoincareMT.Proofs.M57
import PoincareMT.Proofs.M58
import PoincareMT.Proofs.M59.Providers
import PoincareMT.Proofs.M61
import PoincareMT.Proofs.M66
import PoincareMT.Proofs.M67
import PoincareMT.Proofs.M68
import PoincareMT.Proofs.M69
import PoincareMT.Proofs.M71.Assembly
import PoincareMT.Proofs.M75
import PoincareMT.Proofs.M75.Providers
import PoincareMT.Proofs.M76
import PoincareMT.Proofs.M77
import PoincareMT.Proofs.M78
import PoincareMT.Proofs.M79
import PoincareMT.Proofs.M80
import PoincareMT.Proofs.M83

/-!
# Actual milestone suppliers for the two endpoints

All services are supplied inside checked theorem proofs. The original
manifold, chosen normalized metric, calibrated flow, event topology and
extinction conclusion stay fixed through reconstruction. No endpoint service,
sphere identification or projective-plane exclusion is an input.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- On each compact Hausdorff second-countable simply connected smooth
three-manifold with its Borel measurable structure, the actual milestones
supply a normalized metric, one global flow and the reduction of that flow's
initial slice required by M75. M01 supplies the metric; M02/M83 exclude a
two-sided projective plane; M71 supplies extinction on the calibrated flow;
M72--M74 reconstruct and reduce the same flow through the checked M75 adapter.

Sources: Morgan--Tian Theorem 0.3 footnote 2, p. xii; Theorem 15.9 and
Corollary 15.10, pp. 363-364; Theorem 18.1, p. 415; Corollary 15.4(2),
pp. 358-359. This is checked assembly with no additional admission. -/
theorem m90SmoothEndpointInputs
    (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ N : NormalizedInitialMetric (M := M), Nonempty (M75EndpointInput N) := by
  classical
  obtain ⟨N0⟩ := existsNormalizedInitialMetric (M := M)
  let A25 : RepairedNeckCapTopologyTheory.{u} := Classical.choice m25NeckCapTopology
  let P48 : M48Predecessors.{u} :=
    { m11 := generalizedSpacetimeGeometry 3
      m12 := generalizedRicciGaugeGeometry_from_M03_M04_M11 3
      m13 := generalizedParabolicRescaling_from_M12 3
      m31 := m31SingularRegularLimitTheory
      m32 := m32HornSelectionFromMilestones
      m33 := m33BranchContinuationFromMilestones
      m36 := repairedMetricSurgery
      m43 := repairedUnifiedContinuation }
  let hM59 := m59LoopClassesAndComponentTopology_from_predecessors.{u}
  let hM61 := m61Widths (Classical.choose hM59) m60AreaAndFilling_from_predecessors
  let hM64 := m64AnnulusComparison_from_predecessors.{u}
  let hM65 := m65LoopFamilyDeformation hM61.toM61RawWidthCore hM64
  let hM66 := m66SmoothTimeWidthComparison hM61.toM61RawWidthCore
    repairedShortLoopTriviality hM65
  obtain ⟨G, L, ⟨E⟩⟩ :=
    m71ExtinctionFromCalibratedTheories A25 rawLocalSurgeryTopology
      repairedComparisonMap repairedComparisonHomotopy m59ClosedTopologyProvider_from_M02
      repairedGlobalFlow (m28BoundedDistance ⟨ricciFlowCurvatureTheory, ⟨A25⟩⟩)
      repairedStandardCapExistence m35StandardCapUniquenessFromMilestones
      repairedMetricSurgery m44CapPersistenceFromMilestones
      (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized
      repairedUnifiedContinuation m45ControlledSchedulesTheoryFromMilestones
      m46NoncollapseInductionFromMilestones m47CanonicalInductionFromMilestones
      repairedEpochExtension P48
      repairedVolumeLoss repairedFinitePrefix repairedGlobalSchedule
      repairedSphereSeparation repairedGroupEffects repairedChildComponents repairedFiniteAncestry
      repairedAncestryTransport hM59 hM61 hM64 hM65 repairedShortLoopTriviality hM66
      m67SurgeryWidthTheory m68ScalarClockTheory m69FinitePiecePropagation N0.data
      (m83NoProjectivePlaneFromMilestones (M := M))
  obtain ⟨I, _hI⟩ := m75EndpointInputFromExtinction G L E
  exact ⟨N0.data, ⟨I⟩⟩

/-- The actual M75 input producer proves smooth Poincare. M76--M79 then
transport that result through a compatible smooth model of each original
topological manifold; M80 packages both unchanged endpoint propositions.
Sources: Morgan--Tian Corollary 0.2(a), with Hamilton Theorem 2(1), p. 64,
and Cairns Theorem III, p. 797, through M76's reviewed smoothing contract.
All inputs are supplied milestone results; this theorem has no new admission. -/
theorem m90EndpointPackageFromMilestones : Nonempty (M80EndpointConclusion.{u}) := by
  have hSmooth : SmoothPoincare.{u} := m75SmoothPoincare m90SmoothEndpointInputs
  have hTopological : TopologicalPoincare.{u} :=
    m79TopologicalPoincare m76CompatibleSmoothing m77TransportTopologicalHypotheses
      hSmooth m78EndpointTransport
  exact m80EndpointAssembly hSmooth hTopological

end PoincareMT

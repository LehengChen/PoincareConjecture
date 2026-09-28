import PoincareMT.Statements.Ch05.Compactness
import PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier

/-! Compatibility bridge to Mapher's frozen M07 statement declarations. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

namespace FlowCarrier

/- The extended metric induced by a slice, exposed as a value so that
completeness-transfer lemmas can quantify over a family of slices. -/
noncomputable def metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    EMetricSpace C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier

theorem preconnected_metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    @PreconnectedSpace C.carrier
      (C.metricEMetricSpace g).toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : EMetricSpace C.carrier := C.metricEMetricSpace g
  change @PreconnectedSpace C.carrier C.topologicalSpace
  exact ⟨C.connected.isPreconnected⟩

end FlowCarrier

end PoincareMT

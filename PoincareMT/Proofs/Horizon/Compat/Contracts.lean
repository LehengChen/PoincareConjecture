import PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier
import PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence
import PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed
import PoincareMT.Definitions.Ch05.Compactness
import PoincareMT.Statements.Ch05.Compactness
import PoincareMT.Definitions.Ch01.Normalization

/-! Deduplicated bridge for the Horizon snapshot module
`Compat.Contracts`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier`
`PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence`
`PoincareMT.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/


/-!
# Contract-side supplements for the Horizon closure

The Horizon snapshot's own carrier, pointed-compactness and normalization
modules carried a few derived declarations that the generated compatibility
bridges (which re-export the frozen `Definitions`/`Statements` modules) do not
provide. This module supplies exactly those declarations, proved from the
frozen contract without changing it:

* `FlowCarrier.metricEMetricSpace`: the extended-metric structure of a slice
  metric, the same instance that `FlowCarrier.metricComplete` uses;
* `FlowCarrier.preconnected_metricEMetricSpace`: that structure's topology is
  the carrier topology, which is connected;
* `FlowCarrier.subsingleton_zero`: a connected zero-dimensional carrier is a point;
* `PointedRicciFlowCompactnessHypotheses.all_time_curvature_control_on_zero_ball`:
  the time-zero-ball specialisation of `all_time_curvature_control`;
* `normalizedMetricVolume_eq_smul_hausdorffVolume`: the definition of the
  normalized volume as a rewrite lemma.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The normalized volume is the calibrated Hausdorff volume, by definition. -/
theorem normalizedMetricVolume_eq_smul_hausdorffVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M]
    [BorelSpace M] [T3Space M] (g : RiemannianMetric 3 M) :
    normalizedMetricVolume g = euclideanHausdorffCalibration • g.hausdorffVolume :=
  rfl

end PoincareMT

import PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Covering
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.LocalBall
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareMT.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite

/-! Deduplicated bridge for the Horizon snapshot module
`Geometry.Riemannian.Measure.Balls`.
Its constants already exist on main in
`PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Covering`
so that module is imported instead of a copy; see
`docs/progress/2026-09-20-horizon-duplicate-modules.json`. -/

/-!
# Positive finite volumes of intrinsic balls

Local coordinate comparison gives positive volume to every positive-radius
ball. Completeness makes its volume finite, by compactness of closed balls.
These are the measure inputs to heat-kernel averaging and Gaussian moments.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Complete intrinsic balls of finite radius have finite retained volume. -/
theorem volumeMeasure_ball_lt_top (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) (r : ℝ) :
    g.volumeMeasure (g.ball p r) < ⊤ := by
  apply (measure_mono (show g.ball p r ⊆ {q | g.edist p q ≤ ENNReal.ofReal r}
    from fun q hq => (show g.edist p q < ENNReal.ofReal r from hq).le)).trans_lt
  exact g.volumeMeasure_lt_top_of_isCompact (g.isCompact_closedBall_of_metricComplete hcomplete p r)

end PoincareMT.RiemannianMetric

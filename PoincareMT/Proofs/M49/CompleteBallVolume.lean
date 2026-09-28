import PoincareMT.Proofs.M49.CalibratedVolume
import PoincareMT.Proofs.M09.RiemannianProper

/-!
# Finite actual volume of balls in complete connected manifolds

The standard model balls in Morgan-Tian Theorem 13.2, p. 333,
and Lemma 17.12, p. 410, have finite calibrated volume. M09's
properness theorem retains the specified Riemannian metric exactly.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M49

/-- Complete connected model balls have finite actual calibrated volume,
as used in MT Theorem 13.2, p. 333, and Lemma 17.12, p. 410. -/
theorem calibratedMetricVolume_ball_lt_top {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (r : ℝ) :
    calibratedMetricVolume g (g.ball p r) < ⊤ := by
  exact (measure_mono subset_closure).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact g
      (Proofs.M09.isCompact_closure_metric_ball g hc p r))

end PoincareMT.M49

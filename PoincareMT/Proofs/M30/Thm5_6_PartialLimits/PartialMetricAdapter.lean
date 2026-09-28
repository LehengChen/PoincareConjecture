import PoincareMT.Proofs.M30.Thm5_6_PartialLimits.MetricConvergence
import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence

/-!
# Retaining partial metric limits across the lower interface

The M30 and M28 records have identical geometric fields. These constructors
retain the actual carrier, metric, maps and jets without a new extraction
(Morgan--Tian Theorem 5.6, pp. 85--87).
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M30.PartialPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}

/-- The promoted lower record retains every field of the owned partial
metric limit (Theorem 5.6, pp. 85--87). -/
def toM28 (G : PartialPointedMetricConvergence g p A) :
    M28.PartialPointedMetricConvergence g p A where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  base_in_exhaustion := G.base_in_exhaustion
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_step := G.exhaustion_step
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_preserving := G.base_preserving
  metric_jets := G.metric_jets
  boundary_control := G.boundary_control

/-- A promoted lower partial metric limit supplies the identical owned
record (Theorem 5.6, pp. 85--87). -/
def ofM28 (G : M28.PartialPointedMetricConvergence g p A) :
    PartialPointedMetricConvergence g p A where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  base_in_exhaustion := G.base_in_exhaustion
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_step := G.exhaustion_step
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_preserving := G.base_preserving
  metric_jets := G.metric_jets
  boundary_control := G.boundary_control

end PoincareMT.M30.PartialPointedMetricConvergence

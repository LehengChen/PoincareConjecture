import PoincareMT.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence
import PoincareMT.Proofs.M28.Mathlib.WithinConvergenceBounds

/-!
# Initial coordinate bounds from an actual partial metric limit

`PartialPointedMetricConvergence.metric_jets` is the actual compact-uniform
convergence statement for the source embeddings.  This file extracts the
finite bound needed at the initial time of the parabolic estimates.  The
chart, compact set, and source maps remain those supplied by that record.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

variable {n : ℕ} {M : ℕ → Type u}
  [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}

private theorem limit_chart_coefficients_continuousOn
    (G : PartialPointedMetricConvergence g p A)
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK :
      letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      K ⊆ (extChartAt (𝓡 n) q).target) (m : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ContinuousOn
      (iteratedFDeriv ℝ m
        (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 n) q).symm)) K := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  intro z hz
  exact ((G.limitMetric.contDiffOn_chartCoefficients q).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hK hz))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top) |>.continuousWithinAt

/-- The actual source metric coefficients have one eventual finite bound on
any compact subset of a fixed limit chart.  The bound is selected after the
chart compact but before the source index is tested.
-/
theorem PartialPointedMetricConvergence.exists_eventual_initial_chart_jet_bound
    (G : PartialPointedMetricConvergence g p A)
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K)
    (hKtarget :
      letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      K ⊆ (extChartAt (𝓡 n) q).target)
    (m : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ j in atTop, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m
        ((g (G.subsequence j)).pullbackCoefficients
          (G.embedding j ∘ (extChartAt (𝓡 n) q).symm)) z‖ ≤ C := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  exact (G.metric_jets q m K hK hKtarget).exists_eventual_norm_bound hK
    (limit_chart_coefficients_continuousOn G q hKtarget m)

end PoincareMT.M28

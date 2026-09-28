import PoincareMT.Statements.Ch04.CurvatureTheory
import PoincareMT.Statements.M12GeneralizedEquation
import PoincareMT.Definitions.M14GeneralizedLGeometry

/-!
# Metric comparison on the actual compatible cylinder

Lemma 16.15, pp. 379-381. M12 realizes the selected compatible cylinder
as an ordinary Ricci flow with its same metric representative. Its
actual curvature norm is the horizontal curvature norm, so M04's
comparison has the full-tensor coefficient 6 in dimension three.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M46

/-- The actual tested-cylinder metric has the same curvature-based
comparison as its genuine ordinary-flow realization. Source:
Lemma 3.15 and Lemma 16.15, pp. 42 and 379-381. -/
theorem compatibleCylinder_metric_comparison
    {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport 3 X time I)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C] [IsManifold (𝓡 3) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C)
    (M : SpacetimeCylinderMetric e) {s t bound : ℝ}
    (hs : s ∈ K.domain) (ht : t ∈ K.domain) (hst : s ≤ t) (hbound : 0 ≤ bound)
    (hcurvature : ∀ r : (G.timeIntervals.interval K).Point, r.val ∈ Icc s t →
      ∀ z : C, horizontalCurvatureNorm G.leafwise (e.toSpacetime (r, z)) ≤ bound)
    (z : C) (v : TangentSpace (𝓡 3) z) :
    Real.exp (-6 * bound * (t - s)) * (M.metric s).inner z v v ≤
        (M.metric t).inner z v v ∧
      (M.metric t).inner z v v ≤
        Real.exp (6 * bound * (t - s)) * (M.metric s).inner z v v := by
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨W⟩ := H.compatible_ordinary C K e M (fun p _ => G.ricciEquation p)
  let geometry : MovingSpacetimeGaugeGeometry e.toMovingSpacetimeGauge := {
    metric := W.flow.metric
    smooth := by rw [W.metric_eq]; exact M.smooth
    spatialTangentEquiv := M.spatialTangentEquiv
    spatialTangentEquiv_eq := M.spatialTangentEquiv_eq
    metric_eq := W.metric_pullback }
  have calculus := H.moving_calculus C K e.toMovingSpacetimeGauge geometry W.flow.connection
  have hordinary : ∀ r ∈ Icc s t, ∀ y : C,
      (W.flow.connection r).curvatureTensorNorm y ≤ bound := by
    intro r hr y
    have hrK : r ∈ K.domain := K.ordConnected.out hs ht hr
    exact (calculus.curvature_norm_eq ⟨r, hrK⟩ y).trans_le (hcurvature ⟨r, hrK⟩ hr y)
  have hcomparison := hM04.metric_comparison 3 C K.domain W.flow s t bound hs ht hst
    hbound hordinary z v
  rw [W.metric_eq] at hcomparison
  norm_num only [Nat.cast_ofNat] at hcomparison
  exact hcomparison

end PoincareMT.Proofs.M46

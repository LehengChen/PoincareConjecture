import PoincareMT.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_CylinderMetric

/-!
# The factor-two metric bound in the initial safe cylinder

Lemma 16.15, pp. 379-381. The actual full-tensor Ricci contraction
has coefficient 6. The time allowance rho^2*log(2)/8 therefore keeps
the terminal metric below twice every earlier cylinder metric.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M46

/-- The corrected initial time allowance gives the physical
factor-two lower metric comparison. Source: Lemma 3.15 and
Lemma 16.15, pp. 42 and 379-381. -/
theorem compatibleCylinder_half_terminalMetric_le
    {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport 3 X time I)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C] [IsManifold (𝓡 3) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C)
    (M : SpacetimeCylinderMetric e) {s T rho : ℝ}
    (hs : s ∈ K.domain) (hT : T ∈ K.domain) (hst : s ≤ T) (hrho : 0 < rho)
    (hduration : T - s ≤ rho ^ 2 * Real.log 2 / 8)
    (hcurvature : ∀ r : (G.timeIntervals.interval K).Point, r.val ∈ Icc s T →
      ∀ z : C, horizontalCurvatureNorm G.leafwise (e.toSpacetime (r, z)) ≤ rho⁻¹ ^ 2)
    (z : C) (v : TangentSpace (𝓡 3) z) :
    (1 / 2 : ℝ) * (M.metric T).inner z v v ≤ (M.metric s).inner z v v := by
  have hmetric := (compatibleCylinder_metric_comparison G hM04 hM12 K e M
    hs hT hst (sq_nonneg (rho⁻¹)) hcurvature z v).2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexponent : 6 * rho⁻¹ ^ 2 * (T - s) ≤ Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hduration
      (by positivity : 0 ≤ 6 * rho⁻¹ ^ 2)
    have hcancel : 6 * rho⁻¹ ^ 2 * (rho ^ 2 * Real.log 2 / 8) =
        (3 / 4 : ℝ) * Real.log 2 := by
      field_simp [hrho.ne']
      ring
    rw [hcancel] at h
    exact h.trans (by nlinarith)
  have hexp : Real.exp (6 * rho⁻¹ ^ 2 * (T - s)) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_le_exp.mpr hexponent
  have hnonneg : 0 ≤ (M.metric s).inner z v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((M.metric s).pos z v hv).le
  have hupper := hmetric.trans (mul_le_mul_of_nonneg_right hexp hnonneg)
  linarith

end PoincareMT.Proofs.M46

import PoincareMT.Proofs.M63.Sec19_3_Ramps.Cor19_13_DegreePreservation
import PoincareMT.Proofs.M63.Sec19_3_Ramps.Lemma19_14_RatioBound

/-!
# Ramp-preservation package for an existing smooth solution

Assemble Corollary 19.13 and the corrected estimates of Lemma 19.14,
MT2007 pp. 446-447 and MT2015Correction pp. 8-9, in the exact frozen record.
This retains an existing M62 curve and does not assert existence or general
C2-label transport. The three checked derivations are the 2026-09-21
smooth-slope, smooth-ratio and positive-degree records under tasks/M63.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- An existing smooth ramp solution satisfies every field of the frozen
preservation record, including its supplied winding degree and the corrected
forcing. Corollary 19.13 and Lemma 19.14, MT2007 pp. 446-447, with
MT2015Correction pp. 8-9. -/
theorem m63SmoothRampPreservation
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M62CurveEstimates P.flow c K0 K1 K2)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    M63RampPreservation P c b K0 K1 K2 := by
  have hpositive := m63SmoothRamp_preserved P c hc hBounds hramp
  have hu : ∀ t ∈ Set.Icc a b, ∀ x, 0 < m62Slope P c t x :=
    fun t ht => (m63IsRampAt_slice_iff P c t).mp (hpositive t ht)
  exact {
    positive := hpositive
    lower_slope := fun _ hm hinit => m63SmoothSlope_lower P c hc hBounds hm.le hinit
    degree_preserved := fun L _ ht => m63PositiveDegree_preserved P c hc.continuous
      hc.periodic hc.spatial_regular hpositive L ht
    ratio_time := fun _ hε _ ht x => m63RampRatio_differentiableAt_time P c hc hu hε ht x
    ratio_evolution := fun _ hε _ ht x =>
      m63SmoothRampRatio_evolution P c hc hBounds hE hu hε ht x
    ratio_bound := fun _ _ hm _ hinit hR =>
      m63SmoothRampRatio_bound P c hc h0 h1 h2 hBounds hE hm hinit hR
    curvature_bound := fun _ _ hm _ hinit hR =>
      m63SmoothRampCurvature_bound P c hc h0 h1 h2 hBounds hE hm hinit hR }

end PoincareMT

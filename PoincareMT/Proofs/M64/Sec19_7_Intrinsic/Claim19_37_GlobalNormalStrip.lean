import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableNormalStrip
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import Mathlib.Topology.Order.Compact

/-!
# The actual global measurable normal strip

The uniform first-contact construction is initially stated only at boundary
parameters whose geodesic curvature is below a supplied threshold. Since the
curvature is continuous on one compact period, one finite threshold works for
every parameter. This theorem closes that quantifier without adding any
injectivity or no-return premise.

Morgan--Tian context: Claim 19.37, printed pp. 468-469, in the proof of Proposition
19.35. This module supplies actual normal-geodesic data or its coordinate and measure
transport.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- A uniform measurable normal map and first-contact height exist for every boundary
parameter, with the metric lower bound and differential regularity available through each
selected height. The map is the actual normal exponential produced by the lower Claim 19.37
chain; this theorem only closes the compact-period curvature threshold. Source/construction:
Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_exists_global_measurable_normal_strip
    (K : ℝ) {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
      ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
        ∃ (u : ℝ × ℝ → AnnulusCoordinates) (height : ℝ → ℝ),
          ContDiff ℝ ∞ u ∧ Measurable height ∧
          (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
          (∀ s, 0 < height s ∧ height s ≤ R ∧
            (∀ t ∈ Ioo (0 : ℝ) (height s),
              1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
            u (s, height s) ∈ standardAnnulusDomain ∧
            (height s = R ∨ ‖u (s, height s)‖ = 1 ∨
              ‖u (s, height s)‖ = 2)) ∧
          ∀ a ∈ Icc (0 : ℝ) rampPeriod, ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧
            Icc (0 : ℝ) (height a) ⊆ I ∧
            (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) ∧
            ∀ t ∈ Icc (0 : ℝ) (height a),
              (∀ v : ℝ × ℝ,
                (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                  N.metric.inner (u (a, t))
                    (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
              Function.Injective (fderiv ℝ u (a, t)) ∧
              (1 - delta) ^ 2 * intrinsicBoundarySpeed N.metric 1 a ≤
                N.metric.pullbackVolumeDensity
                  (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] := by
  intro N hK
  let k : ℝ → ℝ :=
    intrinsicGeodesicCurvature N.metric N.connection 1
  have hkcont : Continuous k :=
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))
  have hbound : BddAbove (k '' Icc (0 : ℝ) rampPeriod) :=
    isCompact_Icc.bddAbove_image hkcont.continuousOn
  obtain ⟨A, hA⟩ := hbound
  let alpha := max A 0
  have halpha : 0 ≤ alpha := le_max_right _ _
  have hka (a : ℝ) (ha : a ∈ Icc (0 : ℝ) rampPeriod) : k a ≤ alpha :=
    (hA ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  obtain ⟨R, hR, hRsmall, hstrip⟩ :=
    m64Intrinsic_exists_uniform_measurable_normal_strip K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  obtain ⟨u, height, hu, hheight, hboundary, hcontact, hlocal⟩ := hstrip N hK
  refine ⟨u, height, hu, hheight, hboundary, hcontact, ?_⟩
  intro a ha_period
  obtain ⟨S, I, hS, hI, ha, hsub, hgeo, hmetric⟩ := hlocal a
    (show intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha from by
      simpa [k] using hka a ha_period)
  exact ⟨S, I, hS, hI, ha, hsub, hgeo, hmetric⟩

end PoincareMT

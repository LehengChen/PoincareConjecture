import PoincareMT.Proofs.M07.Geometry.Riemannian.Distance.NormalBall
import PoincareMT.Statements.M64Comparison

/-!
# Proposition 19.35: local exponential primitives

The intrinsic annulus carries a genuine smooth metric on the whole plane.
This file exports the lower-milestone Gauss exponential chart and exact
tangent-ball distance identity at the inner boundary point.  The results are
the chart primitives used by the polar/Jacobi stage; no global comparison or
minimal-annulus assertion is smuggled into this adapter.

Source: Morgan--Tian Proposition 19.35, pp. 467--481, with the local
exponential construction from M07 Section 3.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-! The point at radius one and angle zero is the inner boundary basepoint. -/

/-- The literal inner-boundary point at radius one and angular parameter zero. Source: M07
Section 3.4 exponential chart and tangent-ball distance services;
`reports/2026-09-23-intrinsic-assembly.md`. -/
noncomputable def m64IntrinsicBasePoint : AnnulusCoordinates :=
  intrinsicAnnulusBoundary 1 0

/-- M07's smooth local Gauss exponential chart at the intrinsic inner boundary point. The
displayed chart retains the exact metric pairing identity needed for radial Jacobi
comparison. Source: M07 Section 3.4 exponential chart and tangent-ball distance services;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_exists_exponential_chart_gauss (N : IntrinsicAnnulus) :
    let E := EuclideanSpace ℝ (Fin 2)
    let p := m64IntrinsicBasePoint
    let c := extChartAt (𝓡 2) p
    let B := N.metric.pullbackCoefficients c.symm
    ∃ e : OpenPartialHomeomorph E AnnulusCoordinates,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ v ∈ e.source, ∀ w : E,
        N.metric.inner (e v)
          (mfderiv (𝓡 2) (𝓡 2) e v v)
          (mfderiv (𝓡 2) (𝓡 2) e v w) =
            N.metric.inner p v w) ∧
      (∃ r : ℝ, 0 < r ∧
        {v : E | N.metric.tangentNorm p v < r} ⊆ e.source) ∧
      ∃ Γ : E × ℝ → E × E,
        ContDiffOn ℝ ∞ Γ (e.source ×ˢ Ioo (-2 : ℝ) 2) ∧
        ∀ v ∈ e.source,
          Γ (v, 0) = (c p, v) ∧
          c.symm (Γ (v, 1)).1 = e v ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Γ (v, t)).1 ∈ c.target ∧
            HasDerivAt (fun s => Γ (v, s))
              (coordinateGeodesicField B (Γ (v, t))) t := by
  simpa only [m64IntrinsicBasePoint] using
    (RiemannianMetric.exists_exponential_chart_gauss
      (n := 2) (M := AnnulusCoordinates) N.metric
      (intrinsicAnnulusBoundary 1 0))

/-- The inner-boundary chart contains a positive tangent ball on which the intrinsic
distance from the basepoint is exactly the tangent radius. Source: M07 Section 3.4
exponential chart and tangent-ball distance services;
`reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_exists_tangentBall_edist_eq (N : IntrinsicAnnulus) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) AnnulusCoordinates,
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ e.source ∧
      e 0 = m64IntrinsicBasePoint ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin 2),
        N.metric.inner (e v)
          (mfderiv (𝓡 2) (𝓡 2) e v v)
          (mfderiv (𝓡 2) (𝓡 2) e v w) =
            N.metric.inner m64IntrinsicBasePoint v w) ∧
      ∃ r : ℝ, 0 < r ∧
        (∀ v, N.metric.tangentNorm m64IntrinsicBasePoint v < r →
          N.metric.edist m64IntrinsicBasePoint (e v) =
            ENNReal.ofReal (N.metric.tangentNorm m64IntrinsicBasePoint v)) := by
  obtain ⟨e, h0, he0, he, he', hgauss, hball, _⟩ :=
    RiemannianMetric.exists_exponential_chart_gauss
      (n := 2) (M := AnnulusCoordinates) N.metric
      (intrinsicAnnulusBoundary 1 0)
  obtain ⟨r, hr, hsource, hedist⟩ :=
    RiemannianMetric.exists_tangentBall_edist_eq_of_gauss
      (n := 2) (M := AnnulusCoordinates) N.metric
      (intrinsicAnnulusBoundary 1 0) e h0 he0 he he' hgauss
  refine ⟨e, h0, he0, he, he', hgauss, r, hr, ?_⟩
  intro v hv
  exact hedist v hv

end PoincareMT

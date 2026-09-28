import PoincareMT.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RayComparison
import PoincareMT.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareMT.Statements.M64Comparison

/-!
# Proposition 19.35: polar-wedge density comparison

The M07 polar comparison is stated in arbitrary dimension and in terms of a
Ricci lower bound.  This adapter specializes it to the two-dimensional
intrinsic annulus and keeps every radial-chart and nonsingularity obligation
explicit.  The public M64 hypothesis is a Gaussian upper bound; it does not
silently supply the Ricci lower bound required by this analytic comparison.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481; actual intrinsic
boundary, scalar comparison or endpoint assembly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

open RiemannianMetric

/-- An absolute curvature-norm estimate at one point gives the signed Ricci lower bound used
by the M07 comparison. This pointwise form is the adapter needed for the precompact
exponential services, whose curvature field is usually stated on a metric ball rather than
on `standardAnnulusDomain`. Source: M07 polar ray comparison; the explicit
absolute-curvature adapter is recorded in `reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_ricci_lower_at_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (p : AnnulusCoordinates)
    (hcurv : N.connection.curvatureTensorNorm p ≤ K)
    (v : TangentSpace (𝓡 2) p) :
    -((1 : ℝ) * K) * N.metric.inner p v v ≤
      N.connection.ricci p v v := by
  have hsec : ∀ u w : TangentSpace (𝓡 2) p,
      |N.connection.sectionalCurvature p u w| ≤ K := by
    intro u w
    exact (N.connection.abs_sectionalCurvature_le_curvatureTensorNorm p u w).trans hcurv
  have h := N.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
    p K hsec v
  norm_num at h
  simpa only [Nat.cast_one, one_mul, neg_mul] using h

/-- An explicit absolute curvature-norm bound supplies the signed Ricci lower bound required
by the polar comparison. This is a local bridge only: the public Gaussian upper-bound field
does not provide `hcurv`. Source: M07 polar ray comparison; the explicit absolute-curvature
adapter is recorded in `reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_ricci_lower_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ K)
    (p : AnnulusCoordinates) (hp : p ∈ standardAnnulusDomain)
    (v : TangentSpace (𝓡 2) p) :
    -((1 : ℝ) * K) * N.metric.inner p v v ≤
      N.connection.ricci p v v := by
  exact m64Intrinsic_ricci_lower_at_of_curvature_norm N K p (hcurv p hp) v

/-- The pointwise bridge along a radial segment, with curvature supplied on a metric ball as
in M07's precompact exponential data. The radial map-to-ball field remains explicit because
the local exponential need not cover the intrinsic annulus. Source: M07 polar ray
comparison; the explicit absolute-curvature adapter is recorded in
`reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_radial_ricci_lower_of_ball_curvature_norm
    (N : IntrinsicAnnulus) (K R : ℝ)
    (p : AnnulusCoordinates)
    (hcurv : ∀ q ∈ N.metric.ball p R,
      N.connection.curvatureTensorNorm q ≤ K)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {theta : AnnulusCoordinates} {b : ℝ}
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ N.metric.ball p R) :
    ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -((1 : ℕ) : ℝ) * K * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w := by
  intro s hs w
  have hpoint := m64Intrinsic_ricci_lower_at_of_curvature_norm N K
    (e (s • theta)) (hcurv (e (s • theta)) (hmap s hs)) w
  simpa only [Nat.cast_one, one_mul, neg_mul] using hpoint

/-- The same bridge along a radial segment, in the exact binder shape used by the M07 polar
comparison. The map-to-annulus field is explicit because an arbitrary local chart need not
land in `standardAnnulusDomain`. Source: M07 polar ray comparison; the explicit
absolute-curvature adapter is recorded in `reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_radial_ricci_lower_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ K)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {theta : AnnulusCoordinates} {b : ℝ}
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ standardAnnulusDomain) :
    ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -((1 : ℕ) : ℝ) * K * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w := by
  intro s hs w
  have h := m64Intrinsic_ricci_lower_of_curvature_norm N K hcurv
    (e (s • theta)) (hmap s hs) w
  simpa only [Nat.cast_one, one_mul, neg_mul] using h

/-- The two-dimensional M07 polar cross inequality on a regular radial ray. The `hRic` field
is the signed Ricci lower estimate needed by the M07 scalar Jacobi comparison; deriving it
from the annular geometric producer is a separate obligation. Source: M07 polar ray
comparison; the explicit absolute-curvature adapter is recorded in
`reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_polarDensity_cross_le_of_ricci
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U, RiemannianMetric.IsGeodesicOn N.metric
      (fun s : ℝ => e (s • v))
      {s : ℝ | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0)
        (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b kappa : ℝ} (hb : 0 < b) (hkappa : 0 ≤ kappa)
    (hsub : ∀ s ∈ Icc (0 : ℝ) b, s • theta ∈ U)
    (hinj : ∀ s ∈ Icc (0 : ℝ) b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)))
    (hRic : ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -(1 : ℝ) * kappa * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) b)
    (hs : s ∈ Ioo (0 : ℝ) b) (hts : t ≤ s) :
    (s ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (s • theta)) *
        modelS kappa t ^ (1 : ℕ) ≤
      (t ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (t • theta)) *
        modelS kappa s ^ (1 : ℕ) := by
  have hRic' : ∀ u ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (u • theta)),
        -((1 : ℕ) : ℝ) * kappa * N.metric.inner (e (u • theta)) w w ≤
          N.connection.ricci (e (u • theta)) w w := by
    intro u hu w
    simpa only [Nat.cast_one] using hRic u hu w
  exact RiemannianMetric.polarDensity_cross_le_on_regular_ray
    (m := 1) N.metric N.connection one_pos hU h0 he hgeo hmetric theta htheta
    hb hkappa hsub hinj hRic' ht hs hts

/-- The polar comparison with its Ricci field supplied by an absolute curvature-norm bound.
The radial map-to-domain field remains explicit: without it, the norm bound on
`standardAnnulusDomain` cannot be evaluated at the points of the ray. Source: M07 polar ray
comparison; the explicit absolute-curvature adapter is recorded in
`reports/2026-09-24-intrinsic-polar.md`. -/
theorem m64Intrinsic_polarDensity_cross_le_of_curvature_norm
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U, RiemannianMetric.IsGeodesicOn N.metric
      (fun s : ℝ => e (s • v))
      {s : ℝ | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0)
        (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b kappa : ℝ} (hb : 0 < b) (hkappa : 0 ≤ kappa)
    (hsub : ∀ s ∈ Icc (0 : ℝ) b, s • theta ∈ U)
    (hinj : ∀ s ∈ Icc (0 : ℝ) b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)))
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ kappa)
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ standardAnnulusDomain)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) b)
    (hs : s ∈ Ioo (0 : ℝ) b) (hts : t ≤ s) :
    (s ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (s • theta)) *
        modelS kappa t ^ (1 : ℕ) ≤
      (t ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (t • theta)) *
        modelS kappa s ^ (1 : ℕ) := by
  apply m64Intrinsic_polarDensity_cross_le_of_ricci N hU h0 he hgeo hmetric
    theta htheta hb hkappa hsub hinj
  · intro u hu w
    have hric := m64Intrinsic_radial_ricci_lower_of_curvature_norm
      N kappa hcurv hmap u hu w
    simpa only [Nat.cast_one, one_mul] using hric
  · exact ht
  · exact hs
  · exact hts

end PoincareMT

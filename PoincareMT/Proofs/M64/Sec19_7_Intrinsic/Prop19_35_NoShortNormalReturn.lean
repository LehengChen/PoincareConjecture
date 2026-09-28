import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalReturnRegionCurvature
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature

/-!
# Excluding the short boundary arc of a normal return

Morgan--Tian, Lemma 19.46, Case (i), p. 474. An actual annular normal-return
region has Gaussian curvature at least pi/2 minus its inner-arc turning.
The public short-arc hypothesis makes that turning strictly less than
delta. The actual finite coordinate cover gives compactness, and the
one-sided Gaussian bound controls the region by the public annulus area.
These actual estimates contradict the prescribed area threshold.
The boundary arc in this statement is the one bounding the given region;
no exclusion is asserted for a long complementary arc.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- Actual two-arc normal-return geometry cannot enclose a short inner boundary arc when the
public Gaussian, turning, and area bounds have total budget at most pi/2. The Gaussian upper
bound may be any real number, and the actual boundary parameter interval may cross the
angular seam. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-two-arc-region-curvature.md. -/
theorem m64Intrinsic_no_short_normal_return
    {I : Type*} [Finite I] (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (ha0 : deriv alpha 0 ≠ 0)
    (hareg : ∀ p ∈ Ioo (0 : ℝ) A, deriv alpha p ≠ 0)
    (hgeo : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunit : ∀ p ∈ Icc 0 B,
      N.metric.inner (beta p) (deriv beta p) (deriv beta p) = 1)
    (horth : N.metric.inner (alpha 0) (deriv alpha 0) (deriv beta 0) = 0)
    {a b0 : ℝ} (hab : a ≤ b0)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b0))
    (hcircle : alpha '' Icc 0 A = intrinsicAnnulusBoundary 1 '' Icc a b0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcover : (⋃ i, (face i).carrier) = closure U)
    (v0 v1 : Euler.CoordinateVertex F b) (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A)
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hperiod : b0 ≤ a + rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b0 ≤ r) : False := by
  have hcompact : IsCompact (closure U) := by
    rw [← hcover]
    exact isCompact_iUnion fun i => (face i).isCompact_carrier
  have hlower := m64Intrinsic_circle_geodesic_region_curvature_lower_bound N face F b
    hF hFi hsource hcarrier hboundary hinter hfront ha hb hA hB hai hbi hbase hend hmeet
    ha0 hareg hgeo hunit horth hab hcircleInj hcircle hU hV hdisj hfU hfV hclosure
    hVconn hinward hsub hcover v0 v1 hv0 hv1
  have hupper := m64Intrinsic_region_gaussian_integral_le_area N hK hcompact hsub
  have hscaled : max K 0 * intrinsicAnnulusArea N.metric ≤ max K 0 * mu :=
    mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
  have hlocalTurn := hturn a b0 hab hperiod hshort
  linarith only [hlower, hupper, hscaled, hbudget, hlocalTurn]

end PoincareMT

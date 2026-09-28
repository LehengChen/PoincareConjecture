import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalChart
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_Assembly
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import PoincareMT.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaLoss

/-!
# Assembly from a global normal-strip certificate

This is the strict handoff between the geometric producers and the public
Proposition 19.35 consumer.  The certificate keeps the unresolved embedded
strip and focusing-aggregation inputs explicit.  Curvature and area loss are
derived here from the existing M64 lemmas, so they cannot be silently replaced
by a direct witness premise.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481; actual intrinsic
boundary, scalar comparison or endpoint assembly.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- An embedded normal-strip certificate for one annulus. `F` is the genuine open chart on a
strip neighborhood; it avoids imposing injectivity on an all-plane periodic lift.
`focusing_loss_bound` and `remaining_length` are the two aggregate outputs not supplied by
the local Jacobi and chart lemmas. The curvature and area losses are intentionally not
fields: the assembly derives them from the actual boundary and strip data. Source: MT
Proposition 19.35, pp. 480-481; `reports/2026-09-24-global-normal-chart.md`. -/
structure M64IntrinsicGlobalStripCertificate
    (N : IntrinsicAnnulus) (delta r K mu : ℝ) where
  c : ℝ
  radius : ℝ
  c_pos : 0 < c
  radius_pos : 0 < radius
  S : Set ℝ
  height : ℝ → ℝ
  hS : MeasurableSet S
  hheight : Measurable height
  hSsub : S ⊆ Icc (0 : ℝ) rampPeriod
  F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates
  hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source
  hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target
  hsource : {z : AnnulusCoordinates |
      z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ⊆ F.source
  hbound : ∀ x : AnnulusCoordinates, x 0 ∈ S →
    x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
      c ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (F x) (mfderiv (𝓡 2) (𝓡 2) F x v)
          (mfderiv (𝓡 2) (𝓡 2) F x v)
  himage : F '' {z : AnnulusCoordinates |
      z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ⊆ standardAnnulusDomain
  hsmall : intrinsicAnnulusArea N.metric < c ^ 2 * radius * (r / 10)
  focusing_loss : ℝ
  focusing_loss_bound : focusing_loss ≤
    3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50
  remaining_length :
    intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        m64IntrinsicHighCurvatureLength N (100 * delta / r) - focusing_loss -
        m64IntrinsicLongFiberLength N S height radius ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod

private theorem m64Intrinsic_global_strip_area_bound
    {N : IntrinsicAnnulus} {delta r K mu : ℝ}
    (C : M64IntrinsicGlobalStripCertificate N delta r K mu) :
    ENNReal.ofReal (C.c ^ 2) *
        (∫⁻ s in C.S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
          ENNReal.ofReal (C.height s)) ≤
      ENNReal.ofReal (intrinsicAnnulusArea N.metric) := by
  have hspeed : Measurable (intrinsicBoundarySpeed N.metric 1) :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous.measurable
  exact m64Intrinsic_embedded_strip_area_bound N.metric C.F C.hF C.hFinv C.hS
    C.hheight hspeed (c := C.c) C.hsource
    (fun x hx hheight v => C.hbound x hx hheight v) C.himage

private theorem m64Intrinsic_global_strip_area_loss
    {N : IntrinsicAnnulus} {delta r K mu : ℝ}
    (C : M64IntrinsicGlobalStripCertificate N delta r K mu)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod) :
    m64IntrinsicLongFiberLength N C.S C.height C.radius <
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10 := by
  exact m64Intrinsic_long_fiber_length_lt_tenth N C.hS C.hSsub C.hheight
    C.c_pos C.radius_pos hfirst (m64Intrinsic_global_strip_area_bound C) C.hsmall

/-- A global strip certificate produces the public length-loss estimate. The public delta
interval is preserved verbatim; in particular this adapter does not replace the corrected
`delta = 1/200` bookkeeping by a stronger premise. Source: MT Proposition 19.35, pp.
480-481; `reports/2026-09-24-global-normal-chart.md`. -/
theorem m64Intrinsic_length_loss_estimates_of_global_strip_control
    (hcontrol : ∀ delta r K : ℝ, 0 < delta → delta < 1 / 100 → 0 < r →
      ∃ mu : ℝ, 0 < mu ∧
        ∀ N : IntrinsicAnnulus,
          N.GaussianCurvatureBound K →
          r < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
          N.SmallBoundaryTurning delta r →
          intrinsicAnnulusArea N.metric < mu →
          Nonempty (M64IntrinsicGlobalStripCertificate N delta r K mu)) :
    M64IntrinsicLengthLossEstimates := by
  intro delta r K hdelta hdelta_small hr
  obtain ⟨mu, hmu, hN⟩ := hcontrol delta r K hdelta hdelta_small hr
  refine ⟨mu, hmu, ?_⟩
  intro N hcurv hfirst hturn harea
  obtain ⟨C⟩ := hN N hcurv hfirst hturn harea
  have hcurvature := m64Intrinsic_high_curvature_length_lt N hdelta hr hfirst hturn
    (show 100 * delta / r ≤ 100 * delta / r from le_rfl)
  have harea_loss := m64Intrinsic_global_strip_area_loss C hfirst
  have hcurvature_nonneg : 0 ≤
      m64IntrinsicHighCurvatureLength N (100 * delta / r) :=
    m64IntrinsicHighCurvatureLength_nonneg N _
  refine ⟨{
    first_length := intrinsicBoundaryLength N.metric 1 0 rampPeriod
    first_length_eq := rfl
    curvature_loss := m64IntrinsicHighCurvatureLength N (100 * delta / r)
    focusing_loss := C.focusing_loss
    area_loss := m64IntrinsicLongFiberLength N C.S C.height C.radius
    curvature_loss_bound := le_of_lt hcurvature
    focusing_loss_bound := C.focusing_loss_bound
    area_loss_bound := le_of_lt harea_loss
    remaining_length := C.remaining_length
  }⟩

end PoincareMT

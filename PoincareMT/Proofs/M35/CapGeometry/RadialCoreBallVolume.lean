import PoincareMT.Proofs.M35.CapGeometry.RadialCoreCurvatureBalls
import PoincareMT.Proofs.M35.CapGeometry.CoreBallVolume

/-!
# The strict volume clause on the actual radial core

Morgan-Tian Definition 9.72 and Theorem 12.32, pp. 326-327.
The end-orbit radius bounds every exact core curvature radius. Its
explicit time and noncollapse-scale bounds therefore allow the actual
flow certificate to supply the strict frozen reciprocal volume clause.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M35.Uniqueness

/-- Theorem 12.32: the literal radial core has the exact curvature
balls and strict reciprocal volume bound, with the original available
past-time and noncollapse-radius conditions retained explicitly. -/
theorem radial_core_ball_volume
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (NC : StandardFlowNoncollapsingCertificate E.flow) {t a length C : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (ha : 0 < a) (hlength : 0 < length)
    (hC : C⁻¹ < NC.kappa / 8)
    (hfar : 6 * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a < a)
    (hwidth : intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a < 2 * length)
    (hscale : 3 * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a ≤ NC.radius)
    (htime : (3 * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a) ^ 2 ≤ t)
    (y : StandardCapSpace) (hy : radialArclength (E.flow.metric t) ‖y‖ < a - length) :
    ∃ r : ℝ, 0 < r ∧
      scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
        ((E.flow.metric t).ball y r) = r⁻¹ ^ 2 ∧
      closure ((E.flow.metric t).ball y r) ⊆ (E.flow.metric t).ball 0 (a + length) ∧
      IsCompact (closure ((E.flow.metric t).ball y r)) ∧
      ENNReal.ofReal (C⁻¹ * r ^ 3) <
        calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r) := by
  have hR : Continuous (E.flow.connection t).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (E.flow.connection t)).continuous
  obtain ⟨r, hr, hrbound, hrscale, hrinside, hrcompact⟩ := radial_core_curvature_balls
    P (E.flow.metric t) (E.flow.connection t) (E.rotation_invariant t ht)
    (E.complete t ht) (E.nonnegative_sectional t ht) ha hlength hfar hwidth hR y hy
  have hrsq : r ^ 2 ≤ t :=
    (pow_le_pow_left₀ hr.le hrbound 2).trans htime
  have hvolume := E.scalar_curvature_ball_volume_lower P.curvature NC ht hr
    (hrbound.trans hscale) hrsq y hrscale
  refine ⟨r, hr, hrscale, hrinside, hrcompact, ?_⟩
  apply lt_of_lt_of_le _ hvolume
  have hkappa := NC.kappa_pos
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < NC.kappa / 8 * r ^ 3)).mpr
    (mul_lt_mul_of_pos_right hC (pow_pos hr 3))

end PoincareMT.M35.Uniqueness

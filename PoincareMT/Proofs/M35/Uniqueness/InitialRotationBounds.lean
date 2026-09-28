import PoincareMT.Proofs.M35.TerminalBlowup.AngularCollapse
import PoincareMT.Proofs.M35.Uniqueness.CoordinateRotations

/-!
# Bounded actual initial rotation fields

Morgan-Tian, Section 12.5, p. 304: the noncompact vector heat construction
starts with bounded rotational Killing fields. The already proved actual
orbit-radius estimate at time zero bounds every Euclidean skew linear
generator in the initial metric, including the origin where it vanishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

/-- Section 12.5, p. 304: every linear angular generator has globally
bounded initial metric norm. The constant is explicit and the geometric
bound comes from the actual complete rotational solution at time zero. -/
theorem initial_linear_rotation_normSq_le
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hskew : ∀ x, inner ℝ x (B x) = 0) (x : StandardCapSpace) :
    g₀.metric.inner x (B x) (B x) ≤ 4 * ‖B‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero]
    positivity
  have ht : (0 : ℝ) ∈ Ico 0 E.flow.base.lifetime :=
    ⟨le_rfl, E.flow.base.lifetime_pos⟩
  have h := E.angular_tangent_inner_le_remaining_time P ht hx (B x) (hskew x)
  have hinit : E.flow.metric 0 = g₀.metric := E.flow.base.initial_metric
  rw [hinit] at h
  norm_num at h
  have hop := B.le_opNorm x
  have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hratio : ‖B x‖ ^ 2 / ‖x‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    apply (div_le_iff₀ hxnorm).mpr
    have hs := mul_self_le_mul_self (norm_nonneg (B x)) hop
    nlinarith only [hs]
  exact h.trans (mul_le_mul_of_nonneg_left hratio (by norm_num))

/-- The literal coordinate rotation generator is Euclidean angular at
every point, including its fixed axis and the tip. -/
theorem coordinateRotationGenerator_inner_zero (x : StandardCapSpace) :
    inner ℝ x (coordinateRotationGenerator x) = 0 := by
  have he : coordinateRotationGenerator x =
      (-x 1) • EuclideanSpace.single 0 1 + x 0 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;>
      simp [coordinateRotationGenerator, Matrix.toEuclideanLin, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, EuclideanSpace.single]
  rw [he]
  simp only [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right,
    one_mul, starRingEnd_apply, star_trivial]
  ring

/-- Section 12.5, p. 304: the explicit initial coordinate Killing field
has a uniform squared-norm bound for the actual vector heat construction. -/
theorem initial_coordinateRotationGenerator_normSq_le
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (x : StandardCapSpace) :
    g₀.metric.inner x (coordinateRotationGenerator x) (coordinateRotationGenerator x) ≤
      4 * ‖coordinateRotationGenerator‖ ^ 2 :=
  initial_linear_rotation_normSq_le P E coordinateRotationGenerator
    coordinateRotationGenerator_inner_zero x

end PoincareMT.M35.Uniqueness

import PoincareMT.Proofs.M35.Mathlib.SmoothEvenRadial
import PoincareMT.Proofs.M35.RadialGauge.RadialProfileCalculus

/-!
# Actual first and second derivatives of the radial map

Morgan-Tian Section 12.6, pp. 309-314. The harmonic-map computation
uses the actual smooth Euclidean map h(|x|)x. Its first two derivatives
are obtained from the scalar radial derivatives and the product rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35.Uniqueness

/-- The actual Euclidean radial map with scale h; the gauge has h=exp(u). -/
noncomputable def radialScaleMap (h : ℝ → ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  h ‖x‖ • x

theorem radialScaleMap_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (he : Function.Even h) : ContDiff ℝ ∞ (radialScaleMap h) :=
  (SmoothRadial.contDiff_even_norm hh he).smul contDiff_id

private theorem scalar_scale_hessian {S : StandardCapSpace → ℝ}
    (hS : ContDiff ℝ ∞ S) (x u v : StandardCapSpace) :
    fderiv ℝ (fderiv ℝ (fun y => S y • y)) x u v =
      fderiv ℝ S x u • v + fderiv ℝ S x v • u +
        fderiv ℝ (fderiv ℝ S) x u v • x := by
  let F : StandardCapSpace → StandardCapSpace := fun y => S y • y
  have hF : ContDiff ℝ ∞ F := hS.smul contDiff_id
  have hf (y : StandardCapSpace) : fderiv ℝ F y v =
      S y • v + fderiv ℝ S y v • y := by
    have hd := (hS.differentiable (by simp) y).hasFDerivAt.smul (hasFDerivAt_id y)
    change HasFDerivAt F _ y at hd
    rw [hd.fderiv]
    rfl
  have hleft := ((hF.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hright := ((hS.differentiable (by simp) x).hasFDerivAt.smul_const v).add
    ((((hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const v x)).smul (hasFDerivAt_id x))
  have heq : (fun y => fderiv ℝ F y v) =
      fun y => S y • v + fderiv ℝ S y v • y := funext hf
  rw [heq] at hleft
  have h := congrArg (fun L : StandardCapSpace →L[ℝ] StandardCapSpace => L u)
    (hleft.unique hright)
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, id_eq, add_assoc] using h

/-- The genuine radial map differential, away from zero. -/
theorem radialScaleMap_fderiv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {x : StandardCapSpace} (hx : x ≠ 0) (v : StandardCapSpace) :
    fderiv ℝ (radialScaleMap h) x v = h ‖x‖ • v +
      (deriv h ‖x‖ / ‖x‖ * inner ℝ x v) • x := by
  have hd := (RadialGauge.radialProfile_hasFDerivAt
    (hh.differentiable (by simp) ‖x‖) hx).smul (hasFDerivAt_id x)
  change HasFDerivAt (radialScaleMap h) _ x at hd
  rw [hd.fderiv]
  rfl

/-- The actual second differential of the same smooth radial map. -/
theorem radialScaleMap_hessian {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (he : Function.Even h) {x : StandardCapSpace} (hx : x ≠ 0)
    (u v : StandardCapSpace) :
    fderiv ℝ (fderiv ℝ (radialScaleMap h)) x u v =
      (deriv h ‖x‖ / ‖x‖ * inner ℝ x u) • v +
      (deriv h ‖x‖ / ‖x‖ * inner ℝ x v) • u +
      (deriv h ‖x‖ / ‖x‖ * inner ℝ u v +
        (deriv (deriv h) ‖x‖ * ‖x‖ - deriv h ‖x‖) / ‖x‖ ^ 3 *
          inner ℝ x u * inner ℝ x v) • x := by
  have hs : ContDiff ℝ ∞ (fun y : StandardCapSpace => h ‖y‖) :=
    SmoothRadial.contDiff_even_norm hh he
  change fderiv ℝ (fderiv ℝ (fun y : StandardCapSpace => h ‖y‖ • y)) x u v = _
  rw [scalar_scale_hessian hs,
    RadialGauge.radialProfile_hessian_apply hh hx,
    (RadialGauge.radialProfile_hasFDerivAt (hh.differentiable (by simp) ‖x‖) hx).fderiv]
  rfl

end PoincareMT.M35.Uniqueness

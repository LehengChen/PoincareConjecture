import PoincareMT.Proofs.M35.RadialGauge.SmoothGaugeIdentity

/-!
# The actual Euclidean source has the retained exterior formula

Morgan-Tian pp. 313-320, with the corrected single -xi term. The
genuine smooth source agrees with the radial harmonic-gauge equation
at every nonzero Euclidean point. Its exterior decomposition separates
the order-one drift coefficient from the actual restart target.
-/

set_option autoImplicit false

open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem smoothGaugeForcing_eq_norm_radial {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    {x : E} (hx : x ≠ 0) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi x sigma =
      radialGaugeForcing (mapRadius h) f₀ (fun s => s * xi s) sigma ‖x‖ := by
  have heq : smoothGaugeForcing h f₀ xi x sigma =
      smoothGaugeForcing h f₀ xi ‖x‖ sigma := by
    simp only [smoothGaugeForcing, norm_smul, Real.norm_eq_abs, Real.abs_exp,
      abs_norm, smul_eq_mul, abs_mul]
  rw [heq]
  exact smoothGaugeForcing_eq_radial hh he hzero hf hfo hfzero hdfzero
    (norm_pos_iff.mpr hx) sigma

/-- The literal source keeps the actual target coupling and exactly one
copy of the velocity term after passage to Euclidean radius. -/
theorem smoothGaugeForcing_eq_exterior_formula {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    {x : E} (hx : x ≠ 0) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi x sigma =
      radialGaugeDrift (mapRadius h) (fun s => s * xi s) ‖x‖ / ‖x‖ +
        2 / ‖x‖ ^ 2 - 2 * smoothTargetCoupling f₀ ‖Real.exp sigma • x‖ *
          (1 / mapRadius h ‖x‖) ^ 2 := by
  rw [smoothGaugeForcing_eq_norm_radial hh he hzero hf hfo hfzero hdfzero hx sigma]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq : 0 < ‖Real.exp sigma • x‖ := norm_pos_iff.mpr
    (smul_ne_zero (Real.exp_ne_zero _) hx)
  rw [smoothTargetCoupling_eq_exterior hf hfzero hq.ne', norm_smul,
    Real.norm_eq_abs, Real.abs_exp, mul_comm (Real.exp sigma) ‖x‖]
  unfold radialGaugeForcing cylinderTargetForcing radialGaugeDrift
  have hfr : mapRadius h ‖x‖ ≠ 0 := mul_ne_zero hr.ne' (Real.exp_ne_zero _)
  field_simp [hr.ne', hfr]
  ring

end PoincareMT.M35.RadialGauge

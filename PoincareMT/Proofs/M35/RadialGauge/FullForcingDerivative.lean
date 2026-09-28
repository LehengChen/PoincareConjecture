import PoincareMT.Proofs.M35.RadialGauge.ExteriorCoefficients

/-!
# The actual forcing derivative for a general restart target

Morgan-Tian pp. 313-320, with the corrected radial gauge. A restart
target need only have its proved cylindrical end limits. Keeping its
actual coupling f0 f0'/rho isolates the two target terms in the spatial
forcing derivative; the current f'' terms still cancel exactly.
-/

set_option autoImplicit false

open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

/-- The actual angular coupling of the fixed restart target. -/
noncomputable def radialTargetCoupling (f₀ : ℝ → ℝ) (s : ℝ) : ℝ :=
  f₀ s * deriv f₀ s / s

/-- The corrected forcing written without suppressing the target term. -/
noncomputable def radialGaugeForcing (f f₀ velocity : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  cylinderTargetForcing f velocity r -
    2 * radialTargetCoupling f₀ (r * Real.exp sigma) / f r ^ 2

/-- This is exactly the forcing obtained from the logarithmic ansatz. -/
theorem radialGaugeForcing_eq (f f₀ velocity : ℝ → ℝ) (sigma r : ℝ) :
    radialGaugeForcing f f₀ velocity sigma r =
      2 * deriv f r / (r * f r) -
      2 * f₀ (r * Real.exp sigma) * deriv f₀ (r * Real.exp sigma) /
        (r * Real.exp sigma * f r ^ 2) - velocity r / r := by
  unfold radialGaugeForcing cylinderTargetForcing radialTargetCoupling
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual target coupling derivative retains both target jets. -/
theorem radialTargetCoupling_hasDerivAt {f₀ : ℝ → ℝ}
    (hf₀ : ContDiff ℝ ∞ f₀) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (radialTargetCoupling f₀)
      ((deriv f₀ s ^ 2 + f₀ s * deriv (deriv f₀) s) / s -
        f₀ s * deriv f₀ s / s ^ 2) s := by
  have hf := (hf₀.differentiable (by simp) s).hasDerivAt
  have hdf := ((contDiff_infty_iff_deriv.mp hf₀).2.differentiable (by simp) s).hasDerivAt
  have h := (hf.mul hdf).div (hasDerivAt_id s) hs
  change HasDerivAt (radialTargetCoupling f₀) _ s at h
  apply h.congr_deriv
  simp only [id_eq, Pi.mul_apply, mul_one]
  field_simp [hs]

/-- The actual full forcing derivative separates the current-velocity
cancellation from the two target terms needed at a general restart. -/
theorem radialGaugeForcing_hasDerivAt {f f₀ velocity : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf₀ : ContDiff ℝ ∞ f₀) (sigma : ℝ)
    {r : ℝ} (hr : r ≠ 0) (hfr : f r ≠ 0)
    (hv : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    HasDerivAt (radialGaugeForcing f f₀ velocity sigma)
      (-2 * (deriv f r / f r) ^ 2 / r - 2 * (deriv f r / f r) / r ^ 2 +
        velocity r / r ^ 2 -
        2 * deriv (radialTargetCoupling f₀) (r * Real.exp sigma) * Real.exp sigma / f r ^ 2 +
        4 * radialTargetCoupling f₀ (r * Real.exp sigma) * deriv f r / f r ^ 3) r := by
  have hff := (hf.differentiable (by simp) r).hasDerivAt
  have htarget := radialTargetCoupling_hasDerivAt hf₀
    (mul_ne_zero hr (Real.exp_ne_zero sigma))
  have htd : HasDerivAt (radialTargetCoupling f₀)
      (deriv (radialTargetCoupling f₀) (r * Real.exp sigma)) (r * Real.exp sigma) :=
    htarget.differentiableAt.hasDerivAt
  have hcomp := htd.comp r ((hasDerivAt_id r).mul_const (Real.exp sigma))
  have h := (cylinderTargetForcing_hasDerivAt hf hr hfr hv).sub
    ((hcomp.const_mul 2).div (hff.pow 2) (pow_ne_zero 2 hfr))
  change HasDerivAt (radialGaugeForcing f f₀ velocity sigma) _ r at h
  apply h.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, id_eq,
    Function.comp_apply, Pi.pow_apply]
  field_simp [hr, hfr]
  ring

end PoincareMT.M35.RadialGauge

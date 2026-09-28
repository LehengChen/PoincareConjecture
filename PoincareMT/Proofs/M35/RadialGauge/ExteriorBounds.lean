import PoincareMT.Proofs.M35.RadialGauge.ExteriorCoefficients

/-!
# Corrected weighted forcing bounds from radial concavity

Morgan-Tian pp. 311-319, with the radial-gauge correction. The actual
concavity inequality r f' <= f bounds the logarithmic slope by 1/r.
Together with the velocity cancellation and a common velocity bound,
it gives the corrected O(1/r) value and uniform little-o gradient on
an exactly cylindrical target tail. No stronger forcing decay is used.
-/

set_option autoImplicit false

open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

private theorem logarithmicSlope_controls {f : ℝ → ℝ} {r : ℝ}
    (hr : 1 ≤ r) (hf : 0 < f r) (hdf : 0 ≤ deriv f r)
    (hslope : r * deriv f r ≤ f r) :
    0 ≤ deriv f r / f r ∧ deriv f r / f r ≤ 1 ∧ r * (deriv f r / f r) ≤ 1 := by
  have ha := div_nonneg hdf hf.le
  have har : r * (deriv f r / f r) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hf]
    exact hslope
  refine ⟨ha, ?_, har⟩
  nlinarith only [har, mul_nonneg (sub_nonneg.mpr hr) ha]

/-- The actual exterior forcing has the permitted inverse-radius
weight, with a constant determined by the velocity bound alone. -/
theorem cylinderTargetForcing_weighted_bound {f velocity : ℝ → ℝ} {r V : ℝ}
    (hr : 1 ≤ r) (hf : 0 < f r) (hdf : 0 ≤ deriv f r)
    (hslope : r * deriv f r ≤ f r) (hv : |velocity r| ≤ V) :
    (1 + r) * |cylinderTargetForcing f velocity r| ≤ 4 + 2 * V := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨ha, ha1, _⟩ := logarithmicSlope_controls hr hf hdf hslope
  let a := deriv f r / f r
  have heq : r * cylinderTargetForcing f velocity r = 2 * a - velocity r := by
    dsimp [cylinderTargetForcing, a]
    field_simp [hrp.ne', hf.ne']
  have hnum : |2 * a - velocity r| ≤ 2 * a + |velocity r| := by
    have h := abs_add_le (2 * a) (-velocity r)
    have htwo : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha
    simpa only [← sub_eq_add_neg, abs_neg, abs_of_nonneg htwo] using h
  have hb : r * |cylinderTargetForcing f velocity r| ≤ 2 + V := by
    have h := hnum
    rw [← heq, abs_mul, abs_of_pos hrp] at h
    nlinarith only [h, ha1, hv]
  have hweight := mul_le_mul_of_nonneg_right
    (by linarith only [hr] : 1 + r ≤ 2 * r)
    (abs_nonneg (cylinderTargetForcing f velocity r))
  nlinarith only [hb, hweight]

/-- The actual weighted first forcing derivative decays to zero at an
explicit inverse-radius rate, uniformly for a common velocity bound. -/
theorem cylinderTargetForcing_weighted_derivative_bound
    {f velocity : ℝ → ℝ} (hfs : ContDiff ℝ ∞ f) {r V : ℝ}
    (hr : 1 ≤ r) (hf : 0 < f r) (hdf : 0 ≤ deriv f r)
    (hslope : r * deriv f r ≤ f r) (hv : |velocity r| ≤ V)
    (hvd : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    (1 + r) * |deriv (cylinderTargetForcing f velocity) r| ≤ (8 + 2 * V) / r := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨ha, ha1, har⟩ := logarithmicSlope_controls hr hf hdf hslope
  let a := deriv f r / f r
  have heq : r ^ 2 * deriv (cylinderTargetForcing f velocity) r =
      -2 * r * a ^ 2 - 2 * a + velocity r := by
    rw [(cylinderTargetForcing_hasDerivAt hfs hrp.ne' hf.ne' hvd).deriv]
    dsimp only [a]
    field_simp [hrp.ne', hf.ne']
  have ha2 : r * a ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right har ha
    nlinarith only [h, ha1]
  have hneg : |-2 * r * a ^ 2 - 2 * a| = 2 * r * a ^ 2 + 2 * a := by
    rw [show -2 * r * a ^ 2 - 2 * a = -(2 * r * a ^ 2 + 2 * a) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  have hnum := abs_add_le (-2 * r * a ^ 2 - 2 * a) (velocity r)
  rw [hneg, ← heq, abs_mul, abs_of_nonneg (sq_nonneg r)] at hnum
  have hscaled : r ^ 2 * |deriv (cylinderTargetForcing f velocity) r| ≤ 4 + V := by
    nlinarith only [hnum, ha2, ha1, hv]
  have hweight := mul_le_mul_of_nonneg_right
    (show r * (1 + r) ≤ 2 * r ^ 2 by nlinarith only [hr])
    (abs_nonneg (deriv (cylinderTargetForcing f velocity) r))
  rw [le_div_iff₀ hrp]
  nlinarith only [hweight, hscaled]

end PoincareMT.M35.RadialGauge

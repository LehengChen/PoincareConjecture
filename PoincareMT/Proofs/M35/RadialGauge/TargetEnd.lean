import PoincareMT.Proofs.M35.RadialGauge.FullForcingDerivative

/-!
# Actual restart-target end terms in the corrected forcing

Morgan-Tian pp. 313-320. The target angular coupling and its weighted
derivative vanish from the actual first two target-radius end limits.
This is the target contribution at a general restart, where the tail
need not be exactly cylindrical at finite radius.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.RadialGauge

/-- The actual coupling vanishes on an asymptotically cylindrical target. -/
theorem radialTargetCoupling_tendsto_zero {f₀ : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto f₀ atTop (𝓝 L))
    (hdf : Tendsto (deriv f₀) atTop (𝓝 0)) :
    Tendsto (radialTargetCoupling f₀) atTop (𝓝 0) := by
  change Tendsto (fun r => f₀ r * deriv f₀ r / r) atTop (𝓝 0)
  have h := (hf.mul hdf).mul ((tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop).const_div_atTop 1)
  simpa only [one_div, div_eq_mul_inv, mul_zero, id_eq, one_mul] using h

/-- Multiplication by radius leaves exactly the first two actual target
jets and the coupling itself, so the weighted derivative also vanishes. -/
theorem radialTargetCoupling_weighted_derivative_tendsto_zero
    {f₀ : ℝ → ℝ} (hfs : ContDiff ℝ ∞ f₀) {L : ℝ}
    (hf : Tendsto f₀ atTop (𝓝 L))
    (hdf : Tendsto (deriv f₀) atTop (𝓝 0))
    (hddf : Tendsto (deriv (deriv f₀)) atTop (𝓝 0)) :
    Tendsto (fun r => r * deriv (radialTargetCoupling f₀) r) atTop (𝓝 0) := by
  have h := ((hdf.pow 2).add (hf.mul hddf)).sub (radialTargetCoupling_tendsto_zero hf hdf)
  simp only [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [(radialTargetCoupling_hasDerivAt hfs hrp.ne').deriv]
  unfold radialTargetCoupling
  field_simp [hrp.ne']

/-- The two actual target terms are uniformly small past a common
radius, ready for all scalar values in the shrinking gauge strip. -/
theorem radialTargetCoupling_uniform_tail
    {f₀ : ℝ → ℝ} (hfs : ContDiff ℝ ∞ f₀) {L : ℝ}
    (hf : Tendsto f₀ atTop (𝓝 L))
    (hdf : Tendsto (deriv f₀) atTop (𝓝 0))
    (hddf : Tendsto (deriv (deriv f₀)) atTop (𝓝 0)) :
    ∀ epsilon > 0, ∃ R : ℝ, 1 ≤ R ∧ ∀ r, R ≤ r →
      |radialTargetCoupling f₀ r| < epsilon ∧
        |r * deriv (radialTargetCoupling f₀) r| < epsilon := by
  intro epsilon hepsilon
  have h0 := (Metric.tendsto_nhds.1 (radialTargetCoupling_tendsto_zero hf hdf)) epsilon hepsilon
  have h1 := (Metric.tendsto_nhds.1
    (radialTargetCoupling_weighted_derivative_tendsto_zero hfs hf hdf hddf)) epsilon hepsilon
  obtain ⟨R, hR⟩ := eventually_atTop.1 (h0.and h1)
  refine ⟨max 1 R, le_max_left _ _, fun r hr => ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hR r ((le_max_right _ _).trans hr)

end PoincareMT.M35.RadialGauge

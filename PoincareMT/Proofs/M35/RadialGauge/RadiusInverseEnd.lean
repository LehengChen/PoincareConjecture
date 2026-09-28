import PoincareMT.Proofs.M35.RadialGauge.RadiusInverse

/-!
# Bounded radial translation and the actual inverse end

Morgan-Tian pp. 320-322, with the corrected radial end class. The
logarithmic displacement is allowed to be O(1/r). The resulting bounded
translation is retained, and it suffices to send the inverse radius to
infinity uniformly on any parameter family, including a closed time slab.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareMT.M35.RadialGauge

/-- The corrected value weight permits a bounded radial translation. -/
theorem mapRadius_sub_self_bound {u : ℝ → ℝ} {r eta : ℝ}
    (heta : eta ≤ 1) (hu : (1 + |r|) * |u r| ≤ eta) :
    |mapRadius u r - r| ≤ 2 * eta := by
  have hv : |u r| ≤ eta := by
    nlinarith only [hu, mul_nonneg (abs_nonneg r) (abs_nonneg (u r))]
  have he := Real.abs_exp_sub_one_le (hv.trans heta)
  have hweight : |r| * |u r| ≤ eta := by
    nlinarith only [hu, abs_nonneg (u r)]
  calc
    |mapRadius u r - r| = |r| * |Real.exp (u r) - 1| := by
      rw [mapRadius, ← mul_sub_one, abs_mul]
    _ ≤ |r| * (2 * |u r|) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ ≤ 2 * eta := by nlinarith only [hweight]

/-- The genuine inverse has the same bounded translation allowance. -/
theorem inverse_mapRadius_sub_self_bound {u q : ℝ → ℝ} {eta : ℝ}
    (heta : eta ≤ 1) (hu : ∀ r, (1 + |r|) * |u r| ≤ eta)
    (hinv : ∀ z, mapRadius u (q z) = z) (z : ℝ) :
    |q z - z| ≤ 2 * eta := by
  have h := mapRadius_sub_self_bound heta (hu (q z))
  rw [hinv z, abs_sub_comm] at h
  exact h

/-- No vanishing translation is needed to pull end estimates through
the actual inverse radius, uniformly over the filter's parameters. -/
theorem inverse_mapRadius_tendsto_atTop
    {A : Type*} {l : Filter A} {u q : A → ℝ → ℝ} {z : A → ℝ} {eta : ℝ}
    (heta : eta ≤ 1)
    (hu : ∀ a r, (1 + |r|) * |u a r| ≤ eta)
    (hinv : ∀ a r, mapRadius (u a) (q a r) = r)
    (hz : Tendsto z l atTop) :
    Tendsto (fun a => q a (z a)) l atTop := by
  apply tendsto_atTop.2
  intro R
  filter_upwards [(tendsto_atTop.1 hz) (R + 2 * eta)] with a ha
  have hb := inverse_mapRadius_sub_self_bound heta (hu a) (hinv a) (z a)
  linarith only [ha, neg_le_of_abs_le hb]

/-- Positivity of the inverse follows directly from the actual radius
identity and positivity of the exponential factor. -/
theorem inverse_mapRadius_pos {u q : ℝ → ℝ}
    (hinv : ∀ z, mapRadius u (q z) = z) {z : ℝ} (hz : 0 < z) : 0 < q z := by
  have h : 0 < q z * Real.exp (u (q z)) := by
    change 0 < mapRadius u (q z)
    rw [hinv z]
    exact hz
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp h

end PoincareMT.M35.RadialGauge

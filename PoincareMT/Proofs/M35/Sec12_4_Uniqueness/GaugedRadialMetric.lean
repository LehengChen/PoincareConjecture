import PoincareMT.Proofs.M35.RadialGauge.RadiusEnd
import Mathlib.Tactic

/-!
# Actual inverse-radius metric coefficients and their derivatives

Morgan-Tian Proposition 12.26, pp. 320-322, with the 2026-09-17 radial
gauge correction. If q is the inverse of the actual radius map rho,
the pulled-back radial and angular coefficients are q'^2 and (f o q)^2.
These formulas require no vanishing of rho-r at infinity.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.Uniqueness

/-- Differentiating the actual inverse identity gives a nonzero radial
derivative; this does not assume an inverse-derivative formula. -/
theorem radius_deriv_ne_zero_of_right_inverse {ρ q : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (hq : Differentiable ℝ q)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) : deriv ρ (q z) ≠ 0 := by
  have hd := ((hρ (q z)).hasDerivAt.comp z (hq z).hasDerivAt)
  have heq : ρ ∘ q = id := funext hinv
  rw [heq] at hd
  have hp := hd.unique (hasDerivAt_id z)
  intro hz
  rw [hz, zero_mul] at hp
  norm_num at hp

/-- The derivative of the genuine inverse radius is the reciprocal
of the derivative evaluated at its genuine inverse point. -/
theorem inverse_radius_hasDerivAt {ρ q : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (hq : Differentiable ℝ q)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) :
    HasDerivAt q (deriv ρ (q z))⁻¹ z := by
  have hd := ((hρ (q z)).hasDerivAt.comp z (hq z).hasDerivAt)
  have heq : ρ ∘ q = id := funext hinv
  rw [heq] at hd
  have hp := hd.unique (hasDerivAt_id z)
  have hn := radius_deriv_ne_zero_of_right_inverse hρ hq hinv z
  apply (hq z).hasDerivAt.congr_deriv
  apply mul_left_cancel₀ hn
  rw [hp, mul_inv_cancel₀ hn]

/-- The radial coefficient is the actual inverse differential squared. -/
theorem inverse_radial_metric_hasDerivAt {ρ q : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hq : ContDiff ℝ ∞ q)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) :
    HasDerivAt (fun y => deriv q y ^ 2)
      (-2 * deriv (deriv ρ) (q z) / deriv ρ (q z) ^ 4) z := by
  have hρd := hρ.differentiable (by simp)
  have hqd := hq.differentiable (by simp)
  have hq' (y : ℝ) := inverse_radius_hasDerivAt hρd hqd hinv y
  have heq : deriv q = fun y => (deriv ρ (q y))⁻¹ := funext fun y => (hq' y).deriv
  rw [heq]
  have hρ1 := (contDiff_infty_iff_deriv.mp hρ).2
  have ha := ((hρ1.differentiable (by simp) (q z)).hasDerivAt.comp z (hq' z))
  have hn := radius_deriv_ne_zero_of_right_inverse hρd hqd hinv z
  convert! (ha.inv hn).pow 2 using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply, Pi.inv_apply]
  field_simp [hn]

/-- The radial coefficient's second derivative is controlled by the
actual third derivative of rho and a positive lower bound for rho'. -/
theorem inverse_radial_metric_second_hasDerivAt {ρ q : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hq : ContDiff ℝ ∞ q)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) :
    HasDerivAt (deriv (fun y => deriv q y ^ 2))
      (-2 * deriv (deriv (deriv ρ)) (q z) / deriv ρ (q z) ^ 5 +
        8 * deriv (deriv ρ) (q z) ^ 2 / deriv ρ (q z) ^ 6) z := by
  have heq : deriv (fun y => deriv q y ^ 2) = fun y =>
      -2 * deriv (deriv ρ) (q y) / deriv ρ (q y) ^ 4 :=
    funext fun y => (inverse_radial_metric_hasDerivAt hρ hq hinv y).deriv
  rw [heq]
  have hρd := hρ.differentiable (by simp)
  have hqd := hq.differentiable (by simp)
  have hdq := inverse_radius_hasDerivAt hρd hqd hinv z
  have hρ1 := (contDiff_infty_iff_deriv.mp hρ).2
  have hρ2 := (contDiff_infty_iff_deriv.mp hρ1).2
  have ha := (hρ1.differentiable (by simp) (q z)).hasDerivAt.comp z hdq
  have hb := (hρ2.differentiable (by simp) (q z)).hasDerivAt.comp z hdq
  have hn := radius_deriv_ne_zero_of_right_inverse hρd hqd hinv z
  convert! (hb.const_mul (-2)).div (ha.pow 4) (pow_ne_zero 4 hn) using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, Function.comp_apply, Pi.pow_apply]
  field_simp [hn]
  ring

/-- The angular coefficient uses the original warping factor at q. -/
theorem inverse_angular_metric_hasDerivAt {ρ q f : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (hq : Differentiable ℝ q) (hf : Differentiable ℝ f)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) :
    HasDerivAt (fun y => f (q y) ^ 2)
      (2 * f (q z) * deriv f (q z) / deriv ρ (q z)) z := by
  have hdq := inverse_radius_hasDerivAt hρ hq hinv z
  convert! ((hf (q z)).hasDerivAt.comp z hdq).pow 2 using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply]
  ring

/-- The angular C2 bound uses f, f', f'', rho' and rho'' at the
same inverse-radius point, with no stronger displacement estimate. -/
theorem inverse_angular_metric_second_hasDerivAt {ρ q f : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    (hinv : ∀ z, ρ (q z) = z) (z : ℝ) :
    HasDerivAt (deriv (fun y => f (q y) ^ 2))
      (2 * (deriv f (q z) ^ 2 + f (q z) * deriv (deriv f) (q z)) /
          deriv ρ (q z) ^ 2 -
        2 * f (q z) * deriv f (q z) * deriv (deriv ρ) (q z) /
          deriv ρ (q z) ^ 3) z := by
  have hρd := hρ.differentiable (by simp)
  have hqd := hq.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have heq : deriv (fun y => f (q y) ^ 2) = fun y =>
      2 * f (q y) * deriv f (q y) / deriv ρ (q y) :=
    funext fun y => (inverse_angular_metric_hasDerivAt hρd hqd hfd hinv y).deriv
  rw [heq]
  have hdq := inverse_radius_hasDerivAt hρd hqd hinv z
  have hρ1 := (contDiff_infty_iff_deriv.mp hρ).2
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have ha := (hρ1.differentiable (by simp) (q z)).hasDerivAt.comp z hdq
  have hb := (hfd (q z)).hasDerivAt.comp z hdq
  have hc := (hf1.differentiable (by simp) (q z)).hasDerivAt.comp z hdq
  have hn := radius_deriv_ne_zero_of_right_inverse hρd hqd hinv z
  convert! ((hb.const_mul 2).mul hc).div ha hn using 1
  simp only [Function.comp_apply, Pi.mul_apply]
  field_simp [hn]

/-- Uniform rho' -> 1 gives the radial metric's zeroth-order end.
The filter may carry a complete closed time slab. -/
theorem inverse_radial_metric_tendsto {A : Type*} {l : Filter A}
    {ρ q : A → ℝ → ℝ} {z : A → ℝ}
    (hρ : ∀ a, Differentiable ℝ (ρ a)) (hq : ∀ a, Differentiable ℝ (q a))
    (hinv : ∀ a y, ρ a (q a y) = y)
    (hend : Tendsto (fun a => deriv (ρ a) (q a (z a))) l (𝓝 1)) :
    Tendsto (fun a => deriv (q a) (z a) ^ 2) l (𝓝 1) := by
  have heq (a : A) : deriv (q a) (z a) = (deriv (ρ a) (q a (z a)))⁻¹ :=
    (inverse_radius_hasDerivAt (hρ a) (hq a) (hinv a) (z a)).deriv
  simp_rw [heq]
  simpa only [inv_one, one_pow] using (hend.inv₀ one_ne_zero).pow 2

/-- Uniform rho'' -> 0 gives the radial metric's first-order end. -/
theorem inverse_radial_metric_deriv_tendsto {A : Type*} {l : Filter A}
    {ρ q : A → ℝ → ℝ} {z : A → ℝ}
    (hρ : ∀ a, ContDiff ℝ ∞ (ρ a)) (hq : ∀ a, ContDiff ℝ ∞ (q a))
    (hinv : ∀ a y, ρ a (q a y) = y)
    (hend1 : Tendsto (fun a => deriv (ρ a) (q a (z a))) l (𝓝 1))
    (hend2 : Tendsto (fun a => deriv (deriv (ρ a)) (q a (z a))) l (𝓝 0)) :
    Tendsto (fun a => deriv (fun y => deriv (q a) y ^ 2) (z a)) l (𝓝 0) := by
  have heq (a : A) : deriv (fun y => deriv (q a) y ^ 2) (z a) =
      -2 * deriv (deriv (ρ a)) (q a (z a)) / deriv (ρ a) (q a (z a)) ^ 4 :=
    (inverse_radial_metric_hasDerivAt (hρ a) (hq a) (hinv a) (z a)).deriv
  simp_rw [heq]
  have h := ((tendsto_const_nhds (x := (-2 : ℝ))).mul hend2).div
    (hend1.pow 4) (by norm_num)
  convert! h using 1
  norm_num

end PoincareMT.M35.Uniqueness

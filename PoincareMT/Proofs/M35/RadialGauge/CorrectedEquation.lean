import PoincareMT.Proofs.M35.TerminalBlowup.RadialWarping
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The corrected radial harmonic-map equation

Morgan-Tian Equations (12.16)-(12.19), pp. 313-314, with the correction
in reviews/errata/2026-09-17-m35-radial-gauge.md. The time derivative here
holds current radial arclength fixed. Substitution of rho = r exp(u)
gives the zeroth-order velocity term -v/r, hence -xi, exactly once.
The actual spatial and time derivatives are computed before the division.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.RadialGauge

/-- The radial radius in the harmonic-map ansatz, at fixed current arclength. -/
noncomputable def mapRadius (u : ℝ → ℝ) (r : ℝ) : ℝ := r * Real.exp (u r)

/-- The actual radial derivative of the harmonic-map ansatz. -/
theorem mapRadius_hasDerivAt {u : ℝ → ℝ} {r ur : ℝ}
    (hu : HasDerivAt u ur r) :
    HasDerivAt (mapRadius u) (Real.exp (u r) * (1 + r * ur)) r := by
  convert! (hasDerivAt_id r).mul hu.exp using 1
  simp only [id_eq, one_mul]
  ring

/-- The actual second radial derivative of the harmonic-map ansatz. -/
theorem mapRadius_second_deriv {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    deriv (deriv (mapRadius u)) r =
      Real.exp (u r) * (2 * deriv u r +
        r * (deriv u r ^ 2 + deriv (deriv u) r)) := by
  have hd (s : ℝ) := mapRadius_hasDerivAt ((hu.differentiable (by simp) s).hasDerivAt)
  have heq : deriv (mapRadius u) = fun s => Real.exp (u s) * (1 + s * deriv u s) :=
    funext (fun s => (hd s).deriv)
  rw [heq]
  have hdu := (((contDiff_infty_iff_deriv.mp hu).2).differentiable (by simp) r).hasDerivAt
  have h := ((hu.differentiable (by simp) r).hasDerivAt.exp).mul
    (((hasDerivAt_id r).mul hdu).const_add 1)
  convert! h.deriv using 1
  simp only [Pi.mul_apply, id_eq, one_mul]
  ring

/-- The time chain rule holds current r fixed, so it introduces no second
copy of the radial velocity. -/
theorem mapRadius_hasDerivAt_time {u : ℝ → ℝ → ℝ} {t ut : ℝ}
    (r : ℝ) (hu : HasDerivAt (fun s => u s r) ut t) :
    HasDerivAt (fun s => mapRadius (u s) r) (mapRadius (u t) r * ut) t := by
  convert! hu.exp.const_mul r using 1
  simp only [mapRadius]
  ring

/-- The actual one-dimensional radial harmonic tension, with the moving
arclength transport term retained. Here n-1 is the orbit dimension. -/
noncomputable def harmonicRadialOperator
    (n : ℝ) (f f₀ velocity rho : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv rho) r + (n - 1) * (deriv f r / f r) * deriv rho r -
    (n - 1) * f₀ (rho r) * deriv f₀ (rho r) / f r ^ 2 - velocity r * deriv rho r

/-- The corrected operator on logarithmic displacement. The last term
is -xi when xi=v/r; the possible limiting radial translation is retained. -/
noncomputable def logarithmicRadialOperator
    (n : ℝ) (f f₀ velocity u : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv u) r + deriv u r ^ 2 +
    (2 / r + (n - 1) * deriv f r / f r - velocity r) * deriv u r +
    (n - 1) * deriv f r / (r * f r) -
    (n - 1) * f₀ (mapRadius u r) * deriv f₀ (mapRadius u r) /
      (mapRadius u r * f r ^ 2) - velocity r / r

/-- Equations (12.16)-(12.17), corrected: substituting the actual
derivatives of r exp(u) produces precisely the -v/r logarithmic equation. -/
theorem harmonicRadialOperator_mapRadius
    (n : ℝ) (f f₀ velocity : ℝ → ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : 0 < r) (hf : f r ≠ 0) :
    harmonicRadialOperator n f f₀ velocity (mapRadius u) r =
      mapRadius u r * logarithmicRadialOperator n f f₀ velocity u r := by
  unfold harmonicRadialOperator logarithmicRadialOperator
  rw [mapRadius_second_deriv hu,
    (mapRadius_hasDerivAt ((hu.differentiable (by simp) r).hasDerivAt)).deriv]
  unfold mapRadius
  field_simp [hr.ne', hf, Real.exp_ne_zero]
  ring

/-- At a restart slice the source and target coincide and u=0. The
corrected forcing is exactly -v/r, the required identity-tension check. -/
theorem logarithmicRadialOperator_zero (n : ℝ) (f velocity : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) (hf : f r ≠ 0) :
    logarithmicRadialOperator n f f velocity (fun _ => 0) r = -velocity r / r := by
  simp only [logarithmicRadialOperator, deriv_const', mapRadius, Real.exp_zero, mul_one,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add, mul_zero, add_zero]
  field_simp [hr.ne', hf]
  ring

/-- The corrected PDE is equivalent to the actual radial harmonic-map
equation at every positive radius. No equation is asserted at the singular
coordinate r=0; its smooth Euclidean extension is constructed separately. -/
theorem corrected_equation_iff
    (n : ℝ) (f f₀ velocity : ℝ → ℝ) {u : ℝ → ℝ → ℝ}
    {t r : ℝ} (hr : 0 < r) (hf : f r ≠ 0)
    (huspace : ContDiff ℝ ∞ (u t))
    (hutime : DifferentiableAt ℝ (fun s => u s r) t) :
    deriv (fun s => mapRadius (u s) r) t =
        harmonicRadialOperator n f f₀ velocity (mapRadius (u t)) r ↔
      deriv (fun s => u s r) t = logarithmicRadialOperator n f f₀ velocity (u t) r := by
  rw [(mapRadius_hasDerivAt_time r hutime.hasDerivAt).deriv,
    harmonicRadialOperator_mapRadius n f f₀ velocity huspace hr hf]
  constructor
  · exact mul_left_cancel₀ (mul_ne_zero hr.ne' (Real.exp_ne_zero _))
  · intro h
    rw [h]

end PoincareMT.M35.RadialGauge

import PoincareMT.Proofs.M35.RadialGauge.CorrectedEquation
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Removing the radial forcing singularity at the tip

Morgan-Tian Equation (12.18), pp. 313-314, corrected to -xi. The apparent
quotient (1-exp(2wd))/w has a canonical smooth extension at w=0. We
construct it using the actual exponential divided difference, prove its
smoothness, and evaluate its tip value. This is a coefficient construction
for the radial PDE on R5, not an assumed solution to that PDE.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M35.RadialGauge

/-- The smooth exponential divided difference, including its derivative at zero. -/
noncomputable def expSlope (z : ℝ) : ℝ := dslope Real.exp 0 z

/-- The divided difference is smooth through the apparent singularity. -/
theorem expSlope_contDiff : ContDiff ℝ ∞ expSlope := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    obtain ⟨p, hp⟩ := (analyticAt_rexp : AnalyticAt ℝ Real.exp 0)
    exact (show AnalyticAt ℝ expSlope 0 from
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩).contDiffAt
  · have hs : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.exp x - 1) / x) z :=
      (Real.contDiff_exp.contDiffAt.sub contDiffAt_const).div contDiffAt_id hz
    apply hs.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz] with x hx
    simp [expSlope, dslope_of_ne _ hx, slope_def_field, div_eq_mul_inv]

/-- The tip value of the smooth exponential divided difference. -/
theorem expSlope_zero : expSlope 0 = 1 := by
  simp [expSlope, dslope_same, Real.deriv_exp]

/-- Multiplication restores the exact exponential increment, also at zero. -/
theorem mul_expSlope (z : ℝ) : z * expSlope z = Real.exp z - 1 := by
  simpa only [sub_zero, smul_eq_mul, Real.exp_zero, expSlope] using
    sub_smul_dslope Real.exp 0 z

/-- The nonsingular extension of the quotient in Equation (12.18). -/
noncomputable def exponentialForcingQuotient (w d : ℝ) : ℝ :=
  -2 * d * expSlope (2 * w * d)

/-- The constructed extension agrees with the punctured forcing. -/
theorem exponentialForcingQuotient_eq {w : ℝ} (hw : w ≠ 0) (d : ℝ) :
    exponentialForcingQuotient w d = (1 - Real.exp (2 * w * d)) / w := by
  apply (eq_div_iff hw).mpr
  have h := mul_expSlope (2 * w * d)
  unfold exponentialForcingQuotient
  nlinarith only [h]

/-- The tip coefficient is obtained without dividing by the radial coordinate. -/
theorem exponentialForcingQuotient_zero (d : ℝ) :
    exponentialForcingQuotient 0 d = -2 * d := by
  simp [exponentialForcingQuotient, expSlope_zero]

/-- The repaired quotient is jointly smooth in the squared radius and
the coefficient which vanishes to the required order at the tip. -/
theorem exponentialForcingQuotient_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => exponentialForcingQuotient p.1 p.2) := by
  unfold exponentialForcingQuotient
  exact ((contDiff_const.mul contDiff_snd).mul
    (expSlope_contDiff.comp ((contDiff_const.mul contDiff_fst).mul contDiff_snd)))

/-- The corrected zeroth-order forcing, written using smooth coefficient
values. d is the divided radial difference of h0 and h; hW and h0W are
their squared-radius derivatives. There is exactly one -xi term. -/
noncomputable def correctedForcing
    (n sigma w d hW h0W xi : ℝ) : ℝ :=
  (n - 1) * exponentialForcingQuotient w d + 2 * (n - 1) * hW -
    2 * (n - 1) * Real.exp (2 * w * d + 2 * sigma) * h0W - xi

/-- Corrected Equation (12.18) on the punctured radial domain. -/
theorem correctedForcing_eq (n sigma d hW h0W xi : ℝ) {w : ℝ} (hw : w ≠ 0) :
    correctedForcing n sigma w d hW h0W xi =
      (n - 1) / w * (1 - Real.exp (2 * w * d)) + 2 * (n - 1) * hW -
        2 * (n - 1) * Real.exp (2 * w * d + 2 * sigma) * h0W - xi := by
  rw [correctedForcing, exponentialForcingQuotient_eq hw]
  ring

/-- At a restart, h0=h and sigma=0. The smooth tip value therefore also
has the corrected velocity coefficient -xi. -/
theorem correctedForcing_restart (n w hW xi : ℝ) :
    correctedForcing n 0 w 0 hW hW xi = -xi := by
  simp [correctedForcing, exponentialForcingQuotient]

/-- Smooth coefficient fields produce a smooth forcing on Euclidean space,
including at radial squared radius zero. -/
theorem correctedForcing_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℝ) {sigma w d hW h0W xi : E → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) (hw : ContDiff ℝ ∞ w)
    (hd : ContDiff ℝ ∞ d) (hhW : ContDiff ℝ ∞ hW)
    (hh0W : ContDiff ℝ ∞ h0W) (hxi : ContDiff ℝ ∞ xi) :
    ContDiff ℝ ∞ (fun x => correctedForcing n (sigma x) (w x) (d x)
      (hW x) (h0W x) (xi x)) := by
  unfold correctedForcing
  have hquot : ContDiff ℝ ∞ (fun x => exponentialForcingQuotient (w x) (d x)) :=
    exponentialForcingQuotient_contDiff.comp (hw.prodMk hd)
  have hexp : ContDiff ℝ ∞ (fun x => Real.exp (2 * w x * d x + 2 * sigma x)) :=
    (((contDiff_const.mul hw).mul hd).add (contDiff_const.mul hsigma)).exp
  exact (((contDiff_const.mul hquot).add (contDiff_const.mul hhW)).sub
    ((contDiff_const.mul hexp).mul hh0W)).sub hxi

end PoincareMT.M35.RadialGauge

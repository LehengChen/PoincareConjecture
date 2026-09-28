import PoincareMT.Proofs.M25.Topology3D.Space3.CirclePeriodCoordinates
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Smooth immersed circles from nonstationary real lifts

The rotated logarithm supplies local time on the prescribed circle.
Factoring a curve through that local time proves smoothness; the
right-inverse identity and nonzero real velocity prove injectivity
of its manifold derivative. This is the analytic part of the reviewed
period-circle-planar adapter derivation of 2026-09-22, for Hatcher,
Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-2.
-/

set_option autoImplicit false

open Function
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth real lift of a map from the prescribed circle makes the
map smooth in the existing sphere manifold structure. -/
theorem contMDiff_of_smooth_period_lift (T : ℝ) (hT : T ≠ 0)
    (c : UnitCircle → E) (hc : ContDiff ℝ ∞ (c ∘ periodCircleParam T)) :
    ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ c := by
  intro q
  obtain ⟨s, hs, hsection⟩ := exists_periodCircle_local_time T hT q
  have heq : (c ∘ periodCircleParam T) ∘ s = c := by
    rw [comp_assoc, hsection, comp_id]
  have h := hc.comp_contMDiffAt hs
  rwa [heq] at h

/-- Nonzero velocity of the actual smooth real lift makes the circle's
manifold derivative injective. Periodicity alone is not used to infer
global injectivity of the circle map. -/
theorem mfderiv_injective_of_nonzero_period_lift (T : ℝ) (hT : T ≠ 0)
    (c : UnitCircle → E) (hc : ContDiff ℝ ∞ (c ∘ periodCircleParam T))
    (hv : ∀ s, deriv (c ∘ periodCircleParam T) s ≠ 0) (q : UnitCircle) :
    Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) c q) := by
  obtain ⟨s, hs, hsection⟩ := exists_periodCircle_local_time T hT q
  have ha := (periodCircleParam_contMDiff T).mdifferentiable (by simp) (s q)
  have hsd := hs.mdifferentiableAt (by simp)
  have hid := (ha.hasMFDerivAt.comp q hsd.hasMFDerivAt).mfderiv
  rw [hsection, mfderiv_id] at hid
  have hsi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) s q) := by
    have hcomp : Injective ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (periodCircleParam T) (s q)).comp
        (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) s q)) := by
      rw [← hid]
      exact injective_id
    intro a b hab
    apply hcomp
    exact congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (periodCircleParam T) (s q)) hab
  have hγi : Injective (fderiv ℝ (c ∘ periodCircleParam T) (s q)) := by
    intro a b hab
    simp only [fderiv_eq_smul_deriv] at hab
    exact smul_left_injective ℝ (hv (s q)) hab
  have heq : (c ∘ periodCircleParam T) ∘ s = c := by
    rw [comp_assoc, hsection, comp_id]
  have hd := ((hc.differentiable (by simp) (s q)).hasFDerivAt.hasMFDerivAt.comp q
    hsd.hasMFDerivAt).mfderiv
  rw [heq] at hd
  rw [hd]
  exact hγi.comp hsi

end PoincareMT.M25.Topology3D

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Radial contraction in smooth chart coordinates

Pushing the linear field x |-> -x through a smooth chart gives the
velocity of its exponentially shrinking radial tracks. These are the
local formulas for Hatcher's shrinking move, Notes on Basic 3-Manifold
Topology, Lemma 1.3, p. 3. See the ball-shrinking derivation in the task
records; the relative attaching-cap condition is a separate obligation.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The radial contraction field in the target of a smooth chart.
Only values on the chart target have geometric meaning. -/
noncomputable def chartRadialField (e : OpenPartialHomeomorph E F) (y : F) : F :=
  -((fderiv ℝ e (e.symm y)) (e.symm y))

/-- Smoothness of the forward chart and its inverse makes the pushed
radial field smooth on the chart target. -/
theorem chartRadialField_contDiffOn (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (chartRadialField e) e.target := by
  exact (((he.fderiv_of_isOpen e.open_source (by simp)).comp hi
    (fun _ hy => e.map_target hy)).clm_apply hi).neg

/-- Exponential scaling in source coordinates solves the pushed
radial field wherever the scaled coordinate stays in the source. -/
theorem chartRadialField_track_hasDerivAt (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (x : E) (t : ℝ)
    (hx : Real.exp (-t) • x ∈ e.source) :
    HasDerivAt (fun s : ℝ => e (Real.exp (-s) • x))
      (chartRadialField e (e (Real.exp (-t) • x))) t := by
  have hs : HasDerivAt (fun s : ℝ => Real.exp (-s) • x)
      (-(Real.exp (-t) • x)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg_one, neg_smul] using
      ((hasDerivAt_id t).neg.exp).smul_const x
  have hd := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hs
  simpa only [Function.comp_def, chartRadialField, e.left_inv hx, map_neg] using hd

end PoincareMT.M25.Topology3D

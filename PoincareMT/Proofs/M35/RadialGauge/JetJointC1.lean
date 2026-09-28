import PoincareMT.Proofs.M35.RadialGauge.JointC1
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint C1 regularity of the actual spatial jets

Morgan-Tian Proposition 12.26, pp. 320-322; task derivation 10.
The proved time equations and closed-slab jet continuity identify the
joint differential of each spatial jet. In particular the first jet has
the genuine joint C1 regularity needed for inverse-differential calculus.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareMT.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual spatial jets are jointly C1 when their already identified
time equations have jointly continuous right-hand-side jets. -/
theorem spatial_jets_joint_c1_of_time_equation
    {u H : ℝ → E → F} {a b : ℝ}
    (hs : ∀ t ∈ Icc a b, ContDiff ℝ ∞ (u t))
    (huj : ∀ j : ℕ, Continuous
      (fun p : Icc a b × E => iteratedFDeriv ℝ j (u p.1.1) p.2))
    (hHj : ∀ j : ℕ, Continuous
      (fun p : Icc a b × E => iteratedFDeriv ℝ j (H p.1.1) p.2))
    (htime : ∀ j t, t ∈ Ioo a b → ∀ x,
      HasDerivAt (fun s => iteratedFDeriv ℝ j (u s) x)
        (iteratedFDeriv ℝ j (H t) x) t) (j : ℕ) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => iteratedFDeriv ℝ j (u p.1) p.2)
      (Ioo a b ×ˢ univ) := by
  have hspace (t : ℝ) (ht : t ∈ Icc a b) :
      Differentiable ℝ (iteratedFDeriv ℝ j (u t)) := by
    intro x
    exact (hs t ht).contDiffAt.differentiableAt_iteratedFDeriv
      (show (j : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
  have hdc : Continuous
      (fun p : Icc a b × E => fderiv ℝ (iteratedFDeriv ℝ j (u p.1.1)) p.2) := by
    have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).continuous.comp
      (huj (j + 1))
    simpa only [fderiv_iteratedFDeriv, Function.comp_def] using h
  exact joint_contDiffOn_one_of_slab_partials hspace (htime j) (hHj j) hdc

end PoincareMT.M35.RadialGauge

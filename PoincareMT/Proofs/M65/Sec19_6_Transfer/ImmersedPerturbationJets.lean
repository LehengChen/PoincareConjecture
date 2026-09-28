import PoincareMT.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationVelocity
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual joint angular-time jets

Holding the genuine perturbation parameter fixed produces ordinary
angular-time derivatives whose dependence on every variable remains
smooth. These are the literal derivatives used by the C2 approximation.
MT Lemma 19.4, pp. 439-441; M65 derivation 49, section 12.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareMT.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- All actual angular-time slice jets of a smooth perturbation chart
map depend smoothly on the perturbation parameter. In particular this
supplies orders zero, one, and two without a jet premise.
MT Lemma 19.4, pp. 439-441; derivation 49, section 12. -/
theorem slice_jet_contDiffOn (f : P × (ℝ × ℝ) → LoopAmbient)
    (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun z => iteratedFDeriv ℝ j (fun w => f (z.1, w)) z.2) U := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) LoopAmbient).symm.contDiff.comp_contDiffOn hf
  | succ j hj =>
    intro z hz
    have hunc : ContDiffAt ℝ ∞
        (fun w : (P × (ℝ × ℝ)) × (ℝ × ℝ) =>
          iteratedFDeriv ℝ j (fun x => f (w.1.1, x)) w.2) (z, z.2) :=
      (hj.contDiffAt (hU.mem_nhds hz)).comp (z, z.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun w : P × (ℝ × ℝ) =>
        fderiv ℝ (fun x : ℝ × ℝ => iteratedFDeriv ℝ j (fun y => f (w.1, y)) x) w.2) z :=
      ContDiffAt.fderiv
        (f := fun w : P × (ℝ × ℝ) => fun x : ℝ × ℝ =>
          iteratedFDeriv ℝ j (fun y => f (w.1, y)) x)
        (g := fun w : P × (ℝ × ℝ) => w.2) hunc contDiffAt_snd (by simp)
    have h := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) => ℝ × ℝ) LoopAmbient).symm.contDiff.contDiffAt.comp z hd
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using h.contDiffWithinAt

end PoincareMT.M65Perturbation
